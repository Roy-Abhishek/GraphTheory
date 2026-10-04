/* Simulated annealing for level labelings of a box grid (3-d, 6-neighbour).
 *
 * Finds t: cells -> {0..H} such that
 *   (1) adjacent cells have different labels, and
 *   (2) every cell has exactly 0 or K = 3 neighbours with a smaller label.
 * Ordering the edges by label gives an acyclic orientation with every in-degree 0 or 3, so the
 * cells with in-degree 0 form a minimum-size percolating set whose percolation time is the
 * longest directed path, at most H (see minperc.py). Energy = sum over cells of the distance of
 * the in-degree to {0, K} + number of adjacent equal-label pairs; E = 0 is a solution.
 *
 * usage: anneal NX NY NZ H0 SEED BUDGET TEMP INIT PIN [ORBITS [CORNER]]   (CORNER = the word "corner": see HI below)
 *   H0      largest label to start with (random start: uniform in 0..H0; seeded start: clipped to H0)
 *   BUDGET  moves allowed per height level before giving up
 *   TEMP    Metropolis temperature (energy is an integer count of violations; ~0.3 works)
 *   INIT    file of NX*NY*NZ labels (cell index (x*NY + y)*NZ + z), or "-" for a random start
 *   PIN     file of cell indices forced to be sources (label 0, never moved), or "-"
 *   ORBITS  optional file restricting the search to labelings constant on orbits of a symmetry group:
 *           first the number of orbits, then per orbit its size and cell indices. A move relabels a whole
 *           orbit. Omitted or "-": every cell is its own orbit. INIT must already be constant on orbits.
 * After each solution the labels are replaced by the true levels (longest path from a source),
 * the target height drops to (that height - 1), and the search continues from there. Output:
 *   SOLVED <target H> <T> <moves>   then one line of labels (the levels)
 *   STUCK <target H> <best energy> <moves>     when the budget runs out; the program then exits
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define K 3
static int nx, ny, nz, N, H;
static int *nb;
static int8_t *deg;
static int16_t *lab;
static int8_t *in;
static uint8_t *pinned;
static int *movable, nmovable;           /* indices of the orbits that may be moved */
static int *dmin, maxdmin, use_corner;   /* Manhattan distance of each cell to its nearest corner */
/* Every directed path ends at a corner (the only possible sinks), so a cell's label is at most
 * H - dmin(cell). With CORNER on, labels are confined to 0..H - dmin: a sound restriction. */
#define HI(cell) (use_corner ? H - dmin[cell] : H)
static int norbits, *orbit_start, *orbit_cells;   /* orbits in compressed form: cells orbit_cells[orbit_start[o] .. orbit_start[o+1]) */
static long E;
static uint64_t rs;

static inline uint64_t rng(void) {
    rs ^= rs >> 12; rs ^= rs << 25; rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}
static inline int dev(int i) { int a = i, b = i > K ? i - K : K - i; return a < b ? a : b; }

static void build_grid(void) {
    N = nx * ny * nz;
    nb = malloc(sizeof(int) * N * 6);
    deg = malloc(N);
    for (int x = 0; x < nx; x++) for (int y = 0; y < ny; y++) for (int z = 0; z < nz; z++) {
        int v = (x * ny + y) * nz + z, c = 0;
        if (x > 0) nb[v * 6 + c++] = ((x - 1) * ny + y) * nz + z;
        if (x < nx - 1) nb[v * 6 + c++] = ((x + 1) * ny + y) * nz + z;
        if (y > 0) nb[v * 6 + c++] = (x * ny + y - 1) * nz + z;
        if (y < ny - 1) nb[v * 6 + c++] = (x * ny + y + 1) * nz + z;
        if (z > 0) nb[v * 6 + c++] = (x * ny + y) * nz + z - 1;
        if (z < nz - 1) nb[v * 6 + c++] = (x * ny + y) * nz + z + 1;
        deg[v] = c;
    }
}

static void full_energy(void) {
    E = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int i = 0; i < deg[v]; i++) if (lab[nb[v * 6 + i]] < lab[v]) c++;
        in[v] = c;
        E += dev(c);
        for (int i = 0; i < deg[v]; i++) { int w = nb[v * 6 + i]; if (w > v && lab[w] == lab[v]) E++; }
    }
}

static inline int try_delta(int u, int b, int *new_in_u, int *dn) {
    int a = lab[u], less = 0, eq_new = 0, eq_old = 0, d = 0;
    for (int i = 0; i < deg[u]; i++) {
        int lw = lab[nb[u * 6 + i]];
        less += lw < b; eq_new += lw == b; eq_old += lw == a;
        int delta = (b < lw) - (a < lw);
        dn[i] = delta;
        if (delta) { int w = nb[u * 6 + i]; d += dev(in[w] + delta) - dev(in[w]); }
    }
    *new_in_u = less;
    return d + dev(less) - dev(in[u]) + (eq_new - eq_old);
}

/* relabel one cell, updating in-degrees and the energy; returns the energy change */
static int apply_cell(int u, int b) {
    int dn[6], new_in, d = try_delta(u, b, &new_in, dn);
    lab[u] = b; in[u] = new_in;
    for (int i = 0; i < deg[u]; i++) in[nb[u * 6 + i]] += dn[i];
    E += d;
    return d;
}

/* run until E == 0 or `budget` moves; returns moves used, -1 if the budget ran out */
static long anneal(long budget, double temp, long *best_E) {
    double accept[64];
    for (int k = 0; k < 64; k++) accept[k] = exp(-k / temp);
    *best_E = E;
    for (long m = 0; m < budget; m++) {
        if (E == 0) return m;
        int o = movable[rng() % nmovable], first = orbit_cells[orbit_start[o]], size = orbit_start[o + 1] - orbit_start[o];
        int a = lab[first], b, hu = HI(first);
        uint64_t r = rng();
        if (hu <= 0) continue;                           /* forced to be a source */
        if (r & 1) b = (int)((r >> 8) % (hu + 1));
        else { b = a + ((r & 2) ? 1 : -1) * (1 + (int)((r >> 2) & 1)); if (b < 0 || b > hu) continue; }
        if (b == a) continue;
        int d = 0;
        for (int j = 0; j < size; j++) d += apply_cell(orbit_cells[orbit_start[o] + j], b);
        if (d > 0 && (d >= 64 || (rng() >> 11) * (1.0 / 9007199254740992.0) >= accept[d]))
            for (int j = size - 1; j >= 0; j--) apply_cell(orbit_cells[orbit_start[o] + j], a);   /* undo */
        else if (E < *best_E) *best_E = E;
    }
    return E == 0 ? budget : -1;
}

/* replace labels by true levels: 0 for sources, else 1 + max level of the smaller-labelled neighbours */
static int compress(void) {
    int maxl = 0;
    int16_t *lvl = calloc(N, sizeof(int16_t));
    for (int l = 0; l <= H; l++)                  /* labels are a topological order: increasing label */
        for (int v = 0; v < N; v++) if (lab[v] == l) {
            int best = -1;
            if (in[v] > 0) for (int i = 0; i < deg[v]; i++) { int w = nb[v * 6 + i]; if (lab[w] < l && lvl[w] > best) best = lvl[w]; }
            lvl[v] = in[v] > 0 ? best + 1 : 0;
            if (lvl[v] > maxl) maxl = lvl[v];
        }
    memcpy(lab, lvl, sizeof(int16_t) * N);
    free(lvl);
    return maxl;
}

int main(int argc, char **argv) {
    if (argc < 10) { fprintf(stderr, "usage: anneal NX NY NZ H0 SEED BUDGET TEMP INIT PIN [ORBITS]\n"); return 2; }
    nx = atoi(argv[1]); ny = atoi(argv[2]); nz = atoi(argv[3]); H = atoi(argv[4]);
    rs = (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL + 88172645463325252ULL;
    long budget = atol(argv[6]); double temp = atof(argv[7]);
    build_grid();
    use_corner = argc > 11 && strcmp(argv[11], "corner") == 0;
    dmin = malloc(sizeof(int) * N);
    for (int x = 0; x < nx; x++) for (int y = 0; y < ny; y++) for (int z = 0; z < nz; z++) {
        int a = x < nx - 1 - x ? x : nx - 1 - x, b = y < ny - 1 - y ? y : ny - 1 - y, c = z < nz - 1 - z ? z : nz - 1 - z;
        dmin[(x * ny + y) * nz + z] = a + b + c;
        if (a + b + c > maxdmin) maxdmin = a + b + c;
    }
    if (use_corner && H < maxdmin) { printf("STUCK %d 0 0\n", H); return 0; }   /* the center alone needs T >= maxdmin */
    lab = calloc(N, sizeof(int16_t)); in = calloc(N, 1); pinned = calloc(N, 1); movable = malloc(sizeof(int) * N);
    if (strcmp(argv[8], "-") == 0) { for (int v = 0; v < N; v++) lab[v] = rng() % (HI(v) + 1); }
    else {
        FILE *f = fopen(argv[8], "r");
        if (!f) { perror("init"); return 2; }
        for (int v = 0; v < N; v++) { int x; if (fscanf(f, "%d", &x) != 1) return 2; lab[v] = x > HI(v) ? HI(v) : x; }
        fclose(f);
    }
    if (strcmp(argv[9], "-") != 0) {
        FILE *f = fopen(argv[9], "r"); int v;
        if (!f) { perror("pin"); return 2; }
        while (fscanf(f, "%d", &v) == 1) { pinned[v] = 1; lab[v] = 0; }
        fclose(f);
    }
    if (argc > 10 && strcmp(argv[10], "-") != 0) {
        FILE *f = fopen(argv[10], "r");
        if (!f || fscanf(f, "%d", &norbits) != 1) { perror("orbits"); return 2; }
        orbit_start = malloc(sizeof(int) * (norbits + 1)); orbit_cells = malloc(sizeof(int) * N);
        int pos = 0;
        for (int o = 0; o < norbits; o++) {
            int k; if (fscanf(f, "%d", &k) != 1) return 2;
            orbit_start[o] = pos;
            for (int j = 0; j < k; j++) { if (fscanf(f, "%d", &orbit_cells[pos++]) != 1) return 2; }
        }
        orbit_start[norbits] = pos;
        fclose(f);
        if (pos != N) { fprintf(stderr, "orbits must partition the %d cells (got %d)\n", N, pos); return 2; }
    } else {
        norbits = N; orbit_start = malloc(sizeof(int) * (N + 1)); orbit_cells = malloc(sizeof(int) * N);
        for (int v = 0; v < N; v++) { orbit_start[v] = v; orbit_cells[v] = v; }
        orbit_start[N] = N;
    }
    for (int o = 0; o < norbits; o++) {            /* labels constant on orbits; a pinned cell pins its orbit */
        int first = orbit_cells[orbit_start[o]], any_pinned = 0;
        for (int j = orbit_start[o]; j < orbit_start[o + 1]; j++) {
            if (lab[orbit_cells[j]] != lab[first] && strcmp(argv[8], "-") != 0) { fprintf(stderr, "INIT is not constant on orbit %d\n", o); return 2; }
            any_pinned |= pinned[orbit_cells[j]];
        }
        for (int j = orbit_start[o]; j < orbit_start[o + 1]; j++) lab[orbit_cells[j]] = any_pinned ? 0 : lab[first];
        if (any_pinned) for (int j = orbit_start[o]; j < orbit_start[o + 1]; j++) pinned[orbit_cells[j]] = 1;
    }
    nmovable = 0;
    for (int o = 0; o < norbits; o++) if (!pinned[orbit_cells[orbit_start[o]]]) movable[nmovable++] = o;
    full_energy();
    long total = 0, best_E;
    for (;;) {
        long used = anneal(budget, temp, &best_E);
        total += used < 0 ? budget : used;
        if (used < 0) { printf("STUCK %d %ld %ld\n", H, best_E, total); return 0; }
        long check = E; full_energy();
        if (E != 0 || check != 0) { fprintf(stderr, "energy bookkeeping error: %ld vs %ld\n", check, E); return 3; }
        int target = H, T = compress();
        printf("SOLVED %d %d %ld\n", target, T, total);
        for (int v = 0; v < N; v++) printf("%d%c", lab[v], v + 1 < N ? ' ' : '\n');
        fflush(stdout);
        H = T - 1;
        if (H < 1 || (use_corner && H < maxdmin)) return 0;
        for (int v = 0; v < N; v++) if (lab[v] > HI(v)) lab[v] = HI(v);
        full_energy();
    }
}
