/* Exact search (domain propagation + depth-first branching) for minimum percolating sets of a box.
 *
 * Unknowns: a level label t(v) in {0..H} for every cell (or for every orbit of a symmetry group).
 * Constraints (see minperc.py for why these characterise the minimum percolating sets):
 *   - adjacent cells have different labels;
 *   - t(v) = 0 iff v is a source (then all its neighbours are later), and a cell with t(v) >= 1 has
 *     EXACTLY 3 neighbours with a smaller label, at least one of them with label t(v) - 1
 *     ("tight": t is the longest-path level, so each percolating set has exactly one labeling).
 * A labeling with maximum label <= H exists iff some minimum percolating set has T <= H.
 *
 * usage: exact NX NY NZ H MAXSOL NODE_LIMIT PIN ORBITS [SEED [RESTART_BASE [FORBID]]]
 *   FORBID      file of cell indices that may NOT be sources (a restriction of the search space, so UNSAT
 *               under it only means "no solution with sources inside the allowed cells")
 *   MAXSOL      stop after this many solutions (0 = count them all, -1 = print the root-propagated domains)
 *   NODE_LIMIT  give up after this many search nodes (0 = unlimited)
 *   SEED        nonzero: restart mode for finding ONE solution (MAXSOL = 1): random tie-breaking and value
 *               order, node limit RESTART_BASE (default 2000) growing 1.5x per restart. Still complete:
 *               a restart that finishes without hitting its limit proves UNSAT.
 *   PIN         file of cell indices forced to be sources, or "-"
 *   ORBITS      file in the format of anneal.c (labels constant on orbits), or "-"
 * Output: "SOLUTION" lines each followed by one line of cell labels (cell index (x*NY + y)*NZ + z), then
 *   "SAT <count>"   (count = solutions found; = all of them if the search finished)
 *   "UNSAT"         no labeling exists (exhaustive)
 *   "LIMIT <count>" node limit hit
 * and always "NODES <n>" first. H <= 62.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef uint64_t dom_t;
static int nx, ny, nz, N, H, M;
static int *orb, *orbit_start, *orbit_cells;
static int nn[16384], nj[16384][6], nm[16384][6];   /* per orbit: distinct neighbour orbits and multiplicities */
static long nodes, node_limit, found, maxsol;
static int print_solutions = 1;
static int limit_hit;                    /* set only if the node limit actually cut the search short */
static int key[16384];                    /* per orbit: twice the Manhattan distance of its first cell from the center */
static uint64_t rs;                      /* xorshift state, used only in restart mode */
static int randomize;                    /* restart mode: random tie-breaking and value order */
static long restart_nodes, restart_limit;
static inline uint64_t rng(void) { rs ^= rs >> 12; rs ^= rs << 25; rs ^= rs >> 27; return rs * 2685821657736338717ULL; }

static int cell_nbrs(int v, int *out) {
    int x = v / (ny * nz), y = (v / nz) % ny, z = v % nz, c = 0;
    if (x > 0) out[c++] = v - ny * nz;
    if (x < nx - 1) out[c++] = v + ny * nz;
    if (y > 0) out[c++] = v - nz;
    if (y < ny - 1) out[c++] = v + nz;
    if (z > 0) out[c++] = v - 1;
    if (z < nz - 1) out[c++] = v + 1;
    return c;
}

/* can value t of orbit o be completed given the other domains? */
static int supported(int o, int t, const dom_t *dom) {
    int k = nn[o];
    if (t == 0) {
        for (int j = 0; j < k; j++) if ((dom[nj[o][j]] & ~1ULL) == 0) return 0;     /* all neighbours must be > 0 */
        return 1;
    }
    int forced = 0, forced_t1 = 0, free_idx[6], free_m[6], free_t1[6], nfree = 0;
    for (int j = 0; j < k; j++) {
        dom_t avail = dom[nj[o][j]] & ~(1ULL << t);
        if (!avail) return 0;
        dom_t less = avail & ((1ULL << t) - 1), greater = avail >> (t + 1);
        int has_t1 = (avail >> (t - 1)) & 1;
        if (less && !greater) { forced += nm[o][j]; forced_t1 |= has_t1; }
        else if (greater && !less) { /* contributes nothing */ }
        else { free_idx[nfree] = j; free_m[nfree] = nm[o][j]; free_t1[nfree] = has_t1; nfree++; }
    }
    for (int mask = 0; mask < (1 << nfree); mask++) {
        int total = forced, t1 = forced_t1;
        for (int i = 0; i < nfree; i++) if (mask >> i & 1) { total += free_m[i]; t1 |= free_t1[i]; }
        if (total == 3 && t1) return 1;
    }
    return 0;
}

static int propagate(dom_t *dom) {
    int changed = 1;
    while (changed) {
        changed = 0;
        for (int o = 0; o < M; o++) {
            dom_t d = dom[o], nd = 0;
            for (int t = 0; t <= H; t++) if ((d >> t & 1) && supported(o, t, dom)) nd |= 1ULL << t;
            if (nd != d) { dom[o] = nd; changed = 1; if (!nd) return 0; }
        }
    }
    return 1;
}

static void report(const dom_t *dom) {
    found++;
    if (!print_solutions) return;
    printf("SOLUTION\n");
    for (int v = 0; v < N; v++) {
        int t = __builtin_ctzll(dom[orb[v]]);
        printf("%d%c", t, v + 1 < N ? ' ' : '\n');
    }
}

static int dfs(const dom_t *parent) {
    if ((node_limit && nodes >= node_limit) || (restart_limit && restart_nodes >= restart_limit)) { limit_hit = 1; return 1; }
    nodes++; restart_nodes++;
    dom_t *dom = malloc(sizeof(dom_t) * M);
    memcpy(dom, parent, sizeof(dom_t) * M);
    if (!propagate(dom)) { free(dom); return 0; }
    int best = -1, best_size = 99, ties = 0;
    for (int o = 0; o < M; o++) {                       /* smallest domain first; ties: closest to the center */
        int s = __builtin_popcountll(dom[o]);
        if (s <= 1) continue;
        if (best < 0 || s < best_size || (s == best_size && key[o] < key[best])) { best = o; best_size = s; ties = 1; }
        else if (randomize && s == best_size && key[o] == key[best] && rng() % ++ties == 0) best = o;
    }
    if (best < 0) { report(dom); free(dom); return maxsol && found >= maxsol; }
    int vals[64], nv = 0, stop = 0;
    for (int t = 0; t <= H; t++) if (dom[best] >> t & 1) vals[nv++] = t;
    if (randomize) for (int i = nv - 1; i > 0; i--) { int j = rng() % (i + 1), tmp = vals[i]; vals[i] = vals[j]; vals[j] = tmp; }
    for (int i = 0; i < nv && !stop; i++) {
        dom_t *child = malloc(sizeof(dom_t) * M);
        memcpy(child, dom, sizeof(dom_t) * M);
        child[best] = 1ULL << vals[i];
        stop = dfs(child);
        free(child);
    }
    free(dom);
    return stop;
}

int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: exact NX NY NZ H MAXSOL NODE_LIMIT PIN ORBITS\n"); return 2; }
    nx = atoi(argv[1]); ny = atoi(argv[2]); nz = atoi(argv[3]); H = atoi(argv[4]);
    maxsol = atol(argv[5]); node_limit = atol(argv[6]);
    print_solutions = maxsol != 0;                      /* MAXSOL = 0 only counts */
    N = nx * ny * nz;
    orb = malloc(sizeof(int) * N); orbit_start = malloc(sizeof(int) * (N + 1)); orbit_cells = malloc(sizeof(int) * N);
    if (strcmp(argv[8], "-") != 0) {
        FILE *f = fopen(argv[8], "r");
        if (!f || fscanf(f, "%d", &M) != 1) { perror("orbits"); return 2; }
        int pos = 0;
        for (int o = 0; o < M; o++) {
            int k; if (fscanf(f, "%d", &k) != 1) return 2;
            orbit_start[o] = pos;
            for (int j = 0; j < k; j++) { if (fscanf(f, "%d", &orbit_cells[pos]) != 1) return 2; orb[orbit_cells[pos]] = o; pos++; }
        }
        orbit_start[M] = pos; fclose(f);
        if (pos != N || M > 16384) { fprintf(stderr, "bad orbit file\n"); return 2; }
    } else {
        M = N;
        for (int v = 0; v < N; v++) { orb[v] = v; orbit_start[v] = v; orbit_cells[v] = v; }
        orbit_start[N] = N;
        if (M > 16384) { fprintf(stderr, "too many cells\n"); return 2; }
    }
    for (int o = 0; o < M; o++) {                       /* neighbour orbits of the representative cell */
        int nbrs[6], c = cell_nbrs(orbit_cells[orbit_start[o]], nbrs);
        nn[o] = 0;
        for (int i = 0; i < c; i++) {
            int w = orb[nbrs[i]], j;
            if (w == o) { printf("NODES 0\nUNSAT\n"); return 0; }   /* adjacent cells forced equal: impossible */
            for (j = 0; j < nn[o]; j++) if (nj[o][j] == w) break;
            if (j == nn[o]) { nj[o][j] = w; nm[o][j] = 0; nn[o]++; }
            nm[o][j]++;
        }
    }
    for (int o = 0; o < M; o++) {
        int v = orbit_cells[orbit_start[o]], x = v / (ny * nz), y = (v / nz) % ny, z = v % nz;
        key[o] = abs(2 * x - (nx - 1)) + abs(2 * y - (ny - 1)) + abs(2 * z - (nz - 1));
    }
    dom_t *dom = malloc(sizeof(dom_t) * M);
    for (int o = 0; o < M; o++) dom[o] = ((1ULL << (H + 1)) - 1);
    if (strcmp(argv[7], "-") != 0) {
        FILE *f = fopen(argv[7], "r"); int v;
        if (!f) { perror("pin"); return 2; }
        while (fscanf(f, "%d", &v) == 1) dom[orb[v]] = 1ULL;
        fclose(f);
    }
    if (argc > 11 && strcmp(argv[11], "-") != 0) {      /* FORBID: cells that may not be sources (their orbits lose label 0) */
        FILE *f = fopen(argv[11], "r"); int v;
        if (!f) { perror("forbid"); return 2; }
        while (fscanf(f, "%d", &v) == 1) if (dom[orb[v]] != 1ULL) dom[orb[v]] &= ~1ULL;
        fclose(f);
    }
    if (maxsol < 0) {                                   /* diagnostic: root-propagated domain of every cell */
        if (!propagate(dom)) { printf("UNSAT\n"); return 0; }
        printf("DOMAINS\n");
        for (int v = 0; v < N; v++) {
            dom_t d = dom[orb[v]];
            printf("%d %d %d\n", __builtin_ctzll(d), 63 - __builtin_clzll(d), __builtin_popcountll(d));
        }
        return 0;
    }
    long seed = argc > 9 ? atol(argv[9]) : 0, budget = argc > 10 ? atol(argv[10]) : 2000;
    if (seed) {                                         /* restart mode (use with MAXSOL = 1): randomised DFS, growing node limit */
        randomize = 1;
        rs = (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 88172645463325252ULL;
        int hit_global = 0;
        for (;;) {
            restart_nodes = 0; restart_limit = budget; limit_hit = 0;
            dfs(dom);
            if (found || !limit_hit) break;             /* solution found, or the whole tree was exhausted (UNSAT) */
            if (node_limit && nodes >= node_limit) { hit_global = 1; break; }
            budget += budget / 2 + 1;
        }
        limit_hit = hit_global;
    } else dfs(dom);
    printf("NODES %ld\n", nodes);
    if (maxsol && found >= maxsol) printf("SAT %ld\n", found);
    else if (limit_hit) printf("LIMIT %ld\n", found);
    else if (found) printf("SAT %ld\n", found);
    else printf("UNSAT\n");
    return 0;
}
