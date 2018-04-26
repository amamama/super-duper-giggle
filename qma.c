#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <ctype.h>
#include <assert.h>

#define BIT(n, i) ((((n) & (1 << (i))) >> (i)) & 1u)
#define XOR(x, n) XOR##n(x)
#define XOR4(x) (BIT(x, 0) ^ BIT(x, 2) ^ BIT(x, 3))
#define XOR5(x) (BIT(x, 0) ^ BIT(x, 1) ^ BIT(x, 3))
#define XOR6(x) (BIT(x, 1) ^ BIT(x, 2) ^ BIT(x, 3))

uint8_t encode(uint8_t i) {
        return (i & 0xf)
                |  (XOR(i, 4) << 4)
                |  (XOR(i, 5) << 5)
                |  (XOR(i, 6) << 6)
                ;
}

#define CHKBIT(x, op, n) (XOR(x, n) op BIT(x, n))
#define CHK(x, op1, op2, op3, s) (((CHKBIT(x, op1, 4) & CHKBIT(x, op2, 5) & CHKBIT(x, op3, 6))  ^ BIT(x, s)) << s)

uint8_t decode(uint8_t x) {
        return CHK(x, !=, !=, ==, 0)
                |  CHK(x, ==, !=, !=, 1)
                |  CHK(x, !=, ==, !=, 2)
                |  CHK(x, !=, !=, !=, 3)
                |  CHK(x, !=, ==, ==, 4)
                |  CHK(x, ==, !=, ==, 5)
                |  CHK(x, ==, ==, !=, 6)
                ;
}

#define hamming_dist(n, m) (__builtin_popcount((n) ^ (m)))

//-------------huffman coding----------------------------

typedef struct set *set_p;
typedef struct set {
        __uint128_t bitset;
        set_p next;
        bool ispl; //prime implicants
} set;

set_p alloc_set(__uint128_t s, set_p n) {
        set_p ret = malloc(sizeof(set));
        assert(ret);
        ret->bitset = s;
        ret->next = n;
        ret->ispl = false;
        return ret;
}

void free_set(set_p s) {
        if(!s) return;
        free_set(s->next);
        free(s);
}

set_p copy_set(set_p s) {
        if(!s) return NULL;
        return alloc_set(s->bitset, copy_set(s->next));
}

bool is_member(__uint128_t bs, set_p s) {
        if(!s) return false;
        if(bs == s->bitset) return true;
        return is_member(bs, s->next);
}

bool is_subset(set_p s, set_p t) {
        if(!s) return true;
        if(!is_member(s->bitset, t)) return false;
        return is_subset(s->next, t);
}

set_p union_set(set_p s, set_p t) {
        if(!t) return copy_set(s);
        if(is_member(t->bitset, s)) return union_set(s, t->next);
        return alloc_set(t->bitset, union_set(s, t->next));
}

set_p intersection_set(set_p s, set_p t) {
        if(!t) return NULL;
        if(is_member(t->bitset, s)) return alloc_set(t->bitset, intersection_set(s, t->next));
        return intersection_set(s, t->next);
}

set_p remove_set(set_p s, set_p i) {
        if(s == i) return s->next;
        for(set_p t = s; t; t = t->next) {
                if(t->next == i) {
                        t->next = t->next->next;
                }
        }
        return s;
}

size_t size_set(set_p s) {
        if(!s) return 0;
        return size_set(s->next) + 1;
}

int print_bin(uint8_t n) {
        for(int i = 7; i >= 0; i--) {
                printf("%c", 0x30 + BIT(n, i));
        }
        return 0;
}

#define foreach_bitset(n, v) for(uint8_t v; v = (__builtin_ffsll(n)?:(64 + __builtin_ffsll(n >> 64))) - 1, n; n &= ~(((__uint128_t)1) << v))
int print_bitset(__uint128_t n) {
        int i = 0;
        printf("{");
        foreach_bitset(n, ffs) {
                printf("%d, ", ffs);
                //isgraph(ffs)?printf("%c, ", ffs):printf("%#x, ", ffs);
                i+=ffs;
        }
        printf("}");
        //printf("%d", i);
        return 0;
}

size_t size_bitset(__uint128_t n) {
        size_t ret = 0;
        foreach_bitset(n, v) { ret++; }
        return ret;
}

int print_set(set_p s) {
        printf("{");
        for(; s; s = s->next) {
                print_bitset(s->bitset);
                printf("%s", s->ispl?"*":"");
                printf(", ");
        }
        printf("}");
        return 0;
}

typedef set_p *set_hamming;

void free_set_hamming(set_hamming s) {
        for(int i = 0; i < 9; i++) {
                free_set(s[i]);
        }
        free(s);
}

set_hamming reg_minterm(uint8_t r[128], size_t d) {
        set_hamming ret = malloc(sizeof(set_p[9]));
        for(int i = 0; i < 9; i++) {ret[i] = NULL;}
        for(size_t i = 0; i < 128; i++) {
                if(BIT(r[i], d)) {
                        ret[__builtin_popcount(i)] = alloc_set(((__uint128_t)1) << i, ret[__builtin_popcount(i)]);
                }
        }
        ret[8] = NULL;
        return ret;
}

uint16_t uint8to16(uint8_t n) {
        return (BIT(n, 6) << 12)
                 | (BIT(n, 5) << 10)
                 | (BIT(n, 4) << 8)
                 | (BIT(n, 3) << 6)
                 | (BIT(n, 2) << 4)
                 | (BIT(n, 1) << 2)
                 | (BIT(n, 0) << 0)
                 ;
}


#define CHK_DC(n, m, d) (((BIT(n, 2 * d) ^ BIT(m, 2 * d)) << (2 * d + 1)) | ((BIT(n, 2 * d) & BIT(m, 2 * d)) << (2 * d)))
uint16_t repr_w_dc(uint16_t n, uint16_t m) {
        return CHK_DC(n, m, 6)
                 | CHK_DC(n, m, 5)
                 | CHK_DC(n, m, 4)
                 | CHK_DC(n, m, 3)
                 | CHK_DC(n, m, 2)
                 | CHK_DC(n, m, 1)
                 | CHK_DC(n, m, 0)
                 ;
}

uint16_t minterm_repr(__uint128_t n) {
        uint16_t ret = uint8to16((__builtin_ffsll(n)?:(64 + __builtin_ffsll(n >> 64))) - 1);
        foreach_bitset(n, ffs) {
                ret = repr_w_dc(ret, uint8to16(ffs));
        }
        return ret;
}

bool is_combinable(uint16_t n, uint16_t m) {
        return hamming_dist(n, m) < 2;
}

set_p combine_list(set_p s, set_p t) {
        set_p ret = NULL;
        for(; s; s = s->next) {
                if(s->ispl) {
                        ret = alloc_set(s->bitset, ret);
                        ret->ispl = true;
                        continue;
                }

                bool is_combined = false;
                for(set_p tmp = t; tmp; tmp = tmp->next) {
                        __uint128_t n = s->bitset, m = tmp->bitset;
                        if(__builtin_popcountll(n >> 64) + __builtin_popcountll(n)
                        != __builtin_popcountll(m >> 64) + __builtin_popcountll(m)) {
                                continue;
                        }
                        uint16_t ffsn = minterm_repr(n), ffsm = minterm_repr(m);

                        if(is_combinable(ffsn, ffsm)) {
                                ret = union_set(ret, alloc_set(n | m, NULL));
                                is_combined = true;
                        }
                }
                if(!is_combined) {
                ret = alloc_set(s->bitset, ret);
                ret->ispl = true;
                }
        }
        return ret;
}


set_hamming combine_minterm(set_p minterm[8]) {
        set_hamming new_minterm = malloc(sizeof(set_p[9]));
        for(int i = 0; i < 8; i++) {
                new_minterm[i] = NULL;
                new_minterm[i + 1] = NULL;
                new_minterm[i] = combine_list(minterm[i], minterm[i + 1]);
        }
        return new_minterm;
}

bool is_all_pl(set_hamming s) {
        for(int i = 0; i < 8; i++) {
                for(set_p t = s[i]; t; t = t->next) {
                        if(!t->ispl) return false;
                }
        }
        return true;
}

#define is_subbitset(n, m) (n < m && (n | m) == m)
set_hamming minimize(set_hamming hs) {
        set_hamming ret = malloc(sizeof(set_p[9]));
        for(int i = 7; i > 0; i--) {
                ret[i] = NULL;
                for(set_p s = hs[i]; s; s = s->next) {
                        bool rm = false;
                        for(set_p t = hs[i - 1]; t; t = t->next) {
                                if(is_subbitset(s->bitset, t->bitset)) {
                                        rm = true;
                                        break;
                                }
                        }
                        if(!rm) {
                                ret[i] = alloc_set(s->bitset, ret[i]);
                                ret[i]->ispl = s->ispl;
                        }
                }
        }
        ret[0] = copy_set(hs[0]);
        return ret;
}

typedef struct history *history_p;
typedef struct history {
        set_p hist;
        history_p next;
        size_t size;
} history;

history_p alloc_history(set_p h, history_p n) {
        history_p ret = malloc(sizeof(history));
        ret->hist = h;
        ret->next = n;
        return ret;
}

void free_history(history_p h) {
        if(!h) return;
        free_history(h->next);
        free_set(h->hist);
        return;
}

set_p insert(set_p sorted, set_p i) {
        size_t size = size_bitset(i->bitset);
        if(!sorted || size <= size_bitset(sorted->bitset)) return alloc_set(i->bitset, sorted);
        set_p t = NULL;
        for(t = sorted; t->next; t = t->next) {
                if(size > size_bitset(t->bitset)) continue;
                t->next = alloc_set(i->bitset, t->next);
                return sorted;
        }
        t->next = alloc_set(i->bitset, NULL);
        return sorted;
}

set_p insertion_sort(set_p l) {
        set_p inserted = NULL;
        for(; l; l = l->next) {
                inserted = insert(inserted, l);
        }
        return inserted;
}

history_p sort_history(history_p hist) {
        for(history_p h = hist; h; h = h->next) {
                h->hist = insertion_sort(h->hist);
        }
        return hist;
}

history_p minimize_history(history_p hist) {
        for(history_p h = hist; h; h = h->next) {
                for(set_p t = h->hist; t; t = t->next) {
                        __uint128_t mask = 0;
                        for(set_p u = h->hist; u; u = u->next) {
                                if(u == t) continue;
                                mask |= u->bitset;
                        }

                        if(is_subbitset(t->bitset, mask)) {
                                h->hist = remove_set(h->hist, t);
                        }
                }
        }
        return hist;
}

int print_history(history_p h) {
        printf("{");
        for(; h; h = h->next) {
        printf("{size %u, ", size_set(h->hist));
        print_set(h->hist);
        printf("}\n");
        }
        printf("}");
        return 0;
}

int petrick_method(uint8_t r[128], size_t d, bool iscontain[128], set_p chart[128]) {
        set_p mpi = NULL;
        history_p hist = alloc_history(NULL, NULL);
        printf("found multiple pi\n");
        for(int i = 0; i < 128; i++) {
                if(!(BIT(r[i], d) && iscontain[i] == false)) continue;

                history_p new_hist = NULL;
                for(history_p h = hist; h; h = h->next) {
                        size_t min = 128;
                        for(set_p t = chart[i]; t; t = t->next) {
                                set_p tmp = union_set(h->hist, alloc_set(t->bitset, NULL));
                                size_t size = size_set(tmp);
                                if(size == min) new_hist = alloc_history(tmp, new_hist);
                                else if(size < min) {
                                        free_history(new_hist);
                                        new_hist = alloc_history(tmp, NULL);
                                        min = size;
                                }
                                else free_set(tmp);
                        }
                }
                free_history(hist);
                hist = new_hist;

                mpi = union_set(mpi, chart[i]);
        }
        hist = sort_history(hist);
        hist = minimize_history(hist);
        print_history(hist);
        free_history(hist);
}

set_p find_epi(uint8_t r[128], size_t d, set_p pl_list) { //  find the essential prime implicants
        set_p chart[128] = {NULL};
        for(set_p t = pl_list; t; t = t->next) {
                __uint128_t n = t->bitset;
                foreach_bitset(n, ffs) {
                        chart[ffs] = alloc_set(t->bitset, chart[ffs]);
                }
        }

        printf("essential prime implicants\n");

        set_p ret = NULL;
        bool iscontain[128] = {false};
        for(int i = 0; i < 128; i++) {
                if(BIT(r[i], d) && iscontain[i] == false && chart[i]->next == NULL) {
                        print_set(chart[i]);
                        ret = alloc_set(chart[i]->bitset, ret);
                        printf(", ");

                        __uint128_t n = chart[i]->bitset;
                        foreach_bitset(n, ffs) {
                                iscontain[ffs] = true;
                        }
                }
        }
        puts("");
        petrick_method(r, d, iscontain, chart);
        for(int i = 0; i < 128; i++) {
                free_set(chart[i]);
        }
        return 0;
}

//----------------quine-mccluskey_algorithm-------------------
int main(void) {
        uint8_t r[128] = {0};
        for(uint8_t i = 0; i < 128u; i++) {
                for(uint8_t j = 0; j < 16u; j++) {
                        int d = 0;
                        if((d = hamming_dist(i, encode(j))) < 2) {
                                r[i] = decode(i);
                                break;
                        }
                }
        }

        for(int i = 0; i < 128; i++) {
                print_bin(i);
                printf(" ");
                print_bin(r[i]);
                puts("");
        }
        for(int i = 0; i < 7; i++) {
                set_hamming step = reg_minterm(r, i), old_step = NULL;
                for(int i = 0; !is_all_pl(step); ) {
                        old_step = step;
                        step = combine_minterm(step);
                        free_set_hamming(old_step);
                        puts("");
                }
                old_step = step;
                step = minimize(step);
                free_set_hamming(old_step);

                set_p pl_list = NULL;
                for(int i = 0; i < 8; i++) {
                        pl_list = union_set(pl_list, step[i]);
                }
                find_epi(r, i, pl_list);
                free_set(pl_list);
        }
}
