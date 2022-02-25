/* Gibbon program. */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <inttypes.h>
#include <math.h>
#include <stdbool.h>
#include <string.h>
#include <time.h>
#include <alloca.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>
#include <stdarg.h>
#include <errno.h>
// #include <uthash.h>

#ifdef _WIN64
#include <windows.h>
#endif

#ifdef _GIBBON_POINTER
#include <gc.h>
#endif

#ifdef _GIBBON_PARALLEL
#include <cilk/cilk.h>
#include <cilk/cilk_api.h>
#endif

typedef int64_t GibInt;
typedef bool GibBool;

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Vectors
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

typedef struct gib_vector {
    // Bounds on the vector.
    int64_t lower, upper;

    // Size of each element.
    size_t elt_size;

    // Elements of the vector.
    void *data;

} GibVector;

GibInt gib_vector_length(GibVector *vec)
{
    return (vec->upper - vec->lower);
}

GibVector *gib_vector_alloc(GibInt num, size_t elt_size)
{
    GibVector *vec = (GibVector *) malloc(sizeof(GibVector));
    if (vec == NULL) {
        fprintf(stderr, "alloc_vector: malloc failed: %ld", sizeof(GibVector));
        exit(1);
    }
    void *data = (void *) malloc(num * elt_size);
    if (data == NULL) {
        fprintf(stderr, "alloc_vector: malloc failed: %ld", sizeof(num * elt_size));
        exit(1);
    }
    vec->lower = 0;
    vec->upper = num;
    vec->elt_size = elt_size;
    vec->data = data;
    return vec;
}

void *gib_vector_nth(GibVector *vec, GibInt i)
{
#ifdef _GIBBON_BOUNDSCHECK
    if (i < vec->lower || i > vec->upper) {
        fprintf(stdderr, "gib_vector_nth index out of bounds: %lld (%lld,%lld)\n",
                i, vec->lower, vec->upper);
        exit(1);
    }
#endif
    return ((char*)vec->data + (vec->elt_size * (vec->lower + i)));
}

GibVector *gib_vector_inplace_update(GibVector *vec, GibInt i, void* elt)
{
    void* dst = gib_vector_nth(vec, i);
    memcpy(dst, elt, vec->elt_size);
    return vec;
}

void gib_vector_free(GibVector *vec)
{
    free(vec->data);
    free(vec);
    return;
}

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Program starts here
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

typedef struct GibIntProd_struct {
            GibInt field0;
        } GibIntProd;
typedef struct GibBoolProd_struct {
            GibBool field0;
        } GibBoolProd;
typedef struct GibVectorProd_struct {
            GibVector *field0;
        } GibVectorProd;
GibInt maxInt(GibInt a_273_663_776, GibInt b_274_664_777);
GibVector *generate_loop_452_633(GibVector *vec_205_705_796,
                                 GibInt idx_206_706_797, GibInt end_207_707_798,
                                 GibVector *vec_39_708_799);
GibVector *isort1_516_769(GibVector *xs_48_888_1045);
GibVector *isort_522_778(GibVector *xs_51_889_1049, GibInt n_52_890_1050);
GibVector *insert_525_779(GibVector *xs_58_894_1062, GibInt x_59_895_1063,
                          GibInt n_60_896_1064);
GibVector *isort2_445_629(GibVector *xs_22_710_806);
GibVector *go_448_634(GibInt i_33_712_812, GibInt n_34_713_813,
                      GibVector *ys_36_714_814);
GibVector *shift_449_635(GibInt j_25_716_818, GibVector *ys_27_717_819);
void printVec_loop_526_775(GibInt idx_149_880_1034,
                           GibInt end_150_881_1035,
                           GibVector *vec_151_882_1036);
void printVec_517_770(GibVector *vec_90_876_1029);
GibInt maxInt(GibInt a_273_663_776, GibInt b_274_664_777)
{
    GibBool fltIf_752_778 = a_273_663_776 > b_274_664_777;

    if (fltIf_752_778) {
        return a_273_663_776;
    } else {
        return b_274_664_777;
    }
}
GibVector *generate_loop_452_633(GibVector *vec_205_705_796,
                                 GibInt idx_206_706_797, GibInt end_207_707_798,
                                 GibVector *vec_39_708_799)
{
    GibBool fltIf_756_800 = idx_206_706_797 == end_207_707_798;

    if (fltIf_756_800) {
        return vec_205_705_796;
    } else {
        GibInt *tmp_0;

        tmp_0 = (GibInt *) gib_vector_nth(vec_39_708_799, idx_206_706_797);

        GibInt fltPrm_757_803 = *tmp_0;
        GibVector *vec1_210_709_804 = gib_vector_inplace_update(vec_205_705_796,
                                                                idx_206_706_797,
                                                                &fltPrm_757_803);
        GibInt fltAppE_758_805 = idx_206_706_797 + 1;
        GibVector *tailapp_850 =
                   generate_loop_452_633(vec1_210_709_804, fltAppE_758_805, end_207_707_798, vec_39_708_799);

        return tailapp_850;
    }
}
GibVector *isort1_516_769(GibVector *xs_48_888_1045)
{
    GibInt fltPrm_971_1047 = gib_vector_length(xs_48_888_1045);
    GibInt fltAppE_970_1048 = fltPrm_971_1047 - 1;
    GibVector *tailapp_1134 =  isort_522_778(xs_48_888_1045, fltAppE_970_1048);

    return tailapp_1134;
}
GibVector *isort_522_778(GibVector *xs_51_889_1049, GibInt n_52_890_1050)
{
    GibInt len_54_891_1052 = gib_vector_length(xs_51_889_1049);
    GibBool fltIf_972_1053 = len_54_891_1052 <= 1;

    if (fltIf_972_1053) {
        return xs_51_889_1049;
    } else {
        GibBool fltIf_973_1054 = n_52_890_1050 == 0;

        if (fltIf_973_1054) {
            GibInt tmp_2 = sizeof(GibInt);
            GibVector *ls_55_892_1056 = gib_vector_alloc(len_54_891_1052,
                                                         tmp_2);

            return ls_55_892_1056;
        } else {
            GibInt fltAppE_974_1057 = n_52_890_1050 - 1;
            GibVector *xs__56_893_1058 =
                       isort_522_778(xs_51_889_1049, fltAppE_974_1057);
            GibInt *tmp_3;

            tmp_3 = (GibInt *) gib_vector_nth(xs_51_889_1049, n_52_890_1050);

            GibInt fltAppE_975_1061 = *tmp_3;
            GibVector *tailapp_1135 =
                       insert_525_779(xs__56_893_1058, fltAppE_975_1061, n_52_890_1050);

            return tailapp_1135;
        }
    }
}
GibVector *insert_525_779(GibVector *xs_58_894_1062, GibInt x_59_895_1063,
                          GibInt n_60_896_1064)
{
    GibBool fltIf_976_1065 = n_60_896_1064 == 0;

    if (fltIf_976_1065) {
        GibVector *tailprim_1136 = gib_vector_inplace_update(xs_58_894_1062, 0,
                                                             &x_59_895_1063);

        return tailprim_1136;
    } else {
        GibInt i_88_848_937_1070 = n_60_896_1064 - 1;
        GibInt *tmp_4;

        tmp_4 = (GibInt *) gib_vector_nth(xs_58_894_1062, i_88_848_937_1070);

        GibInt y_62_897_1071 = *tmp_4;
        GibBool fltIf_979_1074 = x_59_895_1063 < y_62_897_1071;
        GibInt fltPrm_978_1076;

        if (fltIf_979_1074) {
            GibInt flt_1150 = 0 - 1;

            fltPrm_978_1076 = flt_1150;
        } else {
            GibBool fltIf_980_1075 = x_59_895_1063 > y_62_897_1071;

            if (fltIf_980_1075) {
                fltPrm_978_1076 = 1;
            } else {
                fltPrm_978_1076 = 0;
            }
        }

        GibBool fltIf_977_1077 = fltPrm_978_1076 < 0;

        if (fltIf_977_1077) {
            GibVector *xs__63_898_1081 =
                      gib_vector_inplace_update(xs_58_894_1062, n_60_896_1064,
                                                &y_62_897_1071);
            GibInt fltAppE_981_1082 = n_60_896_1064 - 1;
            GibVector *tailapp_1137 =
                       insert_525_779(xs__63_898_1081, x_59_895_1063, fltAppE_981_1082);

            return tailapp_1137;
        } else {
            GibVector *tailprim_1138 = gib_vector_inplace_update(xs_58_894_1062,
                                                                 n_60_896_1064,
                                                                 &x_59_895_1063);

            return tailprim_1138;
        }
    }
}
GibVector *isort2_445_629(GibVector *xs_22_710_806)
{
    GibInt n_24_711_808 = gib_vector_length(xs_22_710_806);
    GibInt fltAppE_760_810 = gib_vector_length(xs_22_710_806);
    GibInt n__56_697_783_846 =  maxInt(fltAppE_760_810, 0);
    GibInt tmp_1 = sizeof(GibInt);
    GibVector *vec_57_698_784_847 = gib_vector_alloc(n__56_697_783_846, tmp_1);
    // GibVector *vec1_58_699_785_848 =
    //            generate_loop_452_633(vec_57_698_784_847, 0, n__56_697_783_846, xs_22_710_806);
    GibVector *vec1_58_699_785_848 = xs_22_710_806;
    GibVector *tailapp_851 =  go_448_634(1, n_24_711_808, vec1_58_699_785_848);

    return tailapp_851;
}
GibVector *go_448_634(GibInt i_33_712_812, GibInt n_34_713_813,
                      GibVector *ys_36_714_814)
{
    GibBool fltIf_761_815 = i_33_712_812 == n_34_713_813;

    if (fltIf_761_815) {
        return ys_36_714_814;
    } else {
        GibVector *ys__38_715_816 =  shift_449_635(i_33_712_812, ys_36_714_814);
        GibInt fltAppE_762_817 = i_33_712_812 + 1;
        GibVector *tailapp_852 =
                   go_448_634(fltAppE_762_817, n_34_713_813, ys__38_715_816);

        return tailapp_852;
    }
}
GibVector *shift_449_635(GibInt j_25_716_818, GibVector *ys_27_717_819)
{
    GibBool fltIf_763_820 = j_25_716_818 == 0;

    if (fltIf_763_820) {
        return ys_27_717_819;
    } else {
        GibInt *tmp_3;

        tmp_3 = (GibInt *) gib_vector_nth(ys_27_717_819, j_25_716_818);

        GibInt a_29_718_823 = *tmp_3;
        GibInt i_49_680_743_825 = j_25_716_818 - 1;
        GibInt *tmp_2;

        tmp_2 = (GibInt *) gib_vector_nth(ys_27_717_819, i_49_680_743_825);

        GibInt b_30_719_826 = *tmp_2;
        GibBool fltIf_766_829 = a_29_718_823 < b_30_719_826;
        GibInt fltPrm_765_831;

        if (fltIf_766_829) {
            GibInt flt_855 = 0 - 1;

            fltPrm_765_831 = flt_855;
        } else {
            GibBool fltIf_767_830 = a_29_718_823 > b_30_719_826;

            if (fltIf_767_830) {
                fltPrm_765_831 = 1;
            } else {
                fltPrm_765_831 = 0;
            }
        }

        GibBool fltIf_764_832 = fltPrm_765_831 > 0;

        if (fltIf_764_832) {
            return ys_27_717_819;
        } else {
            GibVector *ys__31_720_836 = gib_vector_inplace_update(ys_27_717_819,
                                                                  j_25_716_818,
                                                                  &b_30_719_826);
            GibInt i_44_681_749_837 = j_25_716_818 - 1;
            GibVector *ys___32_721_840 =
                      gib_vector_inplace_update(ys__31_720_836,
                                                i_44_681_749_837,
                                                &a_29_718_823);
            GibInt fltAppE_768_841 = j_25_716_818 - 1;
            GibVector *tailapp_853 =
                       shift_449_635(fltAppE_768_841, ys___32_721_840);

            return tailapp_853;
        }
    }
}
void printVec_517_770(GibVector *vec_90_876_1029)
{
    printf("[");
    GibInt fltAppE_963_1031 = gib_vector_length(vec_90_876_1029);
    printVec_loop_526_775(0, fltAppE_963_1031, vec_90_876_1029);
    printf("]\n");
    return;
}
void printVec_loop_526_775(GibInt idx_149_880_1034,
                                    GibInt end_150_881_1035,
                                    GibVector *vec_151_882_1036)
{
    GibBool fltIf_964_1037 = idx_149_880_1034 == end_150_881_1035;

    if (fltIf_964_1037) {
        return;
    } else {
        GibInt *tmp_1;

        tmp_1 = (GibInt *) gib_vector_nth(vec_151_882_1036, idx_149_880_1034);

        GibInt i_41_853_923_1038 = *tmp_1;
        printf("%ld", i_41_853_923_1038);
        printf(", ");
        GibInt fltAppE_965_1041 = idx_149_880_1034 + 1;
        printVec_loop_526_775(fltAppE_965_1041, end_150_881_1035, vec_151_882_1036);

        return;
    }
}
/*
int gib_main_expr(void)
{
    info_table_initialize();
    symbol_table_initialize();

    GibInt n_18_659_769 = gib_get_size_param();
    GibInt n_53_688_722_770 = gib_get_size_param();
    GibInt n__56_690_724_772 =  maxInt(n_53_688_722_770, 0);
    GibInt tmp_4 = sizeof(GibInt);
    GibVector *vec_57_691_725_773 = gib_vector_alloc(n__56_690_724_772, tmp_4);
    GibVector *vec1_58_692_726_774 =
               generate_loop_452_632(vec_57_691_725_773, 0, n__56_690_724_772, n_18_659_769);
    GibVector *tailapp_854 =  isort2_445_629(vec1_58_692_726_774);

    printf("<vector>");
    printf("\n");
    gib_free_symtable();
    return 0;
}
*/

int bench_gibbon_insertion2(int argc, char** argv)
{
    char *algo = argv[1];
    char *elt_type = argv[2];
    uint32_t N = atoi(argv[3]);
    // int rounds = atol(argv[4]);

    // Sorting params.
    size_t elt_size = sizeof(GibInt);
    GibVector *vec = gib_vector_alloc(N, elt_size);
    GibInt elt;
    for (GibInt i = 0; i <= N-1; i++) {
        elt = rand();
        gib_vector_inplace_update(vec, i, &elt);
    }

    GibVector *vec2;
    // vec2 = isort2_445_629(vec);
    // printVec_517_770(vec2);
    // printf("\n");
    // exit(1);

    // Start protocol for criterion-interactive.
    printf("READY\n");
    fflush(stdout);

    char *criterion_cmd = (char*) malloc(100);
    ssize_t read;
    size_t len;
    uint32_t rounds;
    uint32_t i;

    // Wait for criterion-interactive to send a command.
    read = getline(&criterion_cmd, &len, stdin);
    while (strcmp(criterion_cmd,"EXIT") != 0) {
        if (read == -1) {
            printf("Couldn't read from stdin, error=%d\n", errno);
            exit(1);
        }

        // One round of benchmarking.
        if (strncmp(criterion_cmd,"START_BENCH", 11) == 0) {
            rounds = atol(criterion_cmd+12);

#ifdef CBENCH_DEBUG
            puts(criterion_cmd);
            printf("rounds=%" PRIu32 "\n", rounds);
#endif

            // The main event.
            for (i = 0; i <= rounds; i++) {
                vec2 = isort2_445_629(vec);
            }

            printf("END_BENCH\n");
            fflush(stdout);
        }

        // Prepare for next round.
        rounds=0;
        read = getline(&criterion_cmd, &len, stdin);
    }

    printVec_517_770(vec);
    free(criterion_cmd);
    gib_vector_free(vec);

    return 0;
}

int bench_gibbon_insertion1(int argc, char** argv)
{
    char *algo = argv[1];
    char *elt_type = argv[2];
    uint32_t N = atoi(argv[3]);
    // int rounds = atol(argv[4]);

    // Sorting params.
    size_t elt_size = sizeof(GibInt);
    GibVector *vec = gib_vector_alloc(N, elt_size);
    GibInt elt;
    for (GibInt i = 0; i <= N-1; i++) {
        elt = rand();
        gib_vector_inplace_update(vec, i, &elt);
    }

    GibVector *vec2;
    // vec2 = isort1_516_769(vec);
    // printVec_517_770(vec2);
    // printf("\n");
    // exit(1);

    // Start protocol for criterion-interactive.
    printf("READY\n");
    fflush(stdout);

    char *criterion_cmd = (char*) malloc(100);
    ssize_t read;
    size_t len;
    uint32_t rounds;
    uint32_t i;

    // Wait for criterion-interactive to send a command.
    read = getline(&criterion_cmd, &len, stdin);
    while (strcmp(criterion_cmd,"EXIT") != 0) {
        if (read == -1) {
            printf("Couldn't read from stdin, error=%d\n", errno);
            exit(1);
        }

        // One round of benchmarking.
        if (strncmp(criterion_cmd,"START_BENCH", 11) == 0) {
            rounds = atol(criterion_cmd+12);

#ifdef CBENCH_DEBUG
            puts(criterion_cmd);
            printf("rounds=%" PRIu32 "\n", rounds);
#endif

            // The main event.
            for (i = 0; i <= rounds; i++) {
                vec2 = isort1_516_769(vec);
            }

            printf("END_BENCH\n");
            fflush(stdout);
        }

        // Prepare for next round.
        rounds=0;
        read = getline(&criterion_cmd, &len, stdin);
    }

    free(criterion_cmd);
    gib_vector_free(vec);

    return 0;
}
