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

static inline GibInt gib_vector_length(GibVector *vec)
{
    return (vec->upper - vec->lower);
}

static inline GibVector *gib_vector_alloc(GibInt num, size_t elt_size)
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

static inline void *gib_vector_nth(GibVector *vec, GibInt i)
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

static inline GibVector *gib_vector_inplace_update(GibVector *vec, GibInt i, void* elt)
{
    void* dst = gib_vector_nth(vec, i);
    memcpy(dst, elt, vec->elt_size);
    return vec;
}

static inline void gib_vector_free(GibVector *vec)
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
GibVector *isort1_531_794(GibVector *xs_52_928_1105);
GibVector *generate_loop_542_806(GibVector *vec_252_932_1120,
                                 GibInt idx_253_933_1121,
                                 GibInt end_254_934_1122,
                                 GibInt hd_55_935_1123);
GibVector *isort_538_805(GibVector *xs_59_937_1130, GibVector *b_60_938_1131,
                         GibInt n_61_939_1132);
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
GibVector *isort1_531_794(GibVector *xs_52_928_1105)
{
    GibInt n_54_929_1107 = gib_vector_length(xs_52_928_1105);
    GibInt *tmp_3;
    
    tmp_3 = (GibInt *) gib_vector_nth(xs_52_928_1105, 0);
    
    GibInt hd_55_930_1110 = *tmp_3;
    GibInt n__101_925_981_1113 =  maxInt(n_54_929_1107, 0);
    GibInt tmp_2 = sizeof(GibInt);
    GibVector *vec_102_926_982_1114 = gib_vector_alloc(n__101_925_981_1113,
                                                       tmp_2);
    GibVector *vec1_103_927_983_1115 =
               generate_loop_542_806(vec_102_926_982_1114, 0, n__101_925_981_1113, hd_55_930_1110);
    GibInt fltPrm_1028_1118 = gib_vector_length(xs_52_928_1105);
    GibInt fltAppE_1027_1119 = fltPrm_1028_1118 - 1;
    
    return isort_538_805(xs_52_928_1105, vec1_103_927_983_1115,
                         fltAppE_1027_1119);
}
GibVector *generate_loop_542_806(GibVector *vec_252_932_1120,
                                 GibInt idx_253_933_1121,
                                 GibInt end_254_934_1122, GibInt hd_55_935_1123)
{
    GibBool fltIf_1029_1124 = idx_253_933_1121 == end_254_934_1122;
    
    if (fltIf_1029_1124) {
        return vec_252_932_1120;
    } else {
        GibVector *vec1_257_936_1128 =
                  gib_vector_inplace_update(vec_252_932_1120, idx_253_933_1121,
                                            &hd_55_935_1123);
        GibInt fltAppE_1031_1129 = idx_253_933_1121 + 1;
        
        return generate_loop_542_806(vec1_257_936_1128, fltAppE_1031_1129,
                                     end_254_934_1122, hd_55_935_1123);
    }
}
GibVector *isort_538_805(GibVector *xs_59_937_1130, GibVector *b_60_938_1131,
                         GibInt n_61_939_1132)
{    
    GibInt len_63_940_1134 = gib_vector_length(xs_59_937_1130);
    GibBool fltIf_1032_1135 = len_63_940_1134 <= 1;
    
    if (fltIf_1032_1135) {
        return xs_59_937_1130;
    } else {
        GibBool fltIf_1033_1136 = n_61_939_1132 == 0;
        
        if (fltIf_1033_1136) {
            return b_60_938_1131;
        } else {
            GibInt fltAppE_1034_1137 = n_61_939_1132 - 1;
            GibVector *xs__64_941_1138 =
                       isort_538_805(xs_59_937_1130, b_60_938_1131, fltAppE_1034_1137);
            GibInt *tmp_4;
            
            tmp_4 = (GibInt *) gib_vector_nth(xs_59_937_1130, n_61_939_1132);
            
            GibInt fltAppE_1035_1141 = *tmp_4;
            
            return insert_525_779(xs__64_941_1138, fltAppE_1035_1141,
                                  n_61_939_1132);
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
                vec2 = isort1_531_794(vec);
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



/* -------------------------------------------------------------------------- */


/*
GibVector *generate_loop_389_515(GibVector *vec_161_546_568,
                                GibInt idx_162_547_569, GibInt end_163_548_570)
{
    GibBool fltIf_556_571 = idx_162_547_569 == end_163_548_570;

    if (fltIf_556_571) {
        return vec_161_546_568;
    } else {
        GibInt tmp_0 = 1000;
        GibVector *vec1_166_549_574 = gib_vector_inplace_update(vec_161_546_568,
                                                           idx_162_547_569,
                                                           &tmp_0);
        GibInt fltAppE_558_575 = idx_162_547_569 + 1;

        return generate_loop_389_515(vec1_166_549_574, fltAppE_558_575,
                                     end_163_548_570);
    }
}
*/
GibVector *generate_loop_389_515(GibVector *vec_161_546_568,
                                GibInt idx_162_547_569, GibInt end_163_548_570)
{
    GibInt tmp_0 = 1000;
    GibInt *dst;
    for (int i = 0; i < end_163_548_570; i++) {
        gib_vector_inplace_update(vec_161_546_568,
                                  idx_162_547_569,
                                  &tmp_0);

    }
    return vec_161_546_568;
}

int bench_gibbon_fillarray(int argc, char** argv)
{
    uint32_t N = atoi(argv[3]);
    // int rounds = atol(argv[4]);


    GibVector *vec_10_544_552_562 = NULL;
    GibVector *vec1_11_545_553_563 = NULL;

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
                vec_10_544_552_562 = gib_vector_alloc(N, sizeof(GibInt));
                vec1_11_545_553_563 =
                        generate_loop_389_515(vec_10_544_552_562, 0, N);

            }

            printf("END_BENCH\n");
            fflush(stdout);
        }

        // Prepare for next round.
        rounds=0;
        read = getline(&criterion_cmd, &len, stdin);
    }

    free(criterion_cmd);
    gib_vector_free(vec1_11_545_553_563);
    gib_vector_free(vec_10_544_552_562);

    return 0;
}
