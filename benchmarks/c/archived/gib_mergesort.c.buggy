b/* Gibbon program. */

#include "gibbon_rts.h"

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

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Program starts here
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

typedef struct GibIntProd_struct {
            GibInt field0;
        } GibIntProd;
typedef struct GibIntGibVectorProd_struct {
            GibInt field0;
            GibVector *field1;
        } GibIntGibVectorProd;
typedef struct GibIntGibVectorGibIntGibVectorProd_struct {
            GibInt field0;
            GibVector *field1;
            GibInt field2;
            GibVector *field3;
        } GibIntGibVectorGibIntGibVectorProd;
typedef struct GibFloatProd_struct {
            GibFloat field0;
        } GibFloatProd;
typedef struct GibBoolProd_struct {
            GibBool field0;
        } GibBoolProd;
typedef struct GibVectorProd_struct {
            GibVector *field0;
        } GibVectorProd;
unsigned char print_check(GibBool b_568_2644_3753);
GibInt compare_float_original(GibFloat r1_591_2649_3756,
                              GibFloat r2_592_2650_3757);
int compare_float(const void *r1_591_2649_3756, const void *r2_592_2650_3757);
GibInt maxInt(GibInt a_593_2651_3760, GibInt b_594_2652_3761);
GibInt minInt(GibInt a_601_2659_3763, GibInt b_602_2660_3764);
GibIntGibVectorGibIntGibVectorProd lsplitAt__1446(GibInt n_747_2670_3771,
                                                  GibVector *vec_748_2671_3772);
GibIntGibVectorProd length2_1427(GibVector *vec_553_2687_3788);
GibVector *write_loop_seq_1434(GibInt to_idx_494_2704_3799,
                               GibInt from_idx_495_2705_3800,
                               GibInt end_496_2706_3801,
                               GibVector *from_497_2707_3802,
                               GibVector *to_498_2708_3803);
GibVector *write_loop_1435(GibInt to_idx_478_2713_3820,
                           GibInt from_idx_479_2714_3821,
                           GibInt end_480_2715_3822,
                           GibVector *from_481_2716_3823,
                           GibVector *to_482_2717_3824);
GibVector *copy_par_1396(GibVector *vec_875_2770_3840);
GibVector *copy_1394(GibVector *vec_734_2775_3848);
GibVector *generate_par_loop_1406_2351(GibInt cutoff_892_2823_3857,
                                       GibVector *vec_893_2824_3858,
                                       GibInt start_894_2825_3859,
                                       GibInt end_895_2826_3860,
                                       GibVector *vec_875_2827_3861);
GibVector *generate_loop_1400_2352(GibVector *vec_737_2832_3869,
                                   GibInt idx_738_2833_3870,
                                   GibInt end_739_2834_3871,
                                   GibVector *vec_875_2835_3872);
GibVector *generate_loop_1400_2355(GibVector *vec_737_2855_3883,
                                   GibInt idx_738_2856_3884,
                                   GibInt end_739_2857_3885);
GibVector *generate_loop_1400_2356(GibVector *vec_737_2863_3896,
                                   GibInt idx_738_2864_3897,
                                   GibInt end_739_2865_3898);
GibVector *generate_loop_1400_2357(GibVector *vec_737_2867_3905,
                                   GibInt idx_738_2868_3906,
                                   GibInt end_739_2869_3907,
                                   GibVector *vec_734_2870_3908);
GibVector *writeSort1_seq_1447_2362(GibVector *src00_353_2898_3922,
                                    GibVector *tmp_354_2899_3923);
GibVector *writeSort2_seq_1448_2364(GibVector *src0_306_2918_3956,
                                    GibVector *tmp0_307_2919_3957);
GibVector *writeMerge_seq_1436_2365(GibInt n1_454_2940_3991,
                                    GibVector *src_1_455_2941_3992,
                                    GibInt n2_456_2942_3993,
                                    GibVector *src_2_457_2943_3994,
                                    GibVector *tmp_458_2944_3995);
GibVector *writeMerge_seq_loop_1442_2366(GibInt i1_460_2945_3996,
                                         GibInt i2_461_2946_3997,
                                         GibInt j_462_2947_3998,
                                         GibInt n1_463_2948_3999,
                                         GibInt n2_464_2949_4000,
                                         GibVector *src_1_466_2950_4001,
                                         GibVector *src_2_467_2951_4002,
                                         GibVector *tmp_468_2952_4003);
GibVector *writeSort1_1429_2368(GibVector *src00_375_2966_4050,
                                GibVector *tmp_376_2967_4051);
GibVector *writeMerge_1433_2370(GibInt n1_447_2987_4085,
                                GibVector *src_10_448_2988_4086,
                                GibInt n2_449_2989_4087,
                                GibVector *src_20_450_2990_4088,
                                GibVector *tmp0_451_2991_4089);
GibIntGibVectorProd binarySearch_1439_2372(GibVector *vec_505_3002_4108,
                                           GibFloat query_506_3003_4109);
GibInt binarySearch__1445_2375(GibInt lo_513_3007_4115, GibInt hi_514_3008_4116,
                               GibVector *vec_516_3009_4117,
                               GibFloat query_517_3010_4118);
GibVector *writeSort2_1432_2369(GibVector *src0_329_3050_4203,
                                GibVector *tmp0_330_3051_4204);
unsigned char check_sorted_1377_2334(GibVector *sorted_278_3213_4239);
GibBool ifoldl_loop_1398_2390(GibInt idx_660_3217_4253,
                              GibInt end_661_3218_4254,
                              GibBool acc_663_3219_4255,
                              GibVector *vec_664_3220_4256,
                              GibVector *arr1_281_3221_4257);
/*
typedef enum {
            GibInt_T,
            GibFloat_T,
            GibSym_T,
            GibBool_T,
            GibVector_T,
            GibList_T,
            GibCursor_T,
        } GibDatatype;
void info_table_initialize(void)
{
    int error = gib_info_table_initialize(7);
    
    if (error < 0) {
        fprintf(stderr, "Couldn't initialize info table, errorno=%d", error);
        exit(1);
    }
    
    GibDatatype field_tys[0];
    
    gib_info_table_finalize();
}
void symbol_table_initialize(void)
{
    gib_add_symbol(4658, "OK\n");
    gib_add_symbol(4659, "Err\n");
}
unsigned char print_check(GibBool b_568_2644_3753)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;        
    
    if (b_568_2644_3753) {
        unsigned char wildcard__14_569_2645_3754 = gib_print_symbol(4658);
        
        return 0;
    } else {
        unsigned char wildcard__16_570_2646_3755 = gib_print_symbol(4659);
        
        return 0;
    }
}
*/
GibInt compare_float_original(GibFloat r1_591_2649_3756,
                              GibFloat r2_592_2650_3757)
{            
    GibBool fltIf_3646_3758 = r1_591_2649_3756 < r2_592_2650_3757;
    
    if (fltIf_3646_3758) {
        GibInt tailprim_4615 = 0 - 1;
        
        return tailprim_4615;
    } else {
        GibBool fltIf_3647_3759 = r1_591_2649_3756 > r2_592_2650_3757;
        
        if (fltIf_3647_3759) {
            return 1;
        } else {
            return 0;
        }
    }
}
int compare_float(const void *r1_591_2649_3756, const void *r2_592_2650_3757)
{
    GibFloat fst_0 = *(GibFloat *) r1_591_2649_3756;
    GibFloat snd_1 = *(GibFloat *) r2_592_2650_3757;
    
    return compare_float_original(fst_0, snd_1);
}
/*
GibInt maxInt(GibInt a_593_2651_3760, GibInt b_594_2652_3761)
{
            
    GibBool fltIf_3648_3762 = a_593_2651_3760 > b_594_2652_3761;
    
    if (fltIf_3648_3762) {
        return a_593_2651_3760;
    } else {
        return b_594_2652_3761;
    }
}
*/
GibInt minInt(GibInt a_601_2659_3763, GibInt b_602_2660_3764)
{
            
    GibBool fltIf_3649_3765 = a_601_2659_3763 < b_602_2660_3764;
    
    if (fltIf_3649_3765) {
        return a_601_2659_3763;
    } else {
        return b_602_2660_3764;
    }
}
GibIntGibVectorGibIntGibVectorProd lsplitAt__1446(GibInt n_747_2670_3771,
                                                  GibVector *vec_748_2671_3772)
{
            
    GibInt len_756_2666_3249_3775 = gib_vector_length(vec_748_2671_3772);
    GibInt n__757_2667_3250_3776 =  maxInt(n_747_2670_3771, 0);
    GibInt m_758_2668_3251_3777 =
            minInt(n__757_2667_3250_3776, len_756_2666_3249_3775);
    GibInt fltAppE_3652_3778 = len_756_2666_3249_3775 - n__757_2667_3250_3776;
    GibInt m__759_2669_3252_3779 =  maxInt(0, fltAppE_3652_3778);
    GibVector *fltPrd_3653_3780 = gib_vector_slice(0, m_758_2668_3251_3777,
                                                   vec_748_2671_3772);
    GibVector *fltPrd_3654_3781 = gib_vector_slice(m_758_2668_3251_3777,
                                                   m__759_2669_3252_3779,
                                                   vec_748_2671_3772);
    GibInt fltPrd_3655_3785 = gib_vector_length(fltPrd_3653_3780);
    GibInt fltPrd_3656_3786 = gib_vector_length(fltPrd_3654_3781);
    
    return (GibIntGibVectorGibIntGibVectorProd) {fltPrd_3655_3785,
                                                 fltPrd_3653_3780,
                                                 fltPrd_3656_3786,
                                                 fltPrd_3654_3781};
}
GibIntGibVectorProd length2_1427(GibVector *vec_553_2687_3788)
{
            
    GibInt fltPrd_3657_3792 = gib_vector_length(vec_553_2687_3788);
    
    return (GibIntGibVectorProd) {fltPrd_3657_3792, vec_553_2687_3788};
}
GibVector *write_loop_seq_1434(GibInt to_idx_494_2704_3799,
                               GibInt from_idx_495_2705_3800,
                               GibInt end_496_2706_3801,
                               GibVector *from_497_2707_3802,
                               GibVector *to_498_2708_3803)
{
            
    GibBool fltIf_3659_3804 = from_idx_495_2705_3800 == end_496_2706_3801;
    
    if (fltIf_3659_3804) {
        return to_498_2708_3803;
    } else {
        GibFloat *tmp_3;
        
        tmp_3 = (GibFloat *) gib_vector_nth(from_497_2707_3802,
                                            from_idx_495_2705_3800);
        
        GibFloat fltPrd_3660_3810 = *tmp_3;
        GibVector *to1_503_2712_3817 =
                  gib_vector_inplace_update(to_498_2708_3803,
                                            to_idx_494_2704_3799,
                                            &fltPrd_3660_3810);
        GibInt fltAppE_3661_3818 = to_idx_494_2704_3799 + 1;
        GibInt fltAppE_3662_3819 = from_idx_495_2705_3800 + 1;
        GibVector *tailapp_4619 =
                   write_loop_seq_1434(fltAppE_3661_3818, fltAppE_3662_3819, end_496_2706_3801, from_497_2707_3802, to1_503_2712_3817);
        
        return tailapp_4619;
    }
}
/*
GibVector *write_loop_1435(GibInt to_idx_478_2713_3820,
                           GibInt from_idx_479_2714_3821,
                           GibInt end_480_2715_3822,
                           GibVector *from_481_2716_3823,
                           GibVector *to_482_2717_3824)
{
            
    GibInt fltPrm_3664_3825 = end_480_2715_3822 - from_idx_479_2714_3821;
    GibBool fltIf_3663_3826 = fltPrm_3664_3825 < 4096;
    
    if (fltIf_3663_3826) {
        GibVector *tailapp_4620 =
                   write_loop_seq_1434(to_idx_478_2713_3820, from_idx_479_2714_3821, end_480_2715_3822, from_481_2716_3823, to_482_2717_3824);
        
        return tailapp_4620;
    } else {
        GibInt fltPrm_3665_3827 = from_idx_479_2714_3821 + end_480_2715_3822;
        GibInt mid_484_2718_3828 = fltPrm_3665_3827 / 2;
        int parent_id_4606 = __cilkrts_get_worker_number();
        GibVector *to4_491_2725_3835 =
                  cilk_spawn write_loop_1435(to_idx_478_2713_3820, from_idx_479_2714_3821, mid_484_2718_3828, from_481_2716_3823, to_482_2717_3824);
        GibInt fltPrm_3667_3836 = to_idx_478_2713_3820 + mid_484_2718_3828;
        GibInt fltAppE_3666_3837 = fltPrm_3667_3836 - from_idx_479_2714_3821;
        GibVector *to5_492_2726_3838 =
                   write_loop_1435(fltAppE_3666_3837, mid_484_2718_3828, end_480_2715_3822, from_481_2716_3823, to_482_2717_3824);
        
        cilk_sync;
        return to5_492_2726_3838;
    }
}
GibVector *copy_par_1396(GibVector *vec_875_2770_3840)
{
            
    GibInt n_885_2802_3286_3842 = gib_vector_length(vec_875_2770_3840);
    GibInt n__888_2804_3288_3844 =  maxInt(n_885_2802_3286_3842, 0);
    GibInt tmp_4 = sizeof(GibFloat);
    GibVector *vec_889_2805_3289_3845 = gib_vector_alloc(n__888_2804_3288_3844,
                                                         tmp_4);
    GibInt p_781_2662_3767_4293 = gib_get_num_processors();
    GibInt fltPrm_3651_3768_4294 = 8 * p_781_2662_3767_4293;
    GibInt fltAppE_3650_3769_4295 = n__888_2804_3288_3844 /
           fltPrm_3651_3768_4294;
    GibInt grain_782_2663_3770_4296 =  maxInt(1, fltAppE_3650_3769_4295);
    GibInt cutoff_890_2806_3290_3846 =  minInt(2048, grain_782_2663_3770_4296);
    GibVector *vec1_891_2807_3291_3847 =
               generate_par_loop_1406_2351(cutoff_890_2806_3290_3846, vec_889_2805_3289_3845, 0, n__888_2804_3288_3844, vec_875_2770_3840);
    
    return vec1_891_2807_3291_3847;
}
*/
GibVector *copy_1394(GibVector *vec_734_2775_3848)
{
            
    GibInt n_585_2818_3299_3849 = gib_vector_length(vec_734_2775_3848);
    GibInt n__588_2820_3301_3851 =  maxInt(n_585_2818_3299_3849, 0);
    GibInt tmp_5 = sizeof(GibFloat);
    GibVector *vec_589_2821_3302_3852 = gib_vector_alloc(n__588_2820_3301_3851,
                                                         tmp_5);
    GibVector *vec1_590_2822_3303_3853 =
               generate_loop_1400_2357(vec_589_2821_3302_3852, 0, n__588_2820_3301_3851, vec_734_2775_3848);
    
    return vec1_590_2822_3303_3853;
}
/*
GibVector *generate_par_loop_1406_2351(GibInt cutoff_892_2823_3857,
                                       GibVector *vec_893_2824_3858,
                                       GibInt start_894_2825_3859,
                                       GibInt end_895_2826_3860,
                                       GibVector *vec_875_2827_3861)
{
            
    GibInt fltPrm_3669_3862 = end_895_2826_3860 - start_894_2825_3859;
    GibBool fltIf_3668_3863 = fltPrm_3669_3862 <= cutoff_892_2823_3857;
    
    if (fltIf_3668_3863) {
        GibVector *tailapp_4621 =
                   generate_loop_1400_2352(vec_893_2824_3858, start_894_2825_3859, end_895_2826_3860, vec_875_2827_3861);
        
        return tailapp_4621;
    } else {
        GibInt fltPrm_3670_3864 = start_894_2825_3859 + end_895_2826_3860;
        GibInt mid_898_2828_3865 = fltPrm_3670_3864 / 2;
        int parent_id_4607 = __cilkrts_get_worker_number();
        GibVector *_vec1_899_2829_3866 =
                  cilk_spawn generate_par_loop_1406_2351(cutoff_892_2823_3857, vec_893_2824_3858, start_894_2825_3859, mid_898_2828_3865, vec_875_2827_3861);
        GibVector *vec2_900_2830_3867 =
                   generate_par_loop_1406_2351(cutoff_892_2823_3857, vec_893_2824_3858, mid_898_2828_3865, end_895_2826_3860, vec_875_2827_3861);
        
        cilk_sync;
        return vec2_900_2830_3867;
    }
}
*/

GibVector *generate_loop_1400_2352(GibVector *vec_737_2832_3869,
                                   GibInt idx_738_2833_3870,
                                   GibInt end_739_2834_3871,
                                   GibVector *vec_875_2835_3872)
{
            
    GibBool fltIf_3671_3873 = idx_738_2833_3870 == end_739_2834_3871;
    
    if (fltIf_3671_3873) {
        return vec_737_2832_3869;
    } else {
        GibFloat *tmp_6;
        
        tmp_6 = (GibFloat *) gib_vector_nth(vec_875_2835_3872,
                                            idx_738_2833_3870);
        
        GibFloat fltPrm_3672_3876 = *tmp_6;
        GibVector *vec1_742_2836_3877 =
                  gib_vector_inplace_update(vec_737_2832_3869,
                                            idx_738_2833_3870,
                                            &fltPrm_3672_3876);
        GibInt fltAppE_3673_3878 = idx_738_2833_3870 + 1;
        GibVector *tailapp_4622 =
                   generate_loop_1400_2352(vec1_742_2836_3877, fltAppE_3673_3878, end_739_2834_3871, vec_875_2835_3872);
        
        return tailapp_4622;
    }
}
GibVector *generate_loop_1400_2355(GibVector *vec_737_2855_3883,
                                   GibInt idx_738_2856_3884,
                                   GibInt end_739_2857_3885)
{
            
    GibBool fltIf_3674_3886 = idx_738_2856_3884 == end_739_2857_3885;
    
    if (fltIf_3674_3886) {
        return vec_737_2855_3883;
    } else {
        GibInt fltPrm_3676_3888 = rand();
        GibFloat fltPrm_3675_3889 = (GibFloat) fltPrm_3676_3888;
        GibVector *vec1_742_2858_3890 =
                  gib_vector_inplace_update(vec_737_2855_3883,
                                            idx_738_2856_3884,
                                            &fltPrm_3675_3889);
        GibInt fltAppE_3677_3891 = idx_738_2856_3884 + 1;
        GibVector *tailapp_4623 =
                   generate_loop_1400_2355(vec1_742_2858_3890, fltAppE_3677_3891, end_739_2857_3885);
        
        return tailapp_4623;
    }
}
GibVector *generate_loop_1400_2356(GibVector *vec_737_2863_3896,
                                   GibInt idx_738_2864_3897,
                                   GibInt end_739_2865_3898)
{
            
    GibBool fltIf_3678_3899 = idx_738_2864_3897 == end_739_2865_3898;
    
    if (fltIf_3678_3899) {
        return vec_737_2863_3896;
    } else {
        GibInt fltPrm_3680_3901 = rand();
        GibFloat fltPrm_3679_3902 = (GibFloat) fltPrm_3680_3901;
        GibVector *vec1_742_2866_3903 =
                  gib_vector_inplace_update(vec_737_2863_3896,
                                            idx_738_2864_3897,
                                            &fltPrm_3679_3902);
        GibInt fltAppE_3681_3904 = idx_738_2864_3897 + 1;
        GibVector *tailapp_4624 =
                   generate_loop_1400_2356(vec1_742_2866_3903, fltAppE_3681_3904, end_739_2865_3898);
        
        return tailapp_4624;
    }
}
GibVector *generate_loop_1400_2357(GibVector *vec_737_2867_3905,
                                   GibInt idx_738_2868_3906,
                                   GibInt end_739_2869_3907,
                                   GibVector *vec_734_2870_3908)
{
            
    GibBool fltIf_3682_3909 = idx_738_2868_3906 == end_739_2869_3907;
    
    if (fltIf_3682_3909) {
        return vec_737_2867_3905;
    } else {
        GibFloat *tmp_7;
        
        tmp_7 = (GibFloat *) gib_vector_nth(vec_734_2870_3908,
                                            idx_738_2868_3906);
        
        GibFloat fltPrm_3683_3912 = *tmp_7;
        GibVector *vec1_742_2871_3913 =
                  gib_vector_inplace_update(vec_737_2867_3905,
                                            idx_738_2868_3906,
                                            &fltPrm_3683_3912);
        GibInt fltAppE_3684_3914 = idx_738_2868_3906 + 1;
        GibVector *tailapp_4625 =
                   generate_loop_1400_2357(vec1_742_2871_3913, fltAppE_3684_3914, end_739_2869_3907, vec_734_2870_3908);
        
        return tailapp_4625;
    }
}
GibVector *writeSort1_seq_1447_2362(GibVector *src00_353_2898_3922,
                                    GibVector *tmp_354_2899_3923)
{
            
    GibInt fltPrd_3686_3928 = gib_vector_length(src00_353_2898_3922);
    GibBool fltIf_3687_3932 = fltPrd_3686_3928 <= 1;
    
    if (fltIf_3687_3932) {
        return src00_353_2898_3922;
    } else {
        GibBool fltIf_3688_3933 = fltPrd_3686_3928 <= 8192;
        
        if (fltIf_3688_3933) {
            GibVector *tailprim_4626 =
                      gib_vector_inplace_sort(src00_353_2898_3922,
                                              compare_float);
            
            return tailprim_4626;
        } else {
            GibInt n_546_2693_3348_3938 = fltPrd_3686_3928 / 2;
            GibInt len_756_2666_3249_3775_4317 =
                   gib_vector_length(src00_353_2898_3922);
            GibInt n__757_2667_3250_3776_4318 =
                    maxInt(n_546_2693_3348_3938, 0);
            GibInt m_758_2668_3251_3777_4319 =
                    minInt(n__757_2667_3250_3776_4318, len_756_2666_3249_3775_4317);
            GibInt fltAppE_3652_3778_4320 = len_756_2666_3249_3775_4317 -
                   n__757_2667_3250_3776_4318;
            GibInt m__759_2669_3252_3779_4321 =
                    maxInt(0, fltAppE_3652_3778_4320);
            GibVector *fltPrd_3653_3780_4322 = gib_vector_slice(0,
                                                                m_758_2668_3251_3777_4319,
                                                                src00_353_2898_3922);
            GibVector *fltPrd_3654_3781_4323 =
                      gib_vector_slice(m_758_2668_3251_3777_4319,
                                       m__759_2669_3252_3779_4321,
                                       src00_353_2898_3922);
            GibInt fltPrd_3655_3785_4327 =
                   gib_vector_length(fltPrd_3653_3780_4322);
            GibInt fltPrd_3656_3786_4328 =
                   gib_vector_length(fltPrd_3654_3781_4323);
            GibInt n_546_2693_3351_3946 = fltPrd_3686_3928 / 2;
            GibInt len_756_2666_3249_3775_4333 =
                   gib_vector_length(tmp_354_2899_3923);
            GibInt n__757_2667_3250_3776_4334 =
                    maxInt(n_546_2693_3351_3946, 0);
            GibInt m_758_2668_3251_3777_4335 =
                    minInt(n__757_2667_3250_3776_4334, len_756_2666_3249_3775_4333);
            GibInt fltAppE_3652_3778_4336 = len_756_2666_3249_3775_4333 -
                   n__757_2667_3250_3776_4334;
            GibInt m__759_2669_3252_3779_4337 =
                    maxInt(0, fltAppE_3652_3778_4336);
            GibVector *fltPrd_3653_3780_4338 = gib_vector_slice(0,
                                                                m_758_2668_3251_3777_4335,
                                                                tmp_354_2899_3923);
            GibVector *fltPrd_3654_3781_4339 =
                      gib_vector_slice(m_758_2668_3251_3777_4335,
                                       m__759_2669_3252_3779_4337,
                                       tmp_354_2899_3923);
            GibInt fltPrd_3655_3785_4343 =
                   gib_vector_length(fltPrd_3653_3780_4338);
            GibInt fltPrd_3656_3786_4344 =
                   gib_vector_length(fltPrd_3654_3781_4339);
            GibVector *tmp_l1_372_2916_3954 =
                       writeSort2_seq_1448_2364(fltPrd_3653_3780_4322, fltPrd_3653_3780_4338);
            GibVector *tmp_r1_373_2917_3955 =
                       writeSort2_seq_1448_2364(fltPrd_3654_3781_4323, fltPrd_3654_3781_4339);
            GibVector *tailapp_4627 =
                       writeMerge_seq_1436_2365(fltPrd_3655_3785_4343, tmp_l1_372_2916_3954, fltPrd_3656_3786_4344, tmp_r1_373_2917_3955, src00_353_2898_3922);
            
            return tailapp_4627;
        }
    }
}
GibVector *writeSort2_seq_1448_2364(GibVector *src0_306_2918_3956,
                                    GibVector *tmp0_307_2919_3957)
{
            
    GibInt fltPrd_3689_3962 = gib_vector_length(src0_306_2918_3956);
    GibBool fltIf_3690_3966 = fltPrd_3689_3962 <= 1;
    
    if (fltIf_3690_3966) {
        GibVector *tailapp_4628 =
                   write_loop_seq_1434(0, 0, 1, src0_306_2918_3956, tmp0_307_2919_3957);
        
        return tailapp_4628;
    } else {
        GibBool fltIf_3691_3967 = fltPrd_3689_3962 <= 8192;
        
        if (fltIf_3691_3967) {
            GibVector *tmp_1_312_2923_3968 =
                       write_loop_seq_1434(0, 0, fltPrd_3689_3962, src0_306_2918_3956, tmp0_307_2919_3957);
            GibVector *tailprim_4629 =
                      gib_vector_inplace_sort(tmp_1_312_2923_3968,
                                              compare_float);
            
            return tailprim_4629;
        } else {
            GibInt n_546_2693_3359_3973 = fltPrd_3689_3962 / 2;
            GibInt len_756_2666_3249_3775_4349 =
                   gib_vector_length(src0_306_2918_3956);
            GibInt n__757_2667_3250_3776_4350 =
                    maxInt(n_546_2693_3359_3973, 0);
            GibInt m_758_2668_3251_3777_4351 =
                    minInt(n__757_2667_3250_3776_4350, len_756_2666_3249_3775_4349);
            GibInt fltAppE_3652_3778_4352 = len_756_2666_3249_3775_4349 -
                   n__757_2667_3250_3776_4350;
            GibInt m__759_2669_3252_3779_4353 =
                    maxInt(0, fltAppE_3652_3778_4352);
            GibVector *fltPrd_3653_3780_4354 = gib_vector_slice(0,
                                                                m_758_2668_3251_3777_4351,
                                                                src0_306_2918_3956);
            GibVector *fltPrd_3654_3781_4355 =
                      gib_vector_slice(m_758_2668_3251_3777_4351,
                                       m__759_2669_3252_3779_4353,
                                       src0_306_2918_3956);
            GibInt fltPrd_3655_3785_4359 =
                   gib_vector_length(fltPrd_3653_3780_4354);
            GibInt fltPrd_3656_3786_4360 =
                   gib_vector_length(fltPrd_3654_3781_4355);
            GibInt n_546_2693_3362_3981 = fltPrd_3689_3962 / 2;
            GibInt len_756_2666_3249_3775_4365 =
                   gib_vector_length(tmp0_307_2919_3957);
            GibInt n__757_2667_3250_3776_4366 =
                    maxInt(n_546_2693_3362_3981, 0);
            GibInt m_758_2668_3251_3777_4367 =
                    minInt(n__757_2667_3250_3776_4366, len_756_2666_3249_3775_4365);
            GibInt fltAppE_3652_3778_4368 = len_756_2666_3249_3775_4365 -
                   n__757_2667_3250_3776_4366;
            GibInt m__759_2669_3252_3779_4369 =
                    maxInt(0, fltAppE_3652_3778_4368);
            GibVector *fltPrd_3653_3780_4370 = gib_vector_slice(0,
                                                                m_758_2668_3251_3777_4367,
                                                                tmp0_307_2919_3957);
            GibVector *fltPrd_3654_3781_4371 =
                      gib_vector_slice(m_758_2668_3251_3777_4367,
                                       m__759_2669_3252_3779_4369,
                                       tmp0_307_2919_3957);
            GibInt fltPrd_3655_3785_4375 =
                   gib_vector_length(fltPrd_3653_3780_4370);
            GibInt fltPrd_3656_3786_4376 =
                   gib_vector_length(fltPrd_3654_3781_4371);
            GibVector *src_l1_326_2937_3989 =
                       writeSort1_seq_1447_2362(fltPrd_3653_3780_4354, fltPrd_3653_3780_4370);
            GibVector *src_r1_327_2938_3990 =
                       writeSort1_seq_1447_2362(fltPrd_3654_3781_4355, fltPrd_3654_3781_4371);
            GibVector *tailapp_4630 =
                       writeMerge_seq_1436_2365(fltPrd_3655_3785_4359, src_l1_326_2937_3989, fltPrd_3656_3786_4360, src_r1_327_2938_3990, tmp0_307_2919_3957);
            
            return tailapp_4630;
        }
    }
}
GibVector *writeMerge_seq_1436_2365(GibInt n1_454_2940_3991,
                                    GibVector *src_1_455_2941_3992,
                                    GibInt n2_456_2942_3993,
                                    GibVector *src_2_457_2943_3994,
                                    GibVector *tmp_458_2944_3995)
{
            
    GibVector *tailapp_4631 =
               writeMerge_seq_loop_1442_2366(0, 0, 0, n1_454_2940_3991, n2_456_2942_3993, src_1_455_2941_3992, src_2_457_2943_3994, tmp_458_2944_3995);
    
    return tailapp_4631;
}
GibVector *writeMerge_seq_loop_1442_2366(GibInt i1_460_2945_3996,
                                         GibInt i2_461_2946_3997,
                                         GibInt j_462_2947_3998,
                                         GibInt n1_463_2948_3999,
                                         GibInt n2_464_2949_4000,
                                         GibVector *src_1_466_2950_4001,
                                         GibVector *src_2_467_2951_4002,
                                         GibVector *tmp_468_2952_4003)
{
            
    GibBool fltIf_3692_4004 = i1_460_2945_3996 == n1_463_2948_3999;
    
    if (fltIf_3692_4004) {
        GibVector *tailapp_4632 =
                   write_loop_seq_1434(j_462_2947_3998, i2_461_2946_3997, n2_464_2949_4000, src_2_467_2951_4002, tmp_468_2952_4003);
        
        return tailapp_4632;
    } else {
        GibBool fltIf_3693_4005 = i2_461_2946_3997 == n2_464_2949_4000;
        
        if (fltIf_3693_4005) {
            GibVector *tailapp_4633 =
                       write_loop_seq_1434(j_462_2947_3998, i1_460_2945_3996, n1_463_2948_3999, src_1_466_2950_4001, tmp_468_2952_4003);
            
            return tailapp_4633;
        } else {
            GibFloat *tmp_9;
            
            tmp_9 = (GibFloat *) gib_vector_nth(src_1_466_2950_4001,
                                                i1_460_2945_3996);
            
            GibFloat fltPrd_3694_4011 = *tmp_9;
            GibFloat *tmp_8;
            
            tmp_8 = (GibFloat *) gib_vector_nth(src_2_467_2951_4002,
                                                i2_461_2946_3997);
            
            GibFloat fltPrd_3695_4020 = *tmp_8;
            GibBool fltIf_3698_4026 = fltPrd_3694_4011 < fltPrd_3695_4020;
            GibInt fltPrm_3697_4028;
            
            if (fltIf_3698_4026) {
                GibInt flt_4706 = 0 - 1;
                
                fltPrm_3697_4028 = flt_4706;
            } else {
                GibBool fltIf_3699_4027 = fltPrd_3694_4011 > fltPrd_3695_4020;
                
                if (fltIf_3699_4027) {
                    fltPrm_3697_4028 = 1;
                } else {
                    fltPrm_3697_4028 = 0;
                }
            }
            
            GibBool fltIf_3696_4029 = fltPrm_3697_4028 < 0;
            
            if (fltIf_3696_4029) {
                GibVector *tmp_1_476_2959_4033 =
                          gib_vector_inplace_update(tmp_468_2952_4003,
                                                    j_462_2947_3998,
                                                    &fltPrd_3694_4011);
                GibInt fltAppE_3700_4034 = i1_460_2945_3996 + 1;
                GibInt fltAppE_3701_4035 = j_462_2947_3998 + 1;
                GibVector *tailapp_4634 =
                           writeMerge_seq_loop_1442_2366(fltAppE_3700_4034, i2_461_2946_3997, fltAppE_3701_4035, n1_463_2948_3999, n2_464_2949_4000, src_1_466_2950_4001, src_2_467_2951_4002, tmp_1_476_2959_4033);
                
                return tailapp_4634;
            } else {
                GibVector *tmp_1_477_2960_4039 =
                          gib_vector_inplace_update(tmp_468_2952_4003,
                                                    j_462_2947_3998,
                                                    &fltPrd_3695_4020);
                GibInt fltAppE_3702_4040 = i2_461_2946_3997 + 1;
                GibInt fltAppE_3703_4041 = j_462_2947_3998 + 1;
                GibVector *tailapp_4635 =
                           writeMerge_seq_loop_1442_2366(i1_460_2945_3996, fltAppE_3702_4040, fltAppE_3703_4041, n1_463_2948_3999, n2_464_2949_4000, src_1_466_2950_4001, src_2_467_2951_4002, tmp_1_477_2960_4039);
                
                return tailapp_4635;
            }
        }
    }
}
/*
GibVector *writeSort1_1429_2368(GibVector *src00_375_2966_4050,
                                GibVector *tmp_376_2967_4051)
{
            
    GibInt fltPrd_3705_4056 = gib_vector_length(src00_375_2966_4050);
    GibBool fltIf_3706_4060 = fltPrd_3705_4056 <= 1;
    
    if (fltIf_3706_4060) {
        return src00_375_2966_4050;
    } else {
        GibBool fltIf_3707_4061 = fltPrd_3705_4056 <= 8192;
        
        if (fltIf_3707_4061) {
            GibVector *tailprim_4636 =
                      gib_vector_inplace_sort(src00_375_2966_4050,
                                              compare_float);
            
            return tailprim_4636;
        } else {
            GibInt n_546_2693_3399_4066 = fltPrd_3705_4056 / 2;
            GibInt len_756_2666_3249_3775_4395 =
                   gib_vector_length(src00_375_2966_4050);
            GibInt n__757_2667_3250_3776_4396 =
                    maxInt(n_546_2693_3399_4066, 0);
            GibInt m_758_2668_3251_3777_4397 =
                    minInt(n__757_2667_3250_3776_4396, len_756_2666_3249_3775_4395);
            GibInt fltAppE_3652_3778_4398 = len_756_2666_3249_3775_4395 -
                   n__757_2667_3250_3776_4396;
            GibInt m__759_2669_3252_3779_4399 =
                    maxInt(0, fltAppE_3652_3778_4398);
            GibVector *fltPrd_3653_3780_4400 = gib_vector_slice(0,
                                                                m_758_2668_3251_3777_4397,
                                                                src00_375_2966_4050);
            GibVector *fltPrd_3654_3781_4401 =
                      gib_vector_slice(m_758_2668_3251_3777_4397,
                                       m__759_2669_3252_3779_4399,
                                       src00_375_2966_4050);
            GibInt fltPrd_3655_3785_4405 =
                   gib_vector_length(fltPrd_3653_3780_4400);
            GibInt fltPrd_3656_3786_4406 =
                   gib_vector_length(fltPrd_3654_3781_4401);
            GibInt n_546_2693_3402_4074 = fltPrd_3705_4056 / 2;
            GibInt len_756_2666_3249_3775_4411 =
                   gib_vector_length(tmp_376_2967_4051);
            GibInt n__757_2667_3250_3776_4412 =
                    maxInt(n_546_2693_3402_4074, 0);
            GibInt m_758_2668_3251_3777_4413 =
                    minInt(n__757_2667_3250_3776_4412, len_756_2666_3249_3775_4411);
            GibInt fltAppE_3652_3778_4414 = len_756_2666_3249_3775_4411 -
                   n__757_2667_3250_3776_4412;
            GibInt m__759_2669_3252_3779_4415 =
                    maxInt(0, fltAppE_3652_3778_4414);
            GibVector *fltPrd_3653_3780_4416 = gib_vector_slice(0,
                                                                m_758_2668_3251_3777_4413,
                                                                tmp_376_2967_4051);
            GibVector *fltPrd_3654_3781_4417 =
                      gib_vector_slice(m_758_2668_3251_3777_4413,
                                       m__759_2669_3252_3779_4415,
                                       tmp_376_2967_4051);
            GibInt fltPrd_3655_3785_4421 =
                   gib_vector_length(fltPrd_3653_3780_4416);
            GibInt fltPrd_3656_3786_4422 =
                   gib_vector_length(fltPrd_3654_3781_4417);
            int parent_id_4608 = __cilkrts_get_worker_number();
            GibVector *tmp_l1_394_2984_4082 =
                      cilk_spawn writeSort2_1432_2369(fltPrd_3653_3780_4400, fltPrd_3653_3780_4416);
            GibVector *tmp_r1_395_2985_4083 =
                       writeSort2_1432_2369(fltPrd_3654_3781_4401, fltPrd_3654_3781_4417);
            
            cilk_sync;
            
            GibVector *tailapp_4637 =
                       writeMerge_1433_2370(fltPrd_3655_3785_4421, tmp_l1_394_2984_4082, fltPrd_3656_3786_4422, tmp_r1_395_2985_4083, src00_375_2966_4050);
            
            return tailapp_4637;
        }
    }
}
*/
/*
GibVector *writeMerge_1433_2370(GibInt n1_447_2987_4085,
                                GibVector *src_10_448_2988_4086,
                                GibInt n2_449_2989_4087,
                                GibVector *src_20_450_2990_4088,
                                GibVector *tmp0_451_2991_4089)
{
            
    GibInt fltPrm_3710_4090 = n1_447_2987_4085 + n2_449_2989_4087;
    GibBool fltPrm_3709_4091 = fltPrm_3710_4090 <= 4096;
    GibBool fltPrm_3712_4092 = n1_447_2987_4085 == 0;
    GibBool fltPrm_3713_4093 = n2_449_2989_4087 == 0;
    GibBool fltPrm_3711_4094 = fltPrm_3712_4092 || fltPrm_3713_4093;
    GibBool fltIf_3708_4095 = fltPrm_3709_4091 || fltPrm_3711_4094;
    
    if (fltIf_3708_4095) {
        GibVector *tailapp_4638 =
                   writeMerge_seq_1436_2365(n1_447_2987_4085, src_10_448_2988_4086, n2_449_2989_4087, src_20_450_2990_4088, tmp0_451_2991_4089);
        
        return tailapp_4638;
    } else {
        GibBool fltIf_3714_4096 = n1_447_2987_4085 == 0;
        
        if (fltIf_3714_4096) {
            GibVector *tailapp_4639 =
                       write_loop_1435(0, 0, n2_449_2989_4087, src_20_450_2990_4088, tmp0_451_2991_4089);
            
            return tailapp_4639;
        } else {
            GibBool fltIf_3715_4097 = n2_449_2989_4087 == 0;
            
            if (fltIf_3715_4097) {
                GibVector *tailapp_4640 =
                           write_loop_1435(0, 0, n1_447_2987_4085, src_10_448_2988_4086, tmp0_451_2991_4089);
                
                return tailapp_4640;
            } else {
                GibInt mid1_435_2992_3405_4098 = n1_447_2987_4085 / 2;
                GibFloat *tmp_16;
                
                tmp_16 = (GibFloat *) gib_vector_nth(src_10_448_2988_4086,
                                                     mid1_435_2992_3405_4098);
                
                GibFloat fltPrd_3658_3798_4428 = *tmp_16;
                GibIntGibVectorProd tmp_struct_10 =
                                     binarySearch_1439_2372(src_20_450_2990_4088, fltPrd_3658_3798_4428);
                GibInt pvrtmp_4723 = tmp_struct_10.field0;
                GibVector *pvrtmp_4724 = tmp_struct_10.field1;
                GibIntGibVectorGibIntGibVectorProd tmp_struct_11 =
                                                    lsplitAt__1446(mid1_435_2992_3405_4098, src_10_448_2988_4086);
                GibInt pvrtmp_4725 = tmp_struct_11.field0;
                GibVector *pvrtmp_4726 = tmp_struct_11.field1;
                GibInt pvrtmp_4727 = tmp_struct_11.field2;
                GibVector *pvrtmp_4728 = tmp_struct_11.field3;
                GibIntGibVectorGibIntGibVectorProd tmp_struct_12 =
                                                    lsplitAt__1446(1, pvrtmp_4728);
                GibInt pvrtmp_4729 = tmp_struct_12.field0;
                GibVector *pvrtmp_4730 = tmp_struct_12.field1;
                GibInt pvrtmp_4731 = tmp_struct_12.field2;
                GibVector *pvrtmp_4732 = tmp_struct_12.field3;
                GibIntGibVectorGibIntGibVectorProd tmp_struct_13 =
                                                    lsplitAt__1446(pvrtmp_4723, pvrtmp_4724);
                GibInt pvrtmp_4733 = tmp_struct_13.field0;
                GibVector *pvrtmp_4734 = tmp_struct_13.field1;
                GibInt pvrtmp_4735 = tmp_struct_13.field2;
                GibVector *pvrtmp_4736 = tmp_struct_13.field3;
                GibInt n_546_2693_3476_4179_4459 = mid1_435_2992_3405_4098 +
                       pvrtmp_4723;
                GibIntGibVectorGibIntGibVectorProd tmp_struct_14 =
                                                    lsplitAt__1446(n_546_2693_3476_4179_4459, tmp0_451_2991_4089);
                GibInt pvrtmp_4737 = tmp_struct_14.field0;
                GibVector *pvrtmp_4738 = tmp_struct_14.field1;
                GibInt pvrtmp_4739 = tmp_struct_14.field2;
                GibVector *pvrtmp_4740 = tmp_struct_14.field3;
                GibIntGibVectorGibIntGibVectorProd tmp_struct_15 =
                                                    lsplitAt__1446(1, pvrtmp_4740);
                GibInt pvrtmp_4741 = tmp_struct_15.field0;
                GibVector *pvrtmp_4742 = tmp_struct_15.field1;
                GibInt pvrtmp_4743 = tmp_struct_15.field2;
                GibVector *pvrtmp_4744 = tmp_struct_15.field3;
                GibVector *tmp_one__430_3046_4195_4475 =
                           write_loop_seq_1434(0, 0, 1, pvrtmp_4730, pvrtmp_4742);
                int parent_id_4609 = __cilkrts_get_worker_number();
                GibVector *tmp_l1_431_3047_4196_4476 =
                          cilk_spawn writeMerge_1433_2370(pvrtmp_4725, pvrtmp_4726, pvrtmp_4733, pvrtmp_4734, pvrtmp_4738);
                GibVector *tmp_r1_432_3048_4197_4477 =
                           writeMerge_1433_2370(pvrtmp_4731, pvrtmp_4732, pvrtmp_4735, pvrtmp_4736, pvrtmp_4744);
                
                cilk_sync;
                
                GibVector *vec1_550_2691_3484_4201_4481 =
                          gib_vector_merge(tmp_l1_431_3047_4196_4476,
                                           tmp_one__430_3046_4195_4475);
                GibVector *tailprim_4641 =
                          gib_vector_merge(vec1_550_2691_3484_4201_4481,
                                           tmp_r1_432_3048_4197_4477);
                
                return tailprim_4641;
            }
        }
    }
}
*/
GibIntGibVectorProd binarySearch_1439_2372(GibVector *vec_505_3002_4108,
                                           GibFloat query_506_3003_4109)
{
            
    GibInt fltAppE_3717_4113 = gib_vector_length(vec_505_3002_4108);
    GibInt fltPrd_3716_4114 =
            binarySearch__1445_2375(0, fltAppE_3717_4113, vec_505_3002_4108, query_506_3003_4109);
    
    return (GibIntGibVectorProd) {fltPrd_3716_4114, vec_505_3002_4108};
}
GibInt binarySearch__1445_2375(GibInt lo_513_3007_4115, GibInt hi_514_3008_4116,
                               GibVector *vec_516_3009_4117,
                               GibFloat query_517_3010_4118)
{
            
    GibInt n_519_3011_4119 = hi_514_3008_4116 - lo_513_3007_4115;
    GibBool fltIf_3718_4120 = n_519_3011_4119 == 0;
    
    if (fltIf_3718_4120) {
        return lo_513_3007_4115;
    } else {
        GibInt fltPrm_3719_4122 = n_519_3011_4119 / 2;
        GibInt i_535_2700_3459_4123 = lo_513_3007_4115 + fltPrm_3719_4122;
        GibFloat *tmp_17;
        
        tmp_17 = (GibFloat *) gib_vector_nth(vec_516_3009_4117,
                                             i_535_2700_3459_4123);
        
        GibFloat fltPrd_3720_4127 = *tmp_17;
        GibBool fltIf_3723_4133 = query_517_3010_4118 < fltPrd_3720_4127;
        GibInt fltPrm_3722_4135;
        
        if (fltIf_3723_4133) {
            GibInt flt_4749 = 0 - 1;
            
            fltPrm_3722_4135 = flt_4749;
        } else {
            GibBool fltIf_3724_4134 = query_517_3010_4118 > fltPrd_3720_4127;
            
            if (fltIf_3724_4134) {
                fltPrm_3722_4135 = 1;
            } else {
                fltPrm_3722_4135 = 0;
            }
        }
        
        GibBool fltIf_3721_4136 = fltPrm_3722_4135 < 0;
        
        if (fltIf_3721_4136) {
            GibInt fltPrm_3726_4137 = n_519_3011_4119 / 2;
            GibInt fltAppE_3725_4138 = lo_513_3007_4115 + fltPrm_3726_4137;
            GibInt tailapp_4643 =
                    binarySearch__1445_2375(lo_513_3007_4115, fltAppE_3725_4138, vec_516_3009_4117, query_517_3010_4118);
            
            return tailapp_4643;
        } else {
            GibBool fltIf_3729_4141 = query_517_3010_4118 < fltPrd_3720_4127;
            GibInt fltPrm_3728_4143;
            
            if (fltIf_3729_4141) {
                GibInt flt_4750 = 0 - 1;
                
                fltPrm_3728_4143 = flt_4750;
            } else {
                GibBool fltIf_3730_4142 = query_517_3010_4118 >
                        fltPrd_3720_4127;
                
                if (fltIf_3730_4142) {
                    fltPrm_3728_4143 = 1;
                } else {
                    fltPrm_3728_4143 = 0;
                }
            }
            
            GibBool fltIf_3727_4144 = fltPrm_3728_4143 > 0;
            
            if (fltIf_3727_4144) {
                GibInt fltPrm_3733_4145 = n_519_3011_4119 / 2;
                GibInt fltPrm_3732_4146 = lo_513_3007_4115 + fltPrm_3733_4145;
                GibInt fltAppE_3731_4147 = fltPrm_3732_4146 + 1;
                GibInt tailapp_4644 =
                        binarySearch__1445_2375(fltAppE_3731_4147, hi_514_3008_4116, vec_516_3009_4117, query_517_3010_4118);
                
                return tailapp_4644;
            } else {
                GibInt fltPrm_3734_4148 = n_519_3011_4119 / 2;
                GibInt tailprim_4645 = lo_513_3007_4115 + fltPrm_3734_4148;
                
                return tailprim_4645;
            }
        }
    }
}
/*
GibVector *writeSort2_1432_2369(GibVector *src0_329_3050_4203,
                                GibVector *tmp0_330_3051_4204)
{
            
    GibInt fltPrd_3735_4209 = gib_vector_length(src0_329_3050_4203);
    GibBool fltIf_3736_4213 = fltPrd_3735_4209 <= 1;
    
    if (fltIf_3736_4213) {
        GibVector *tailapp_4646 =
                   write_loop_seq_1434(0, 0, 1, src0_329_3050_4203, tmp0_330_3051_4204);
        
        return tailapp_4646;
    } else {
        GibBool fltIf_3737_4214 = fltPrd_3735_4209 <= 8192;
        
        if (fltIf_3737_4214) {
            GibVector *tmp_1_335_3055_4215 =
                       write_loop_1435(0, 0, fltPrd_3735_4209, src0_329_3050_4203, tmp0_330_3051_4204);
            GibVector *tailprim_4647 =
                      gib_vector_inplace_sort(tmp_1_335_3055_4215,
                                              compare_float);
            
            return tailprim_4647;
        } else {
            GibInt n_546_2693_3491_4220 = fltPrd_3735_4209 / 2;
            GibInt len_756_2666_3249_3775_4568 =
                   gib_vector_length(src0_329_3050_4203);
            GibInt n__757_2667_3250_3776_4569 =
                    maxInt(n_546_2693_3491_4220, 0);
            GibInt m_758_2668_3251_3777_4570 =
                    minInt(n__757_2667_3250_3776_4569, len_756_2666_3249_3775_4568);
            GibInt fltAppE_3652_3778_4571 = len_756_2666_3249_3775_4568 -
                   n__757_2667_3250_3776_4569;
            GibInt m__759_2669_3252_3779_4572 =
                    maxInt(0, fltAppE_3652_3778_4571);
            GibVector *fltPrd_3653_3780_4573 = gib_vector_slice(0,
                                                                m_758_2668_3251_3777_4570,
                                                                src0_329_3050_4203);
            GibVector *fltPrd_3654_3781_4574 =
                      gib_vector_slice(m_758_2668_3251_3777_4570,
                                       m__759_2669_3252_3779_4572,
                                       src0_329_3050_4203);
            GibInt fltPrd_3655_3785_4578 =
                   gib_vector_length(fltPrd_3653_3780_4573);
            GibInt fltPrd_3656_3786_4579 =
                   gib_vector_length(fltPrd_3654_3781_4574);
            GibInt n_546_2693_3494_4228 = fltPrd_3735_4209 / 2;
            GibInt len_756_2666_3249_3775_4584 =
                   gib_vector_length(tmp0_330_3051_4204);
            GibInt n__757_2667_3250_3776_4585 =
                    maxInt(n_546_2693_3494_4228, 0);
            GibInt m_758_2668_3251_3777_4586 =
                    minInt(n__757_2667_3250_3776_4585, len_756_2666_3249_3775_4584);
            GibInt fltAppE_3652_3778_4587 = len_756_2666_3249_3775_4584 -
                   n__757_2667_3250_3776_4585;
            GibInt m__759_2669_3252_3779_4588 =
                    maxInt(0, fltAppE_3652_3778_4587);
            GibVector *fltPrd_3653_3780_4589 = gib_vector_slice(0,
                                                                m_758_2668_3251_3777_4586,
                                                                tmp0_330_3051_4204);
            GibVector *fltPrd_3654_3781_4590 =
                      gib_vector_slice(m_758_2668_3251_3777_4586,
                                       m__759_2669_3252_3779_4588,
                                       tmp0_330_3051_4204);
            GibInt fltPrd_3655_3785_4594 =
                   gib_vector_length(fltPrd_3653_3780_4589);
            GibInt fltPrd_3656_3786_4595 =
                   gib_vector_length(fltPrd_3654_3781_4590);
            int parent_id_4610 = __cilkrts_get_worker_number();
            GibVector *src_l1_349_3069_4236 =
                      cilk_spawn writeSort1_1429_2368(fltPrd_3653_3780_4573, fltPrd_3653_3780_4589);
            GibVector *src_r1_350_3070_4237 =
                       writeSort1_1429_2368(fltPrd_3654_3781_4574, fltPrd_3654_3781_4590);
            
            cilk_sync;
            
            GibVector *tailapp_4648 =
                       writeMerge_1433_2370(fltPrd_3655_3785_4578, src_l1_349_3069_4236, fltPrd_3656_3786_4579, src_r1_350_3070_4237, tmp0_330_3051_4204);
            
            return tailapp_4648;
        }
    }
}
*/
unsigned char check_sorted_1377_2334(GibVector *sorted_278_3213_4239)
{
            
    GibInt len_280_3214_4241 = gib_vector_length(sorted_278_3213_4239);
    GibBool fltIf_3738_4242 = len_280_3214_4241 <= 1;
    
    if (fltIf_3738_4242) {
        unsigned char tailapp_4649 =  print_check(true);
        
        return tailapp_4649;
    } else {
        GibInt n_580_2777_3635_4245 = len_280_3214_4241 - 2;
        GibVector *arr1_281_3215_4247 = gib_vector_slice(0,
                                                         n_580_2777_3635_4245,
                                                         sorted_278_3213_4239);
        GibInt fltAppE_3740_4251 = gib_vector_length(arr1_281_3215_4247);
        GibBool check_286_3216_4252 =
                 ifoldl_loop_1398_2390(0, fltAppE_3740_4251, true, arr1_281_3215_4247, arr1_281_3215_4247);
        unsigned char tailapp_4650 =  print_check(check_286_3216_4252);
        
        return tailapp_4650;
    }
}
GibBool ifoldl_loop_1398_2390(GibInt idx_660_3217_4253,
                              GibInt end_661_3218_4254,
                              GibBool acc_663_3219_4255,
                              GibVector *vec_664_3220_4256,
                              GibVector *arr1_281_3221_4257)
{
    
        
    GibBool fltIf_3741_4258 = idx_660_3217_4253 == end_661_3218_4254;
    
    if (fltIf_3741_4258) {
        return acc_663_3219_4255;
    } else {
        GibFloat *tmp_19;
        
        tmp_19 = (GibFloat *) gib_vector_nth(vec_664_3220_4256,
                                             idx_660_3217_4253);
        
        GibFloat elt1_282_3207_3642_4261 = *tmp_19;
        GibInt fltAppE_3742_4263 = idx_660_3217_4253 + 1;
        GibFloat *tmp_18;
        
        tmp_18 = (GibFloat *) gib_vector_nth(arr1_281_3221_4257,
                                             fltAppE_3742_4263);
        
        GibFloat elt2_285_3209_3644_4264 = *tmp_18;
        GibBool fltIf_3646_3758_4600 = elt1_282_3207_3642_4261 <
                elt2_285_3209_3644_4264;
        GibInt fltPrm_3744_4265;
        
        if (fltIf_3646_3758_4600) {
            GibInt flt_4765 = 0 - 1;
            
            fltPrm_3744_4265 = flt_4765;
        } else {
            GibBool fltIf_3647_3759_4601 = elt1_282_3207_3642_4261 >
                    elt2_285_3209_3644_4264;
            
            if (fltIf_3647_3759_4601) {
                fltPrm_3744_4265 = 1;
            } else {
                fltPrm_3744_4265 = 0;
            }
        }
        
        GibBool fltPrm_3743_4266 = fltPrm_3744_4265 <= 0;
        GibBool acc1_667_3222_4267 = acc_663_3219_4255 && fltPrm_3743_4266;
        GibInt fltAppE_3745_4268 = idx_660_3217_4253 + 1;
        GibBool tailapp_4651 =
                 ifoldl_loop_1398_2390(fltAppE_3745_4268, end_661_3218_4254, acc1_667_3222_4267, vec_664_3220_4256, arr1_281_3221_4257);
        
        return tailapp_4651;
    }
}

int bench_gibbon_mergesort(int argc, char** argv)
{
    char *algo = argv[1];
    char *elt_type = argv[2];
    uint32_t N = atoi(argv[3]);
    // int rounds = atol(argv[4]);

    // Sorting params.
    size_t elt_size = sizeof(GibInt);
    GibVector *vec = gib_vector_alloc(N, elt_size);
    GibFloat elt;
    GibFloat a = 1000000.0;
    for (GibInt i = 0; i <= N-1; i++) {
        // https://stackoverflow.com/a/13409133.
        elt = (float)rand()/(float)(RAND_MAX/a);        
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
                // vec2 = isort2_445_629(vec);
                GibVector *src_300_2894_3334_3917_4275 =
                        copy_1394(vec);
                GibIntGibVectorProd tmp_struct_20 =
                        length2_1427(src_300_2894_3334_3917_4275);
                GibInt pvrtmp_4660 = tmp_struct_20.field0;
                GibVector *pvrtmp_4661 = tmp_struct_20.field1;
                GibInt tmp_2 = sizeof(GibFloat);
                GibVector *fltAppE_3685_3921_4279 =  gib_vector_alloc(pvrtmp_4660, tmp_2);
                GibVector *tailapp_4652 =
                        writeSort1_seq_1447_2362(pvrtmp_4661, fltAppE_3685_3921_4279);
                vec2 = tailapp_4652;
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
/*
int gib_main_expr(void)
{
    {
        GibInt n_261_2630_3223_3747 = gib_get_size_param();
        GibInt n__588_2852_3880_4270 =  maxInt(n_261_2630_3223_3747, 0);
        GibInt tmp_26 = sizeof(GibFloat);
        GibVector *vec_589_2853_3881_4271 =
                  gib_vector_alloc(n__588_2852_3880_4270, tmp_26);
        GibVector *vec1_590_2854_3882_4272 =
                   generate_loop_1400_2355(vec_589_2853_3881_4271, 0, n__588_2852_3880_4270);
        GibVector *timed_4656;
        GibVector *times_24 = gib_vector_alloc(gib_get_iters_param(),
                                               sizeof(double));
        struct timespec begin_timed_4656;
        struct timespec end_timed_4656;
        
        for (long long iters_timed_4656 = 0; iters_timed_4656 <
             gib_get_iters_param(); iters_timed_4656++) {
            if (iters_timed_4656 != gib_get_iters_param() - 1)
                gib_list_bumpalloc_save_state();
            clock_gettime(CLOCK_MONOTONIC_RAW, &begin_timed_4656);
            
            GibVector *src_300_2894_3334_3917_4275 =
                       copy_1394(vec1_590_2854_3882_4272);
            GibIntGibVectorProd tmp_struct_20 =
                                 length2_1427(src_300_2894_3334_3917_4275);
            GibInt pvrtmp_4660 = tmp_struct_20.field0;
            GibVector *pvrtmp_4661 = tmp_struct_20.field1;
            GibVector *fltAppE_3685_3921_4279 =  alloc_1428(pvrtmp_4660);
            GibVector *tailapp_4652 =
                       writeSort1_seq_1447_2362(pvrtmp_4661, fltAppE_3685_3921_4279);
            
            timed_4656 = tailapp_4652;
            clock_gettime(CLOCK_MONOTONIC_RAW, &end_timed_4656);
            if (iters_timed_4656 != gib_get_iters_param() - 1)
                gib_list_bumpalloc_restore_state();
            
            double itertime_21 = gib_difftimespecs(&begin_timed_4656,
                                                   &end_timed_4656);
            
            printf("itertime: %lf\n", itertime_21);
            gib_vector_inplace_update(times_24, iters_timed_4656, &itertime_21);
        }
        gib_vector_inplace_sort(times_24, gib_compare_doubles);
        
        double *tmp_25 = (double *) gib_vector_nth(times_24,
                                                   gib_get_iters_param() / 2);
        double selftimed_23 = *tmp_25;
        double batchtime_22 = gib_sum_timing_array(times_24);
        
        gib_print_timing_array(times_24);
        gib_vector_free(times_24);
        printf("ITERS: %ld\n", gib_get_iters_param());
        printf("SIZE: %ld\n", gib_get_size_param());
        printf("BATCHTIME: %e\n", batchtime_22);
        printf("SELFTIMED: %e\n", selftimed_23);
        
        // unsigned char tailapp_4653 =  check_sorted_1377_2334(timed_4656);
        
        printf("'#()");
        printf("\n");
        return 0;
    }
}
*/
