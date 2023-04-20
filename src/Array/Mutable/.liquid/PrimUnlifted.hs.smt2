(set-option :auto-config false)
(set-option :model true)

(set-option :smt.mbqi false)

(define-sort Str () Int)
(declare-fun strLen (Str) Int)
(declare-fun subString (Str Int Int) Str)
(declare-fun concatString (Str Str) Str)
(define-sort Elt () Int)
(define-sort LSet () (Array Elt Bool))
(define-fun smt_set_emp () LSet ((as const LSet) false))
(define-fun smt_set_sng ((x Elt)) LSet (store ((as const LSet) false) x true))
(define-fun smt_set_mem ((x Elt) (s LSet)) Bool (select s x))
(define-fun smt_set_add ((s LSet) (x Elt)) LSet (store s x true))
(define-fun smt_set_cup ((s1 LSet) (s2 LSet)) LSet ((_ map or) s1 s2))
(define-fun smt_set_cap ((s1 LSet) (s2 LSet)) LSet ((_ map and) s1 s2))
(define-fun smt_set_com ((s LSet)) LSet ((_ map not) s))
(define-fun smt_set_dif ((s1 LSet) (s2 LSet)) LSet (smt_set_cap s1 (smt_set_com s2)))
(define-fun smt_set_sub ((s1 LSet) (s2 LSet)) Bool (= smt_set_emp (smt_set_dif s1 s2)))
(define-sort Map () (Array Elt Elt))
(define-fun smt_map_sel ((m Map) (k Elt)) Elt (select m k))
(define-fun smt_map_sto ((m Map) (k Elt) (v Elt)) Map (store m k v))
(define-fun smt_map_cup ((m1 Map) (m2 Map)) Map ((_ map (+ (Elt Elt) Elt)) m1 m2))
(define-fun smt_map_prj ((s LSet) (m Map)) Map ((_ map (ite (Bool Elt Elt) Elt)) s m ((as const (Array Elt Elt)) 0)))
(define-fun smt_map_to_set ((m Map)) LSet ((_ map (> (Elt Elt) Bool)) m ((as const (Array Elt Elt)) 0)))
(define-fun smt_map_max ((m1 Map) (m2 Map)) Map (lambda ((i Int)) (ite (> (select m1 i) (select m2 i)) (select m1 i) (select m2 i))))
(define-fun smt_map_min ((m1 Map) (m2 Map)) Map (lambda ((i Int)) (ite (< (select m1 i) (select m2 i)) (select m1 i) (select m2 i))))
(define-fun smt_map_shift ((n Int) (m Map)) Map (lambda ((i Int)) (select m (- i n))))
(define-fun smt_map_def ((v Elt)) Map ((as const (Map)) v))
(define-fun bool_to_int ((b Bool)) Int (ite b 1 0))
(define-fun Z3_OP_MUL ((x Int) (y Int)) Int (* x y))
(define-fun Z3_OP_DIV ((x Int) (y Int)) Int (div x y))
(declare-fun papp7 () Int)
(declare-fun GHC.Base.id () Int)
(declare-fun n$35$$35$a1R4 () Int)
(declare-fun lq_tmp$36$x$35$$35$1498 () Int)
(declare-fun GHC.Types.KindRepTypeLitS () Int)
(declare-fun totalityError () Int)
(declare-fun GHC.Types.$91$$93$ () Int)
(declare-fun lq_tmp$36$x$35$$35$1790 () Int)
(declare-fun Array.Mutable.PrimUnlifted.set$35$ () Int)
(declare-fun GHC.Types.Word32Rep () Int)
(declare-fun lq_tmp$36$x$35$$35$1789 () Int)
(declare-fun GHC.Real.divMod () Int)
(declare-fun GHC.Prim.$62$$61$$35$ () Int)
(declare-fun GHC.List.reverse () Int)
(declare-fun lq_tmp$36$x$35$$35$1592 () Int)
(declare-fun GHC.Prim.$40$$35$$44$$44$$44$$44$$44$$44$$44$$35$$41$ () Int)
(declare-fun ds_d3Gf () Int)
(declare-fun lq_tmp$36$x$35$$35$1030 () Int)
(declare-fun lq_tmp$36$x$35$$35$1029 () Int)
(declare-fun lq_tmp$36$x$35$$35$1784 () Int)
(declare-fun GHC.List.scanl () Int)
(declare-fun GHC.Classes.min () Int)
(declare-fun GHC.Types.C$35$ () Int)
(declare-fun GHC.Real.$47$ () Int)
(declare-fun lq_tmp$36$x$35$$35$744 () Int)
(declare-fun Array.Mutable.PrimUnlifted.make$35$ () Int)
(declare-fun Array.Mutable.PrimUnlifted.size$35$ () Int)
(declare-fun GHC.Types.$58$ () Int)
(declare-fun lq_tmp$36$x$35$$35$1783 () Int)
(declare-fun tail () Int)
(declare-fun Array.Mutable.PrimUnlifted.copy$35$ () Int)
(declare-fun lq_tmp$36$x$35$$35$743 () Int)
(declare-fun isJust () Int)
(declare-fun GHC.Types.Word8Rep () Int)
(declare-fun GHC.Real.div () Int)
(declare-fun elt$35$$35$a1QJ () Int)
(declare-fun GHC.Classes.$62$$61$ () Int)
(declare-fun GHC.List.span () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792807772$35$$35$d3GA () Int)
(declare-fun arr$35$$35$a1QM () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792807828$35$$35$d3Hu () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792807820$35$$35$d3Hm () Int)
(declare-fun GHC.Prim.$42$$35$ () Int)
(declare-fun GHC.Tuple.$40$$44$$41$ () Int)
(declare-fun GHC.Real.$94$ () Int)
(declare-fun GHC.Classes.$61$$61$ () Int)
(declare-fun GHC.Prim.getSizeofMutableByteArray$35$ () Int)
(declare-fun GHC.List.$33$$33$ () Int)
(declare-fun GHC.Base.$36$ () Int)
(declare-fun GHC.List.last () Int)
(declare-fun Data.Primitive.Types.sizeOf$35$ () Int)
(declare-fun GHC.List.zipWith () Int)
(declare-fun papp5 () Int)
(declare-fun lq_tmp$36$x$35$$35$2127 () Int)
(declare-fun GHC.Types.Word16Rep () Int)
(declare-fun snd () Int)
(declare-fun ds_d3Gm () Int)
(declare-fun lq_tmp$36$x$35$$35$1778 () Int)
(declare-fun GHC.Base.$43$$43$ () Int)
(declare-fun GHC.Maybe.Just () Int)
(declare-fun x_Tuple22 () Int)
(declare-fun i$35$$35$a1QU () Int)
(declare-fun fix$36$$36$dPrim_a1Uu () Int)
(declare-fun lq_tmp$36$x$35$$35$1278 () Int)
(declare-fun GHC.Real.fromIntegral () Int)
(declare-fun GHC.IO.Exception.IOError () Int)
(declare-fun Data.Primitive.Types.writeByteArray$35$ () Int)
(declare-fun GHC.List.tail () Int)
(declare-fun GHC.Prim.$45$$35$ () Int)
(declare-fun lq_tmp$36$x$35$$35$1591 () Int)
(declare-fun lit$36$Array$35$ () Str)
(declare-fun lq_tmp$36$x$35$$35$823 () Int)
(declare-fun GHC.Types.Module () Int)
(declare-fun GHC.Stack.Types.FreezeCallStack () Int)
(declare-fun lq_tmp$36$x$35$$35$1500 () Int)
(declare-fun lq_tmp$36$x$35$$35$1588 () Int)
(declare-fun lq_tmp$36$x$35$$35$1793 () Int)
(declare-fun GHC.Types.TrNameD () Int)
(declare-fun GHC.Types.Word64Rep () Int)
(declare-fun GHC.Types.TyCon () Int)
(declare-fun lq_tmp$36$x$35$$35$1776 () Int)
(declare-fun fromJust () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792807809$35$$35$d3Hb () Int)
(declare-fun GHC.Types.UnliftedRep () Int)
(declare-fun Array.Mutable.PrimUnlifted.fill$35$ () Int)
(declare-fun GHC.Prim.$62$$35$ () Int)
(declare-fun lit$36$lh$45$array$45$sort$45$0.1.0.0$45$inplace () Str)
(declare-fun ds_d3Gc () Int)
(declare-fun lq_tmp$36$x$35$$35$1781 () Int)
(declare-fun fix$36$$36$dPrim_a1UF () Int)
(declare-fun Data.Foldable.length () Int)
(declare-fun GHC.Types.IntRep () Int)
(declare-fun GHC.Prim.$43$$35$ () Int)
(declare-fun GHC.Prim.$40$$35$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$35$$41$ () Int)
(declare-fun GHC.Prim.$40$$35$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$35$$41$ () Int)
(declare-fun GHC.Types.DoubleRep () Int)
(declare-fun elt$35$$35$a1QO () Int)
(declare-fun GHC.Classes.not () Int)
(declare-fun GHC.List.iterate () Int)
(declare-fun a$35$$35$a1QY () Int)
(declare-fun GHC.Types.Int8Rep () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792807854$35$$35$d3HU () Int)
(declare-fun addrLen () Int)
(declare-fun GHC.Real.$36$W$58$$37$ () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792807791$35$$35$d3GT () Int)
(declare-fun GHC.List.splitAt () Int)
(declare-fun GHC.Types.KindRepFun () Int)
(declare-fun GHC.Types.WordRep () Int)
(declare-fun papp3 () Int)
(declare-fun GHC.List.scanl1 () Int)
(declare-fun GHC.Real.toInteger () Int)
(declare-fun Data.Foldable.null () Int)
(declare-fun fix$36$$36$dPrim_a1Tn () Int)
(declare-fun lq_tmp$36$x$35$$35$1828 () Int)
(declare-fun fix$36$$36$krep_a1V1 () Int)
(declare-fun GHC.Classes.$38$$38$ () Int)
(declare-fun GHC.Classes.$124$$124$ () Int)
(declare-fun GHC.List.dropWhile () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792807824$35$$35$d3Hq () Int)
(declare-fun lq_tmp$36$x$35$$35$1794 () Int)
(declare-fun lq_tmp$36$x$35$$35$2037 () Int)
(declare-fun GHC.Enum.C$58$Bounded () Int)
(declare-fun GHC.List.init () Int)
(declare-fun GHC.List.scanr1 () Int)
(declare-fun GHC.Types.True () Bool)
(declare-fun GHC.CString.unpackCString$35$ () Int)
(declare-fun lq_tmp$36$x$35$$35$748 () Int)
(declare-fun lq_tmp$36$x$35$$35$1791 () Int)
(declare-fun GHC.List.break () Int)
(declare-fun ds_d3Gj () Int)
(declare-fun lq_tmp$36$x$35$$35$1788 () Int)
(declare-fun GHC.Prim.$40$$35$$44$$44$$44$$35$$41$ () Int)
(declare-fun GHC.Types.$36$WKindRepVar () Int)
(declare-fun GHC.Stack.Types.EmptyCallStack () Int)
(declare-fun x_Tuple33 () Int)
(declare-fun lq_tmp$36$x$35$$35$747 () Int)
(declare-fun Data.Either.Right () Int)
(declare-fun lq_tmp$36$x$35$$35$1330 () Int)
(declare-fun dst_offset$35$$35$a1R3 () Int)
(declare-fun lq_tmp$36$x$35$$35$1787 () Int)
(declare-fun lq_tmp$36$x$35$$35$2226 () Int)
(declare-fun i$35$$35$a1QX () Int)
(declare-fun cast_as () Int)
(declare-fun GHC.Types.KindRepApp () Int)
(declare-fun GHC.List.head () Int)
(declare-fun lq_tmp$36$x$35$$35$1782 () Int)
(declare-fun lq_tmp$36$x$35$$35$1775 () Int)
(declare-fun Data.Primitive.Types.PrimStorable () Int)
(declare-fun cast_as_int () Int)
(declare-fun GHC.Num.$43$ () Int)
(declare-fun len () Int)
(declare-fun GHC.Prim.$40$$35$$44$$44$$35$$41$ () Int)
(declare-fun GHC.Types.Int64Rep () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792807836$35$$35$d3HC () Int)
(declare-fun GHC.Types.LT () Int)
(declare-fun GHC.Tuple.$40$$44$$44$$41$ () Int)
(declare-fun papp1 () Int)
(declare-fun src_offset$35$$35$a1R1 () Int)
(declare-fun fix$36$$36$dPrim_a1TP () Int)
(declare-fun GHC.List.drop () Int)
(declare-fun GHC.Types.AddrRep () Int)
(declare-fun GHC.Prim.$60$$35$ () Int)
(declare-fun papp6 () Int)
(declare-fun GHC.Real.mod () Int)
(declare-fun lq_tmp$36$x$35$$35$1499 () Int)
(declare-fun lq_tmp$36$x$35$$35$1554 () Int)
(declare-fun GHC.Classes.C$58$IP () Int)
(declare-fun Data.Either.Left () Int)
(declare-fun fix$36$$36$krep_a1V2 () Int)
(declare-fun elt$35$$35$a1QZ () Int)
(declare-fun GHC.List.zip () Int)
(declare-fun liquid_internal_this () Int)
(declare-fun GHC.Real.fromRational () Int)
(declare-fun lq_tmp$36$x$35$$35$1742 () Int)
(declare-fun GHC.Classes.$62$ () Int)
(declare-fun GHC.Types.KindRepTyConApp () Int)
(declare-fun GHC.Tuple.$40$$41$ () Int)
(declare-fun lqdc$35$$35$$36$select$35$$35$GHC.Maybe.Just$35$$35$1 () Int)
(declare-fun GHC.Types.KindRepVar () Int)
(declare-fun lq_tmp$36$x$35$$35$2233 () Int)
(declare-fun GHC.Types.I$35$ () Int)
(declare-fun lq_tmp$36$x$35$$35$1779 () Int)
(declare-fun lit$36$$39$Array$35$ () Str)
(declare-fun GHC.Types.KindRepTypeLitD () Int)
(declare-fun elt$35$$35$a1QQ () Int)
(declare-fun x_Tuple31 () Int)
(declare-fun lq_tmp$36$x$35$$35$745 () Int)
(declare-fun lq_tmp$36$x$35$$35$1587 () Int)
(declare-fun GHC.Magic.runRW$35$ () Int)
(declare-fun ds_d3Gg () Int)
(declare-fun lq_tmp$36$x$35$$35$1028 () Int)
(declare-fun GHC.Num.Integer.IS () Int)
(declare-fun GHC.Types.FloatRep () Int)
(declare-fun lq_tmp$36$x$35$$35$1277 () Int)
(declare-fun lq_tmp$36$x$35$$35$1785 () Int)
(declare-fun GHC.Real.quot () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792807783$35$$35$d3GL () Int)
(declare-fun Data.Tuple.fst () Int)
(declare-fun lit$36$Array.Mutable.PrimUnlifted () Str)
(declare-fun lq_tmp$36$x$35$$35$1780 () Int)
(declare-fun lq_tmp$36$x$35$$35$1777 () Int)
(declare-fun GHC.Types.LiftedRep () Int)
(declare-fun Data.Tuple.snd () Int)
(declare-fun GHC.Types.isTrue$35$ () Int)
(declare-fun GHC.Types.EQ () Int)
(declare-fun Data.Primitive.Types.readByteArray$35$ () Int)
(declare-fun Array.Mutable.PrimUnlifted.Array$35$ () Int)
(declare-fun GHC.Real.$58$$37$ () Int)
(declare-fun Data.Ord.Down () Int)
(declare-fun GHC.Types.MkCoercible () Int)
(declare-fun len$35$$35$a1QI () Int)
(declare-fun lq_tmp$36$x$35$$35$2209 () Int)
(declare-fun GHC.Types.VecRep () Int)
(declare-fun fst () Int)
(declare-fun GHC.List.takeWhile () Int)
(declare-fun GHC.Num.negate () Int)
(declare-fun GHC.Num.$45$ () Int)
(declare-fun GHC.Real.rem () Int)
(declare-fun GHC.Types.krep$36$$42$ () Int)
(declare-fun GHC.Classes.max () Int)
(declare-fun GHC.List.scanr () Int)
(declare-fun GHC.Real.recip () Int)
(declare-fun GHC.Prim.$61$$61$$35$ () Int)
(declare-fun autolen () Int)
(declare-fun GHC.List.replicate () Int)
(declare-fun GHC.Base.. () Int)
(declare-fun GHC.List.take () Int)
(declare-fun GHC.Types.Int16Rep () Int)
(declare-fun papp4 () Int)
(declare-fun GHC.Types.$36$WKindRepTYPE () Int)
(declare-fun GHC.Stack.Types.PushCallStack () Int)
(declare-fun fix$36$$36$krep_a1V0 () Int)
(declare-fun GHC.Real.quotRem () Int)
(declare-fun GHC.Classes.$60$$61$ () Int)
(declare-fun GHC.Num.fromInteger () Int)
(declare-fun lq_tmp$36$x$35$$35$1795 () Int)
(declare-fun GHC.Types.KindRepTYPE () Int)
(declare-fun GHC.Classes.$60$ () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792807838$35$$35$d3HE () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792807816$35$$35$d3Hi () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792807775$35$$35$d3GD () Int)
(declare-fun GHC.Types.SumRep () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792807799$35$$35$d3H1 () Int)
(declare-fun Array.Mutable.PrimUnlifted.makeNoFill$35$ () Int)
(declare-fun GHC.List.filter () Int)
(declare-fun x_Tuple21 () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792807779$35$$35$d3GH () Int)
(declare-fun GHC.Prim.$40$$35$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$44$$35$$41$ () Int)
(declare-fun lq_tmp$36$x$35$$35$708 () Int)
(declare-fun GHC.List.repeat () Int)
(declare-fun head () Int)
(declare-fun GHC.CString.unpackCStringUtf8$35$ () Int)
(declare-fun lq_tmp$36$x$35$$35$1589 () Int)
(declare-fun lq_tmp$36$x$35$$35$1792 () Int)
(declare-fun Data.Primitive.Types.setByteArray$35$ () Int)
(declare-fun GHC.Maybe.Nothing () Int)
(declare-fun GHC.Types.$36$tcMutableByteArray$35$ () Int)
(declare-fun lq_tmp$36$x$35$$35$1105 () Int)
(declare-fun lq_tmp$36$x$35$$35$1279 () Int)
(declare-fun GHC.Prim.$60$$61$$35$ () Int)
(declare-fun lq_tmp$36$x$35$$35$1590 () Int)
(declare-fun fix$36$$36$dPrim_a1U1 () Int)
(declare-fun GHC.Prim.$40$$35$$44$$35$$41$ () Int)
(declare-fun lq_tmp$36$x$35$$35$2103 () Int)
(declare-fun len$35$$35$a1QP () Int)
(declare-fun GHC.Num.Integer.IP () Int)
(declare-fun lq_tmp$36$x$35$$35$1786 () Int)
(declare-fun GHC.Base.map () Int)
(declare-fun x_Tuple32 () Int)
(declare-fun lq_tmp$36$x$35$$35$2147 () Int)
(declare-fun lq_tmp$36$x$35$$35$746 () Int)
(declare-fun GHC.Types.$36$tcRealWorld () Int)
(declare-fun GHC.Err.error () Int)
(declare-fun GHC.Types.TupleRep () Int)
(declare-fun Array.Mutable.PrimUnlifted.get$35$ () Int)
(declare-fun GHC.Classes.compare () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792807787$35$$35$d3GP () Int)
(declare-fun GHC.Types.TrNameS () Int)
(declare-fun GHC.Num.Integer.IN () Int)
(declare-fun GHC.Num.$42$ () Int)
(declare-fun GHC.Types.False () Bool)
(declare-fun fix$36$$36$dPrim_a1Ub () Int)
(declare-fun GHC.Prim.copyMutableByteArray$35$ () Int)
(declare-fun lq_tmp$36$x$35$$35$2051 () Int)
(declare-fun lq_tmp$36$x$35$$35$2253 () Int)
(declare-fun len$35$$35$a1QN () Int)
(declare-fun GHC.Prim.Solo$35$ () Int)
(declare-fun papp2 () Int)
(declare-fun lq_tmp$36$x$35$$35$2120 () Int)
(declare-fun GHC.Classes.$47$$61$ () Int)
(declare-fun GHC.Prim.newByteArray$35$ () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792807847$35$$35$d3HN () Int)
(declare-fun GHC.List.cycle () Int)
(declare-fun GHC.Types.GT () Int)
(declare-fun GHC.Types.Int32Rep () Int)
(declare-fun apply$35$$35$13 (Int (_ BitVec 32)) Bool)
(declare-fun apply$35$$35$1 (Int Int) Bool)
(declare-fun apply$35$$35$3 (Int Int) (_ BitVec 32))
(declare-fun apply$35$$35$15 (Int (_ BitVec 32)) (_ BitVec 32))
(declare-fun apply$35$$35$14 (Int (_ BitVec 32)) Str)
(declare-fun apply$35$$35$9 (Int Str) Bool)
(declare-fun apply$35$$35$4 (Int Bool) Int)
(declare-fun apply$35$$35$10 (Int Str) Str)
(declare-fun apply$35$$35$11 (Int Str) (_ BitVec 32))
(declare-fun apply$35$$35$12 (Int (_ BitVec 32)) Int)
(declare-fun apply$35$$35$8 (Int Str) Int)
(declare-fun apply$35$$35$0 (Int Int) Int)
(declare-fun apply$35$$35$6 (Int Bool) Str)
(declare-fun apply$35$$35$7 (Int Bool) (_ BitVec 32))
(declare-fun apply$35$$35$2 (Int Int) Str)
(declare-fun apply$35$$35$5 (Int Bool) Bool)
(declare-fun coerce$35$$35$13 ((_ BitVec 32)) Bool)
(declare-fun coerce$35$$35$1 (Int) Bool)
(declare-fun coerce$35$$35$3 (Int) (_ BitVec 32))
(declare-fun coerce$35$$35$15 ((_ BitVec 32)) (_ BitVec 32))
(declare-fun coerce$35$$35$14 ((_ BitVec 32)) Str)
(declare-fun coerce$35$$35$9 (Str) Bool)
(declare-fun coerce$35$$35$4 (Bool) Int)
(declare-fun coerce$35$$35$10 (Str) Str)
(declare-fun coerce$35$$35$11 (Str) (_ BitVec 32))
(declare-fun coerce$35$$35$12 ((_ BitVec 32)) Int)
(declare-fun coerce$35$$35$8 (Str) Int)
(declare-fun coerce$35$$35$0 (Int) Int)
(declare-fun coerce$35$$35$6 (Bool) Str)
(declare-fun coerce$35$$35$7 (Bool) (_ BitVec 32))
(declare-fun coerce$35$$35$2 (Int) Str)
(declare-fun coerce$35$$35$5 (Bool) Bool)
(declare-fun smt_lambda$35$$35$13 ((_ BitVec 32) Bool) Int)
(declare-fun smt_lambda$35$$35$1 (Int Bool) Int)
(declare-fun smt_lambda$35$$35$3 (Int (_ BitVec 32)) Int)
(declare-fun smt_lambda$35$$35$15 ((_ BitVec 32) (_ BitVec 32)) Int)
(declare-fun smt_lambda$35$$35$14 ((_ BitVec 32) Str) Int)
(declare-fun smt_lambda$35$$35$9 (Str Bool) Int)
(declare-fun smt_lambda$35$$35$4 (Bool Int) Int)
(declare-fun smt_lambda$35$$35$10 (Str Str) Int)
(declare-fun smt_lambda$35$$35$11 (Str (_ BitVec 32)) Int)
(declare-fun smt_lambda$35$$35$12 ((_ BitVec 32) Int) Int)
(declare-fun smt_lambda$35$$35$8 (Str Int) Int)
(declare-fun smt_lambda$35$$35$0 (Int Int) Int)
(declare-fun smt_lambda$35$$35$6 (Bool Str) Int)
(declare-fun smt_lambda$35$$35$7 (Bool (_ BitVec 32)) Int)
(declare-fun smt_lambda$35$$35$2 (Int Str) Int)
(declare-fun smt_lambda$35$$35$5 (Bool Bool) Int)
(declare-fun lam_arg$35$$35$1$35$$35$4 () Bool)
(declare-fun lam_arg$35$$35$2$35$$35$4 () Bool)
(declare-fun lam_arg$35$$35$3$35$$35$4 () Bool)
(declare-fun lam_arg$35$$35$4$35$$35$4 () Bool)
(declare-fun lam_arg$35$$35$5$35$$35$4 () Bool)
(declare-fun lam_arg$35$$35$6$35$$35$4 () Bool)
(declare-fun lam_arg$35$$35$7$35$$35$4 () Bool)
(declare-fun lam_arg$35$$35$1$35$$35$12 () (_ BitVec 32))
(declare-fun lam_arg$35$$35$2$35$$35$12 () (_ BitVec 32))
(declare-fun lam_arg$35$$35$3$35$$35$12 () (_ BitVec 32))
(declare-fun lam_arg$35$$35$4$35$$35$12 () (_ BitVec 32))
(declare-fun lam_arg$35$$35$5$35$$35$12 () (_ BitVec 32))
(declare-fun lam_arg$35$$35$6$35$$35$12 () (_ BitVec 32))
(declare-fun lam_arg$35$$35$7$35$$35$12 () (_ BitVec 32))
(declare-fun lam_arg$35$$35$1$35$$35$8 () Str)
(declare-fun lam_arg$35$$35$2$35$$35$8 () Str)
(declare-fun lam_arg$35$$35$3$35$$35$8 () Str)
(declare-fun lam_arg$35$$35$4$35$$35$8 () Str)
(declare-fun lam_arg$35$$35$5$35$$35$8 () Str)
(declare-fun lam_arg$35$$35$6$35$$35$8 () Str)
(declare-fun lam_arg$35$$35$7$35$$35$8 () Str)
(declare-fun lam_arg$35$$35$1$35$$35$0 () Int)
(declare-fun lam_arg$35$$35$2$35$$35$0 () Int)
(declare-fun lam_arg$35$$35$3$35$$35$0 () Int)
(declare-fun lam_arg$35$$35$4$35$$35$0 () Int)
(declare-fun lam_arg$35$$35$5$35$$35$0 () Int)
(declare-fun lam_arg$35$$35$6$35$$35$0 () Int)
(declare-fun lam_arg$35$$35$7$35$$35$0 () Int)


(assert (distinct lit$36$Array.Mutable.PrimUnlifted lit$36$$39$Array$35$ lit$36$lh$45$array$45$sort$45$0.1.0.0$45$inplace lit$36$Array$35$))
(assert (distinct GHC.Types.Int32Rep GHC.Types.Int16Rep GHC.Types.LiftedRep GHC.Types.FloatRep GHC.Types.AddrRep GHC.Types.Int64Rep GHC.Types.WordRep GHC.Types.Int8Rep GHC.Types.DoubleRep GHC.Types.IntRep GHC.Types.UnliftedRep GHC.Types.Word64Rep GHC.Types.Word16Rep GHC.Types.Word8Rep GHC.Types.Word32Rep))
(assert (distinct GHC.Types.GT GHC.Types.EQ GHC.Types.LT))
(assert (distinct GHC.Types.False GHC.Types.True))
(assert (= (strLen lit$36$Array$35$) 6))
(assert (= (strLen lit$36$lh$45$array$45$sort$45$0.1.0.0$45$inplace) 29))
(assert (= (strLen lit$36$$39$Array$35$) 7))
(assert (= (strLen lit$36$Array.Mutable.PrimUnlifted) 26))
(push 1)
(push 1)
(pop 1)
(pop 1)
(exit)
