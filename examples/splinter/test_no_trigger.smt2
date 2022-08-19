(set-option :print-success false)
(set-info :smt-lib-version 2.6)
(set-option :auto_config false)
(set-option :type_check true)
(set-option :smt.case_split 3)
(set-option :smt.qi.eager_threshold 100)
(set-option :smt.delay_units true)
(set-option :smt.arith.solver 2)
(set-option :smt.arith.nl false)
(set-option :smt.mbqi false)
(set-option :model.compact false)
(set-option :model.v2 true)
(set-option :pp.bv_literals false)
; done setting options


(set-info :category "industrial")
(declare-sort |T@U| 0)
(declare-sort |T@T| 0)
(declare-fun real_pow (Real Real) Real)
(declare-fun UOrdering2 (|T@U| |T@U|) Bool)
(declare-fun UOrdering3 (|T@T| |T@U| |T@U|) Bool)
(declare-fun tickleBool (Bool) Bool)
(assert (and (tickleBool true) (tickleBool false)))
(declare-fun U_2_int (T@U) Int)
(declare-fun U_2_bool (T@U) Bool)
(declare-fun Ctor (T@T) Int)
(declare-fun intType () T@T)
(declare-fun realType () T@T)
(declare-fun boolType () T@T)
(declare-fun rmodeType () T@T)
(declare-fun stringType () T@T)
(declare-fun regexType () T@T)
(declare-fun int_2_U (Int) T@U)
(declare-fun type (T@U) T@T)
(declare-fun real_2_U (Real) T@U)
(declare-fun U_2_real (T@U) Real)
(declare-fun bool_2_U (Bool) T@U)
(declare-fun rmode_2_U (RoundingMode) T@U)
(declare-fun U_2_rmode (T@U) RoundingMode)
(declare-fun string_2_U (String) T@U)
(declare-fun U_2_string (T@U) String)
(declare-fun regex_2_U ((RegEx String)) T@U)
(declare-fun U_2_regex (T@U) (RegEx String))
(declare-fun TBool () T@U)
(declare-fun TChar () T@U)
(declare-fun TInt () T@U)
(declare-fun TReal () T@U)
(declare-fun TORDINAL () T@U)
(declare-fun TagBool () T@U)
(declare-fun TagChar () T@U)
(declare-fun TagInt () T@U)
(declare-fun TagReal () T@U)
(declare-fun TagORDINAL () T@U)
(declare-fun TagSet () T@U)
(declare-fun TagISet () T@U)
(declare-fun TagMultiSet () T@U)
(declare-fun TagSeq () T@U)
(declare-fun TagMap () T@U)
(declare-fun TagIMap () T@U)
(declare-fun TagClass () T@U)
(declare-fun class._System.int () T@U)
(declare-fun class._System.bool () T@U)
(declare-fun class._System.set () T@U)
(declare-fun class._System.seq () T@U)
(declare-fun class._System.multiset () T@U)
(declare-fun alloc () T@U)
(declare-fun allocName () T@U)
(declare-fun Tagclass._System.nat () T@U)
(declare-fun class._System.object? () T@U)
(declare-fun Tagclass._System.object? () T@U)
(declare-fun Tagclass._System.object () T@U)
(declare-fun class._System.array? () T@U)
(declare-fun Tagclass._System.array? () T@U)
(declare-fun Tagclass._System.array () T@U)
(declare-fun Tagclass._System.___hFunc1 () T@U)
(declare-fun Tagclass._System.___hPartialFunc1 () T@U)
(declare-fun Tagclass._System.___hTotalFunc1 () T@U)
(declare-fun Tagclass._System.___hFunc0 () T@U)
(declare-fun Tagclass._System.___hPartialFunc0 () T@U)
(declare-fun Tagclass._System.___hTotalFunc0 () T@U)
(declare-fun class._System.__default () T@U)
(declare-fun Tagclass._System.__default () T@U)
(declare-fun Tagclass._System.___hFunc2 () T@U)
(declare-fun Tagclass._System.___hPartialFunc2 () T@U)
(declare-fun Tagclass._System.___hTotalFunc2 () T@U)
(declare-fun |##_System._tuple#2._#Make2| () T@U)
(declare-fun Tagclass._System.Tuple2 () T@U)
(declare-fun class._System.Tuple2 () T@U)
(declare-fun |##_System._tuple#0._#Make0| () T@U)
(declare-fun Tagclass._System.Tuple0 () T@U)
(declare-fun class._System.Tuple0 () T@U)
(declare-fun |##Test.ChildMap.ChildMap| () T@U)
(declare-fun Tagclass.Common.Key () T@U)
(declare-fun Tagclass.Test.BetreeNode () T@U)
(declare-fun Tagclass.Test.ChildMap () T@U)
(declare-fun class.Test.ChildMap () T@U)
(declare-fun |##Test.BetreeNode.Nil| () T@U)
(declare-fun |##Test.BetreeNode.BetreeNode| () T@U)
(declare-fun class.Test.BetreeNode () T@U)
(declare-fun |##Test.QueryReceiptLine.QueryReceiptLine| () T@U)
(declare-fun Tagclass.Test.QueryReceiptLine () T@U)
(declare-fun class.Test.QueryReceiptLine () T@U)
(declare-fun |##Test.QueryReceipt.QueryReceipt| () T@U)
(declare-fun Tagclass.Test.QueryReceipt () T@U)
(declare-fun class.Test.QueryReceipt () T@U)
(declare-fun class.Test.__default () T@U)
(declare-fun Tagclass.Test.__default () T@U)
(declare-fun Tagclass.Common.byte () T@U)
(declare-fun class.Common.byte () T@U)
(declare-fun class.Common.__default () T@U)
(declare-fun Tagclass.Common.__default () T@U)
(declare-fun tytagFamily$nat () T@U)
(declare-fun tytagFamily$object () T@U)
(declare-fun tytagFamily$array () T@U)
(declare-fun |tytagFamily$_#Func1| () T@U)
(declare-fun |tytagFamily$_#PartialFunc1| () T@U)
(declare-fun |tytagFamily$_#TotalFunc1| () T@U)
(declare-fun |tytagFamily$_#Func0| () T@U)
(declare-fun |tytagFamily$_#PartialFunc0| () T@U)
(declare-fun |tytagFamily$_#TotalFunc0| () T@U)
(declare-fun tytagFamily$_default () T@U)
(declare-fun |tytagFamily$_#Func2| () T@U)
(declare-fun |tytagFamily$_#PartialFunc2| () T@U)
(declare-fun |tytagFamily$_#TotalFunc2| () T@U)
(declare-fun |tytagFamily$_tuple#2| () T@U)
(declare-fun |tytagFamily$_tuple#0| () T@U)
(declare-fun tytagFamily$Key () T@U)
(declare-fun tytagFamily$BetreeNode () T@U)
(declare-fun tytagFamily$ChildMap () T@U)
(declare-fun tytagFamily$QueryReceiptLine () T@U)
(declare-fun tytagFamily$QueryReceipt () T@U)
(declare-fun tytagFamily$byte () T@U)
(declare-fun TyType () T@T)
(declare-fun TyTagType () T@T)
(declare-fun ClassNameType () T@T)
(declare-fun FieldType (T@T) T@T)
(declare-fun FieldTypeInv0 (T@T) T@T)
(declare-fun NameFamilyType () T@T)
(declare-fun DtCtorIdType () T@T)
(declare-fun TyTagFamilyType () T@T)
(declare-fun $$Language$Dafny () Bool)
(declare-fun TBitvector (Int) T@U)
(declare-fun Inv0_TBitvector (T@U) Int)
(declare-fun TSet (T@U) T@U)
(declare-fun Inv0_TSet (T@U) T@U)
(declare-fun TISet (T@U) T@U)
(declare-fun Inv0_TISet (T@U) T@U)
(declare-fun TSeq (T@U) T@U)
(declare-fun Inv0_TSeq (T@U) T@U)
(declare-fun TMultiSet (T@U) T@U)
(declare-fun Inv0_TMultiSet (T@U) T@U)
(declare-fun TMap (T@U T@U) T@U)
(declare-fun Inv0_TMap (T@U) T@U)
(declare-fun Inv1_TMap (T@U) T@U)
(declare-fun TIMap (T@U T@U) T@U)
(declare-fun Inv0_TIMap (T@U) T@U)
(declare-fun Inv1_TIMap (T@U) T@U)
(declare-fun Tag (T@U) T@U)
(declare-fun Lit (T@U) T@U)
(declare-fun $Box (T@U) T@U)
(declare-fun BoxType () T@T)
(declare-fun LitInt (Int) Int)
(declare-fun LitReal (Real) Real)
(declare-fun |char#ToInt| (T@U) Int)
(declare-fun charType () T@T)
(declare-fun |char#FromInt| (Int) T@U)
(declare-fun |char#Plus| (T@U T@U) T@U)
(declare-fun |char#Minus| (T@U T@U) T@U)
(declare-fun $Unbox (T@T T@U) T@U)
(declare-fun $IsBox (T@U T@U) Bool)
(declare-fun $Is (T@U T@U) Bool)
(declare-fun MapType0Type (T@T T@T) T@T)
(declare-fun MapType0TypeInv0 (T@T) T@T)
(declare-fun MapType0TypeInv1 (T@T) T@T)
(declare-fun MapType0Select (T@U T@U) T@U)
(declare-fun MapType0Store (T@U T@U T@U) T@U)
(declare-fun SeqType (T@T) T@T)
(declare-fun SeqTypeInv0 (T@T) T@T)
(declare-fun MapType (T@T T@T) T@T)
(declare-fun MapTypeInv0 (T@T) T@T)
(declare-fun MapTypeInv1 (T@T) T@T)
(declare-fun IMapType (T@T T@T) T@T)
(declare-fun IMapTypeInv0 (T@T) T@T)
(declare-fun IMapTypeInv1 (T@T) T@T)
(declare-fun $IsAllocBox (T@U T@U T@U) Bool)
(declare-fun refType () T@T)
(declare-fun MapType1Type () T@T)
(declare-fun $IsAlloc (T@U T@U T@U) Bool)
(declare-fun MapType1Select (T@U T@U) T@U)
(declare-fun MapType1Store (T@U T@U T@U) T@U)
(declare-fun $IsGoodMultiSet (T@U) Bool)
(declare-fun |Seq#Index| (T@U Int) T@U)
(declare-fun |Seq#Length| (T@U) Int)
(declare-fun |Map#Elements| (T@U) T@U)
(declare-fun |Map#Domain| (T@U) T@U)
(declare-fun |Map#Values| (T@U) T@U)
(declare-fun |Map#Items| (T@U) T@U)
(declare-fun Tclass._System.Tuple2 (T@U T@U) T@U)
(declare-fun |IMap#Elements| (T@U) T@U)
(declare-fun |IMap#Domain| (T@U) T@U)
(declare-fun |IMap#Values| (T@U) T@U)
(declare-fun |IMap#Items| (T@U) T@U)
(declare-fun TypeTuple (T@U T@U) T@U)
(declare-fun TypeTupleCar (T@U) T@U)
(declare-fun TypeTupleCdr (T@U) T@U)
(declare-fun SetRef_to_SetBox (T@U) T@U)
(declare-fun Tclass._System.object? () T@U)
(declare-fun BoxRank (T@U) Int)
(declare-fun DatatypeTypeType () T@T)
(declare-fun DtRank (T@U) Int)
(declare-fun |ORD#Offset| (T@U) Int)
(declare-fun |ORD#FromNat| (Int) T@U)
(declare-fun |ORD#IsNat| (T@U) Bool)
(declare-fun |ORD#Less| (T@U T@U) Bool)
(declare-fun |ORD#LessThanLimit| (T@U T@U) Bool)
(declare-fun |ORD#Plus| (T@U T@U) T@U)
(declare-fun |ORD#Minus| (T@U T@U) T@U)
(declare-fun AtLayer (T@U T@U) T@U)
(declare-fun LayerTypeType () T@T)
(declare-fun $LS (T@U) T@U)
(declare-fun IndexField (Int) T@U)
(declare-fun FDim (T@U) Int)
(declare-fun IndexField_Inverse (T@U) Int)
(declare-fun MultiIndexField (T@U Int) T@U)
(declare-fun MultiIndexField_Inverse0 (T@U) T@U)
(declare-fun MultiIndexField_Inverse1 (T@U) Int)
(declare-fun FieldOfDecl (T@T T@U T@U) T@U)
(declare-fun DeclType (T@U) T@U)
(declare-fun DeclName (T@U) T@U)
(declare-fun $HeapSucc (T@U T@U) Bool)
(declare-fun $IsGhostField (T@U) Bool)
(declare-fun _System.array.Length (T@U) Int)
(declare-fun q@Int (Real) Int)
(declare-fun q@Real (Int) Real)
(declare-fun $IsGoodHeap (T@U) Bool)
(declare-fun $OneHeap () T@U)
(declare-fun $HeapSuccGhost (T@U T@U) Bool)
(declare-fun |Set#Card| (T@U) Int)
(declare-fun |Set#Empty| (T@T) T@U)
(declare-fun |Set#Singleton| (T@U) T@U)
(declare-fun |Set#UnionOne| (T@U T@U) T@U)
(declare-fun |Set#Union| (T@U T@U) T@U)
(declare-fun |Set#Disjoint| (T@U T@U) Bool)
(declare-fun |Set#Difference| (T@U T@U) T@U)
(declare-fun |Set#Intersection| (T@U T@U) T@U)
(declare-fun |Set#Subset| (T@U T@U) Bool)
(declare-fun |Set#Equal| (T@U T@U) Bool)
(declare-fun |ISet#Empty| (T@T) T@U)
(declare-fun |ISet#UnionOne| (T@U T@U) T@U)
(declare-fun |ISet#Union| (T@U T@U) T@U)
(declare-fun |ISet#Disjoint| (T@U T@U) Bool)
(declare-fun |ISet#Difference| (T@U T@U) T@U)
(declare-fun |ISet#Intersection| (T@U T@U) T@U)
(declare-fun |ISet#Subset| (T@U T@U) Bool)
(declare-fun |ISet#Equal| (T@U T@U) Bool)
(declare-fun |Math#min| (Int Int) Int)
(declare-fun |Math#clip| (Int) Int)
(declare-fun |MultiSet#Card| (T@U) Int)
(declare-fun |MultiSet#Empty| (T@T) T@U)
(declare-fun |MultiSet#Singleton| (T@U) T@U)
(declare-fun |MultiSet#UnionOne| (T@U T@U) T@U)
(declare-fun |MultiSet#Union| (T@U T@U) T@U)
(declare-fun |MultiSet#Intersection| (T@U T@U) T@U)
(declare-fun |MultiSet#Difference| (T@U T@U) T@U)
(declare-fun |MultiSet#Subset| (T@U T@U) Bool)
(declare-fun |MultiSet#Equal| (T@U T@U) Bool)
(declare-fun |MultiSet#Disjoint| (T@U T@U) Bool)
(declare-fun |MultiSet#FromSet| (T@U) T@U)
(declare-fun |MultiSet#FromSeq| (T@U) T@U)
(declare-fun |Seq#Build| (T@U T@U) T@U)
(declare-fun |Seq#Empty| (T@T) T@U)
(declare-fun |Seq#Append| (T@U T@U) T@U)
(declare-fun |Seq#Update| (T@U Int T@U) T@U)
(declare-fun |Seq#Singleton| (T@U) T@U)
(declare-fun |Seq#Build_inv0| (T@U) T@U)
(declare-fun |Seq#Build_inv1| (T@U) T@U)
(declare-fun |Seq#Create| (T@U T@U Int T@U) T@U)
(declare-fun HandleTypeType () T@T)
(declare-fun Apply1 (T@U T@U T@U T@U T@U) T@U)
(declare-fun |Seq#Contains| (T@U T@U) Bool)
(declare-fun |Seq#Take| (T@U Int) T@U)
(declare-fun |Seq#Drop| (T@U Int) T@U)
(declare-fun |Seq#Equal| (T@U T@U) Bool)
(declare-fun |Seq#SameUntil| (T@U T@U Int) Bool)
(declare-fun |Seq#FromArray| (T@U T@U) T@U)
(declare-fun |Seq#Rank| (T@U) Int)
(declare-fun |Map#Card| (T@U) Int)
(declare-fun |Map#Empty| (T@T T@T) T@U)
(declare-fun |#_System._tuple#2._#Make2| (T@U T@U) T@U)
(declare-fun _System.Tuple2._0 (T@U) T@U)
(declare-fun _System.Tuple2._1 (T@U) T@U)
(declare-fun |Map#Glue| (T@U T@U T@U) T@U)
(declare-fun |Map#Build| (T@U T@U T@U) T@U)
(declare-fun |Map#Merge| (T@U T@U) T@U)
(declare-fun |Map#Subtract| (T@U T@U) T@U)
(declare-fun |Map#Equal| (T@U T@U) Bool)
(declare-fun |Map#Disjoint| (T@U T@U) Bool)
(declare-fun |IMap#Empty| (T@T T@T) T@U)
(declare-fun |IMap#Glue| (T@U T@U T@U) T@U)
(declare-fun |IMap#Build| (T@U T@U T@U) T@U)
(declare-fun |IMap#Equal| (T@U T@U) Bool)
(declare-fun |IMap#Merge| (T@U T@U) T@U)
(declare-fun |IMap#Subtract| (T@U T@U) T@U)
(declare-fun INTERNAL_add_boogie (Int Int) Int)
(declare-fun INTERNAL_sub_boogie (Int Int) Int)
(declare-fun INTERNAL_mul_boogie (Int Int) Int)
(declare-fun INTERNAL_div_boogie (Int Int) Int)
(declare-fun INTERNAL_mod_boogie (Int Int) Int)
(declare-fun INTERNAL_lt_boogie (Int Int) Bool)
(declare-fun INTERNAL_le_boogie (Int Int) Bool)
(declare-fun INTERNAL_gt_boogie (Int Int) Bool)
(declare-fun INTERNAL_ge_boogie (Int Int) Bool)
(declare-fun Mul (Int Int) Int)
(declare-fun Div (Int Int) Int)
(declare-fun Mod (Int Int) Int)
(declare-fun Add (Int Int) Int)
(declare-fun Sub (Int Int) Int)
(declare-fun _System.__default.rank__is__less__than (T@U T@U T@U T@U) Bool)
(declare-fun Tclass._System.nat () T@U)
(declare-fun TagFamily (T@U) T@U)
(declare-fun null () T@U)
(declare-fun Tclass._System.object () T@U)
(declare-fun Tclass._System.array? (T@U) T@U)
(declare-fun Tclass._System.array?_0 (T@U) T@U)
(declare-fun dtype (T@U) T@U)
(declare-fun Tclass._System.array (T@U) T@U)
(declare-fun Tclass._System.array_0 (T@U) T@U)
(declare-fun Tclass._System.___hFunc1 (T@U T@U) T@U)
(declare-fun Tclass._System.___hFunc1_0 (T@U) T@U)
(declare-fun Tclass._System.___hFunc1_1 (T@U) T@U)
(declare-fun Handle1 (T@U T@U T@U) T@U)
(declare-fun MapType2Type (T@T T@T T@T) T@T)
(declare-fun MapType2Select (T@U T@U T@U) T@U)
(declare-fun MapType2TypeInv0 (T@T) T@T)
(declare-fun MapType2TypeInv1 (T@T) T@T)
(declare-fun MapType2TypeInv2 (T@T) T@T)
(declare-fun MapType2Store (T@U T@U T@U T@U) T@U)
(declare-fun Requires1 (T@U T@U T@U T@U T@U) Bool)
(declare-fun Reads1 (T@U T@U T@U T@U T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc1 (T@U T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc1_0 (T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc1_1 (T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc1 (T@U T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc1_0 (T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc1_1 (T@U) T@U)
(declare-fun Tclass._System.___hFunc0 (T@U) T@U)
(declare-fun Tclass._System.___hFunc0_0 (T@U) T@U)
(declare-fun Apply0 (T@U T@U T@U) T@U)
(declare-fun Handle0 (T@U T@U T@U) T@U)
(declare-fun Requires0 (T@U T@U T@U) Bool)
(declare-fun Reads0 (T@U T@U T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc0 (T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc0_0 (T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc0 (T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc0_0 (T@U) T@U)
(declare-fun Tclass._System.__default () T@U)
(declare-fun |_System.__default.rank__is__less__than#canCall| (T@U T@U T@U T@U) Bool)
(declare-fun |_System.__default.rank__is__less__than#requires| (T@U T@U T@U T@U) Bool)
(declare-fun Tclass._System.___hFunc2 (T@U T@U T@U) T@U)
(declare-fun Tclass._System.___hFunc2_0 (T@U) T@U)
(declare-fun Tclass._System.___hFunc2_1 (T@U) T@U)
(declare-fun Tclass._System.___hFunc2_2 (T@U) T@U)
(declare-fun Apply2 (T@U T@U T@U T@U T@U T@U T@U) T@U)
(declare-fun Handle2 (T@U T@U T@U) T@U)
(declare-fun MapType3Type (T@T T@T T@T T@T) T@T)
(declare-fun MapType3Select (T@U T@U T@U T@U) T@U)
(declare-fun MapType3TypeInv0 (T@T) T@T)
(declare-fun MapType3TypeInv1 (T@T) T@T)
(declare-fun MapType3TypeInv2 (T@T) T@T)
(declare-fun MapType3TypeInv3 (T@T) T@T)
(declare-fun MapType3Store (T@U T@U T@U T@U T@U) T@U)
(declare-fun Requires2 (T@U T@U T@U T@U T@U T@U T@U) Bool)
(declare-fun Reads2 (T@U T@U T@U T@U T@U T@U T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc2 (T@U T@U T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc2_0 (T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc2_1 (T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc2_2 (T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc2 (T@U T@U T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc2_0 (T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc2_1 (T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc2_2 (T@U) T@U)
(declare-fun DatatypeCtorId (T@U) T@U)
(declare-fun _System.Tuple2.___hMake2_q (T@U) Bool)
(declare-fun Tclass._System.Tuple2_0 (T@U) T@U)
(declare-fun Tclass._System.Tuple2_1 (T@U) T@U)
(declare-fun |$IsA#_System.Tuple2| (T@U) Bool)
(declare-fun |_System.Tuple2#Equal| (T@U T@U) Bool)
(declare-fun |#_System._tuple#0._#Make0| () T@U)
(declare-fun _System.Tuple0.___hMake0_q (T@U) Bool)
(declare-fun Tclass._System.Tuple0 () T@U)
(declare-fun |$IsA#_System.Tuple0| (T@U) Bool)
(declare-fun |_System.Tuple0#Equal| (T@U T@U) Bool)
(declare-fun |#Test.ChildMap.ChildMap| (T@U) T@U)
(declare-fun Test.ChildMap.ChildMap_q (T@U) Bool)
(declare-fun Tclass.Common.Key () T@U)
(declare-fun Tclass.Test.BetreeNode () T@U)
(declare-fun Tclass.Test.ChildMap () T@U)
(declare-fun Test.ChildMap.mapp (T@U) T@U)
(declare-fun |$IsA#Test.ChildMap| (T@U) Bool)
(declare-fun |Test.ChildMap#Equal| (T@U T@U) Bool)
(declare-fun Test.ChildMap.WF (T@U T@U) Bool)
(declare-fun AsFuelBottom (T@U) T@U)
(declare-fun $LZ () T@U)
(declare-fun $FunctionContextHeight () Int)
(declare-fun |Test.ChildMap.WF#canCall| (T@U) Bool)
(declare-fun |Test.ChildMap.WF#requires| (T@U T@U) Bool)
(declare-fun |Common.__default.TotalSet#canCall| (T@U) Bool)
(declare-fun Common.__default.TotalSet (T@U) Bool)
(declare-fun Common.__default.AnyKey (T@U) Bool)
(declare-fun |Common.__default.AnyKey#canCall| (T@U) Bool)
(declare-fun |Test.BetreeNode.WF#canCall| (T@U) Bool)
(declare-fun Test.BetreeNode.WF (T@U T@U) Bool)
(declare-fun |#Test.BetreeNode.Nil| () T@U)
(declare-fun Test.BetreeNode.Nil_q (T@U) Bool)
(declare-fun |#Test.BetreeNode.BetreeNode| (T@U) T@U)
(declare-fun Test.BetreeNode.BetreeNode_q (T@U) Bool)
(declare-fun Test.BetreeNode.children (T@U) T@U)
(declare-fun |$IsA#Test.BetreeNode| (T@U) Bool)
(declare-fun |Test.BetreeNode#Equal| (T@U T@U) Bool)
(declare-fun |Test.BetreeNode.WF#requires| (T@U T@U) Bool)
(declare-fun |#Test.QueryReceiptLine.QueryReceiptLine| (T@U) T@U)
(declare-fun Test.QueryReceiptLine.QueryReceiptLine_q (T@U) Bool)
(declare-fun Tclass.Test.QueryReceiptLine () T@U)
(declare-fun Test.QueryReceiptLine.node (T@U) T@U)
(declare-fun |$IsA#Test.QueryReceiptLine| (T@U) Bool)
(declare-fun |Test.QueryReceiptLine#Equal| (T@U T@U) Bool)
(declare-fun Test.QueryReceiptLine.WF (T@U) Bool)
(declare-fun |Test.QueryReceiptLine.WF#canCall| (T@U) Bool)
(declare-fun |Test.QueryReceiptLine.WF#requires| (T@U) Bool)
(declare-fun |#Test.QueryReceipt.QueryReceipt| (T@U T@U T@U) T@U)
(declare-fun Test.QueryReceipt.QueryReceipt_q (T@U) Bool)
(declare-fun Tclass.Test.QueryReceipt () T@U)
(declare-fun Test.QueryReceipt.key (T@U) T@U)
(declare-fun Test.QueryReceipt.root (T@U) T@U)
(declare-fun Test.QueryReceipt.lines (T@U) T@U)
(declare-fun |$IsA#Test.QueryReceipt| (T@U) Bool)
(declare-fun |Test.QueryReceipt#Equal| (T@U T@U) Bool)
(declare-fun Test.QueryReceipt.Structure (T@U) Bool)
(declare-fun |Test.QueryReceipt.Structure#canCall| (T@U) Bool)
(declare-fun |Test.QueryReceipt.Structure#requires| (T@U) Bool)
(declare-fun Test.QueryReceipt.AllLinesWF (T@U) Bool)
(declare-fun |Test.QueryReceipt.AllLinesWF#canCall| (T@U) Bool)
(declare-fun |Test.QueryReceipt.AllLinesWF#requires| (T@U) Bool)
(declare-fun Test.QueryReceipt.ChildAt (T@U Int) T@U)
(declare-fun |Test.QueryReceipt.ChildAt#canCall| (T@U Int) Bool)
(declare-fun |Test.QueryReceipt.ChildAt#requires| (T@U Int) Bool)
(declare-fun Tclass.Test.__default () T@U)
(declare-fun Tclass.Common.byte () T@U)
(declare-fun Tclass.Common.__default () T@U)
(declare-fun |Common.__default.AnyKey#requires| (T@U) Bool)
(declare-fun |Common.__default.TotalSet#requires| (T@U) Bool)
(declare-fun MapType4Select (T@U T@U T@U) T@U)
(declare-fun |lambda#0| (T@U T@U T@U Bool) T@U)
(declare-fun MapType4Type (T@T T@T) T@T)
(declare-fun MapType4TypeInv0 (T@T) T@T)
(declare-fun MapType4TypeInv1 (T@T) T@T)
(declare-fun MapType4Store (T@U T@U T@U T@U) T@U)
(declare-fun |lambda#1| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#2| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#3| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#4| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#5| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#6| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#7| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#8| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#9| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#10| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#11| (T@U T@U T@U Bool) T@U)
(assert  (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (Ctor intType) 0) (= (Ctor realType) 1)) (= (Ctor boolType) 2)) (= (Ctor rmodeType) 3)) (= (Ctor stringType) 4)) (= (Ctor regexType) 5)) (forall ((arg0 Int) ) (! (= (U_2_int (int_2_U arg0)) arg0)
 :qid |typeInv:U_2_int|
 :pattern ( (int_2_U arg0))
))) (forall ((x T@U) ) (!  (=> (= (type x) intType) (= (int_2_U (U_2_int x)) x))
 :qid |cast:U_2_int|
 :pattern ( (U_2_int x))
))) (forall ((arg0@@0 Int) ) (! (= (type (int_2_U arg0@@0)) intType)
 :qid |funType:int_2_U|
 :pattern ( (int_2_U arg0@@0))
))) (forall ((arg0@@1 Real) ) (! (= (U_2_real (real_2_U arg0@@1)) arg0@@1)
 :qid |typeInv:U_2_real|
 :pattern ( (real_2_U arg0@@1))
))) (forall ((x@@0 T@U) ) (!  (=> (= (type x@@0) realType) (= (real_2_U (U_2_real x@@0)) x@@0))
 :qid |cast:U_2_real|
 :pattern ( (U_2_real x@@0))
))) (forall ((arg0@@2 Real) ) (! (= (type (real_2_U arg0@@2)) realType)
 :qid |funType:real_2_U|
 :pattern ( (real_2_U arg0@@2))
))) (forall ((arg0@@3 Bool) ) (! (= (U_2_bool (bool_2_U arg0@@3)) arg0@@3)
 :qid |typeInv:U_2_bool|
 :pattern ( (bool_2_U arg0@@3))
))) (forall ((x@@1 T@U) ) (!  (=> (= (type x@@1) boolType) (= (bool_2_U (U_2_bool x@@1)) x@@1))
 :qid |cast:U_2_bool|
 :pattern ( (U_2_bool x@@1))
))) (forall ((arg0@@4 Bool) ) (! (= (type (bool_2_U arg0@@4)) boolType)
 :qid |funType:bool_2_U|
 :pattern ( (bool_2_U arg0@@4))
))) (forall ((arg0@@5 RoundingMode) ) (! (= (U_2_rmode (rmode_2_U arg0@@5)) arg0@@5)
 :qid |typeInv:U_2_rmode|
 :pattern ( (rmode_2_U arg0@@5))
))) (forall ((x@@2 T@U) ) (!  (=> (= (type x@@2) rmodeType) (= (rmode_2_U (U_2_rmode x@@2)) x@@2))
 :qid |cast:U_2_rmode|
 :pattern ( (U_2_rmode x@@2))
))) (forall ((arg0@@6 RoundingMode) ) (! (= (type (rmode_2_U arg0@@6)) rmodeType)
 :qid |funType:rmode_2_U|
 :pattern ( (rmode_2_U arg0@@6))
))) (forall ((arg0@@7 String) ) (! (= (U_2_string (string_2_U arg0@@7)) arg0@@7)
 :qid |typeInv:U_2_string|
 :pattern ( (string_2_U arg0@@7))
))) (forall ((x@@3 T@U) ) (!  (=> (= (type x@@3) stringType) (= (string_2_U (U_2_string x@@3)) x@@3))
 :qid |cast:U_2_string|
 :pattern ( (U_2_string x@@3))
))) (forall ((arg0@@8 String) ) (! (= (type (string_2_U arg0@@8)) stringType)
 :qid |funType:string_2_U|
 :pattern ( (string_2_U arg0@@8))
))) (forall ((arg0@@9 (RegEx String)) ) (! (= (U_2_regex (regex_2_U arg0@@9)) arg0@@9)
 :qid |typeInv:U_2_regex|
 :pattern ( (regex_2_U arg0@@9))
))) (forall ((x@@4 T@U) ) (!  (=> (= (type x@@4) regexType) (= (regex_2_U (U_2_regex x@@4)) x@@4))
 :qid |cast:U_2_regex|
 :pattern ( (U_2_regex x@@4))
))) (forall ((arg0@@10 (RegEx String)) ) (! (= (type (regex_2_U arg0@@10)) regexType)
 :qid |funType:regex_2_U|
 :pattern ( (regex_2_U arg0@@10))
))))
(assert (forall ((x@@5 T@U) ) (! (UOrdering2 x@@5 x@@5)
 :qid |bg:subtype-refl|
 :no-pattern (U_2_int x@@5)
 :no-pattern (U_2_bool x@@5)
)))
(assert (forall ((x@@6 T@U) (y T@U) (z T@U) ) (! (let ((alpha (type x@@6)))
 (=> (and (and (= (type y) alpha) (= (type z) alpha)) (and (UOrdering2 x@@6 y) (UOrdering2 y z))) (UOrdering2 x@@6 z)))
 :qid |bg:subtype-trans|
 :pattern ( (UOrdering2 x@@6 y) (UOrdering2 y z))
)))
(assert (forall ((x@@7 T@U) (y@@0 T@U) ) (! (let ((alpha@@0 (type x@@7)))
 (=> (= (type y@@0) alpha@@0) (=> (and (UOrdering2 x@@7 y@@0) (UOrdering2 y@@0 x@@7)) (= x@@7 y@@0))))
 :qid |bg:subtype-antisymm|
 :pattern ( (UOrdering2 x@@7 y@@0) (UOrdering2 y@@0 x@@7))
)))
(assert  (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (Ctor TyType) 6) (= (type TBool) TyType)) (= (type TChar) TyType)) (= (type TInt) TyType)) (= (type TReal) TyType)) (= (type TORDINAL) TyType)) (= (Ctor TyTagType) 7)) (= (type TagBool) TyTagType)) (= (type TagChar) TyTagType)) (= (type TagInt) TyTagType)) (= (type TagReal) TyTagType)) (= (type TagORDINAL) TyTagType)) (= (type TagSet) TyTagType)) (= (type TagISet) TyTagType)) (= (type TagMultiSet) TyTagType)) (= (type TagSeq) TyTagType)) (= (type TagMap) TyTagType)) (= (type TagIMap) TyTagType)) (= (type TagClass) TyTagType)) (= (Ctor ClassNameType) 8)) (= (type class._System.int) ClassNameType)) (= (type class._System.bool) ClassNameType)) (= (type class._System.set) ClassNameType)) (= (type class._System.seq) ClassNameType)) (= (type class._System.multiset) ClassNameType)) (forall ((arg0@@11 T@T) ) (! (= (Ctor (FieldType arg0@@11)) 9)
 :qid |ctor:FieldType|
))) (forall ((arg0@@12 T@T) ) (! (= (FieldTypeInv0 (FieldType arg0@@12)) arg0@@12)
 :qid |typeInv:FieldTypeInv0|
 :pattern ( (FieldType arg0@@12))
))) (= (type alloc) (FieldType boolType))) (= (Ctor NameFamilyType) 10)) (= (type allocName) NameFamilyType)) (= (type Tagclass._System.nat) TyTagType)) (= (type class._System.object?) ClassNameType)) (= (type Tagclass._System.object?) TyTagType)) (= (type Tagclass._System.object) TyTagType)) (= (type class._System.array?) ClassNameType)) (= (type Tagclass._System.array?) TyTagType)) (= (type Tagclass._System.array) TyTagType)) (= (type Tagclass._System.___hFunc1) TyTagType)) (= (type Tagclass._System.___hPartialFunc1) TyTagType)) (= (type Tagclass._System.___hTotalFunc1) TyTagType)) (= (type Tagclass._System.___hFunc0) TyTagType)) (= (type Tagclass._System.___hPartialFunc0) TyTagType)) (= (type Tagclass._System.___hTotalFunc0) TyTagType)) (= (type class._System.__default) ClassNameType)) (= (type Tagclass._System.__default) TyTagType)) (= (type Tagclass._System.___hFunc2) TyTagType)) (= (type Tagclass._System.___hPartialFunc2) TyTagType)) (= (type Tagclass._System.___hTotalFunc2) TyTagType)) (= (Ctor DtCtorIdType) 11)) (= (type |##_System._tuple#2._#Make2|) DtCtorIdType)) (= (type Tagclass._System.Tuple2) TyTagType)) (= (type class._System.Tuple2) ClassNameType)) (= (type |##_System._tuple#0._#Make0|) DtCtorIdType)) (= (type Tagclass._System.Tuple0) TyTagType)) (= (type class._System.Tuple0) ClassNameType)) (= (type |##Test.ChildMap.ChildMap|) DtCtorIdType)) (= (type Tagclass.Common.Key) TyTagType)) (= (type Tagclass.Test.BetreeNode) TyTagType)) (= (type Tagclass.Test.ChildMap) TyTagType)) (= (type class.Test.ChildMap) ClassNameType)) (= (type |##Test.BetreeNode.Nil|) DtCtorIdType)) (= (type |##Test.BetreeNode.BetreeNode|) DtCtorIdType)) (= (type class.Test.BetreeNode) ClassNameType)) (= (type |##Test.QueryReceiptLine.QueryReceiptLine|) DtCtorIdType)) (= (type Tagclass.Test.QueryReceiptLine) TyTagType)) (= (type class.Test.QueryReceiptLine) ClassNameType)) (= (type |##Test.QueryReceipt.QueryReceipt|) DtCtorIdType)) (= (type Tagclass.Test.QueryReceipt) TyTagType)) (= (type class.Test.QueryReceipt) ClassNameType)) (= (type class.Test.__default) ClassNameType)) (= (type Tagclass.Test.__default) TyTagType)) (= (type Tagclass.Common.byte) TyTagType)) (= (type class.Common.byte) ClassNameType)) (= (type class.Common.__default) ClassNameType)) (= (type Tagclass.Common.__default) TyTagType)) (= (Ctor TyTagFamilyType) 12)) (= (type tytagFamily$nat) TyTagFamilyType)) (= (type tytagFamily$object) TyTagFamilyType)) (= (type tytagFamily$array) TyTagFamilyType)) (= (type |tytagFamily$_#Func1|) TyTagFamilyType)) (= (type |tytagFamily$_#PartialFunc1|) TyTagFamilyType)) (= (type |tytagFamily$_#TotalFunc1|) TyTagFamilyType)) (= (type |tytagFamily$_#Func0|) TyTagFamilyType)) (= (type |tytagFamily$_#PartialFunc0|) TyTagFamilyType)) (= (type |tytagFamily$_#TotalFunc0|) TyTagFamilyType)) (= (type tytagFamily$_default) TyTagFamilyType)) (= (type |tytagFamily$_#Func2|) TyTagFamilyType)) (= (type |tytagFamily$_#PartialFunc2|) TyTagFamilyType)) (= (type |tytagFamily$_#TotalFunc2|) TyTagFamilyType)) (= (type |tytagFamily$_tuple#2|) TyTagFamilyType)) (= (type |tytagFamily$_tuple#0|) TyTagFamilyType)) (= (type tytagFamily$Key) TyTagFamilyType)) (= (type tytagFamily$BetreeNode) TyTagFamilyType)) (= (type tytagFamily$ChildMap) TyTagFamilyType)) (= (type tytagFamily$QueryReceiptLine) TyTagFamilyType)) (= (type tytagFamily$QueryReceipt) TyTagFamilyType)) (= (type tytagFamily$byte) TyTagFamilyType)))
(assert (distinct TBool TChar TInt TReal TORDINAL TagBool TagChar TagInt TagReal TagORDINAL TagSet TagISet TagMultiSet TagSeq TagMap TagIMap TagClass class._System.int class._System.bool class._System.set class._System.seq class._System.multiset alloc allocName Tagclass._System.nat class._System.object? Tagclass._System.object? Tagclass._System.object class._System.array? Tagclass._System.array? Tagclass._System.array Tagclass._System.___hFunc1 Tagclass._System.___hPartialFunc1 Tagclass._System.___hTotalFunc1 Tagclass._System.___hFunc0 Tagclass._System.___hPartialFunc0 Tagclass._System.___hTotalFunc0 class._System.__default Tagclass._System.__default Tagclass._System.___hFunc2 Tagclass._System.___hPartialFunc2 Tagclass._System.___hTotalFunc2 |##_System._tuple#2._#Make2| Tagclass._System.Tuple2 class._System.Tuple2 |##_System._tuple#0._#Make0| Tagclass._System.Tuple0 class._System.Tuple0 |##Test.ChildMap.ChildMap| Tagclass.Common.Key Tagclass.Test.BetreeNode Tagclass.Test.ChildMap class.Test.ChildMap |##Test.BetreeNode.Nil| |##Test.BetreeNode.BetreeNode| class.Test.BetreeNode |##Test.QueryReceiptLine.QueryReceiptLine| Tagclass.Test.QueryReceiptLine class.Test.QueryReceiptLine |##Test.QueryReceipt.QueryReceipt| Tagclass.Test.QueryReceipt class.Test.QueryReceipt class.Test.__default Tagclass.Test.__default Tagclass.Common.byte class.Common.byte class.Common.__default Tagclass.Common.__default tytagFamily$nat tytagFamily$object tytagFamily$array |tytagFamily$_#Func1| |tytagFamily$_#PartialFunc1| |tytagFamily$_#TotalFunc1| |tytagFamily$_#Func0| |tytagFamily$_#PartialFunc0| |tytagFamily$_#TotalFunc0| tytagFamily$_default |tytagFamily$_#Func2| |tytagFamily$_#PartialFunc2| |tytagFamily$_#TotalFunc2| |tytagFamily$_tuple#2| |tytagFamily$_tuple#0| tytagFamily$Key tytagFamily$BetreeNode tytagFamily$ChildMap tytagFamily$QueryReceiptLine tytagFamily$QueryReceipt tytagFamily$byte)
)
(assert $$Language$Dafny)
(assert (forall ((arg0@@13 Int) ) (! (= (type (TBitvector arg0@@13)) TyType)
 :qid |funType:TBitvector|
 :pattern ( (TBitvector arg0@@13))
)))
(assert (forall ((w Int) ) (! (= (Inv0_TBitvector (TBitvector w)) w)
 :qid |DafnyPreludebpl.34:15|
 :skolemid |347|
 :pattern ( (TBitvector w))
)))
(assert  (and (forall ((arg0@@14 T@U) ) (! (= (type (TSet arg0@@14)) TyType)
 :qid |funType:TSet|
 :pattern ( (TSet arg0@@14))
)) (forall ((arg0@@15 T@U) ) (! (= (type (Inv0_TSet arg0@@15)) TyType)
 :qid |funType:Inv0_TSet|
 :pattern ( (Inv0_TSet arg0@@15))
))))
(assert (forall ((t T@U) ) (!  (=> (= (type t) TyType) (= (Inv0_TSet (TSet t)) t))
 :qid |DafnyPreludebpl.36:15|
 :skolemid |348|
 :pattern ( (TSet t))
)))
(assert  (and (forall ((arg0@@16 T@U) ) (! (= (type (TISet arg0@@16)) TyType)
 :qid |funType:TISet|
 :pattern ( (TISet arg0@@16))
)) (forall ((arg0@@17 T@U) ) (! (= (type (Inv0_TISet arg0@@17)) TyType)
 :qid |funType:Inv0_TISet|
 :pattern ( (Inv0_TISet arg0@@17))
))))
(assert (forall ((t@@0 T@U) ) (!  (=> (= (type t@@0) TyType) (= (Inv0_TISet (TISet t@@0)) t@@0))
 :qid |DafnyPreludebpl.38:15|
 :skolemid |349|
 :pattern ( (TISet t@@0))
)))
(assert  (and (forall ((arg0@@18 T@U) ) (! (= (type (TSeq arg0@@18)) TyType)
 :qid |funType:TSeq|
 :pattern ( (TSeq arg0@@18))
)) (forall ((arg0@@19 T@U) ) (! (= (type (Inv0_TSeq arg0@@19)) TyType)
 :qid |funType:Inv0_TSeq|
 :pattern ( (Inv0_TSeq arg0@@19))
))))
(assert (forall ((t@@1 T@U) ) (!  (=> (= (type t@@1) TyType) (= (Inv0_TSeq (TSeq t@@1)) t@@1))
 :qid |DafnyPreludebpl.40:15|
 :skolemid |350|
 :pattern ( (TSeq t@@1))
)))
(assert  (and (forall ((arg0@@20 T@U) ) (! (= (type (TMultiSet arg0@@20)) TyType)
 :qid |funType:TMultiSet|
 :pattern ( (TMultiSet arg0@@20))
)) (forall ((arg0@@21 T@U) ) (! (= (type (Inv0_TMultiSet arg0@@21)) TyType)
 :qid |funType:Inv0_TMultiSet|
 :pattern ( (Inv0_TMultiSet arg0@@21))
))))
(assert (forall ((t@@2 T@U) ) (!  (=> (= (type t@@2) TyType) (= (Inv0_TMultiSet (TMultiSet t@@2)) t@@2))
 :qid |DafnyPreludebpl.42:15|
 :skolemid |351|
 :pattern ( (TMultiSet t@@2))
)))
(assert  (and (forall ((arg0@@22 T@U) (arg1 T@U) ) (! (= (type (TMap arg0@@22 arg1)) TyType)
 :qid |funType:TMap|
 :pattern ( (TMap arg0@@22 arg1))
)) (forall ((arg0@@23 T@U) ) (! (= (type (Inv0_TMap arg0@@23)) TyType)
 :qid |funType:Inv0_TMap|
 :pattern ( (Inv0_TMap arg0@@23))
))))
(assert (forall ((t@@3 T@U) (u T@U) ) (!  (=> (and (= (type t@@3) TyType) (= (type u) TyType)) (= (Inv0_TMap (TMap t@@3 u)) t@@3))
 :qid |DafnyPreludebpl.45:15|
 :skolemid |352|
 :pattern ( (TMap t@@3 u))
)))
(assert (forall ((arg0@@24 T@U) ) (! (= (type (Inv1_TMap arg0@@24)) TyType)
 :qid |funType:Inv1_TMap|
 :pattern ( (Inv1_TMap arg0@@24))
)))
(assert (forall ((t@@4 T@U) (u@@0 T@U) ) (!  (=> (and (= (type t@@4) TyType) (= (type u@@0) TyType)) (= (Inv1_TMap (TMap t@@4 u@@0)) u@@0))
 :qid |DafnyPreludebpl.46:15|
 :skolemid |353|
 :pattern ( (TMap t@@4 u@@0))
)))
(assert  (and (forall ((arg0@@25 T@U) (arg1@@0 T@U) ) (! (= (type (TIMap arg0@@25 arg1@@0)) TyType)
 :qid |funType:TIMap|
 :pattern ( (TIMap arg0@@25 arg1@@0))
)) (forall ((arg0@@26 T@U) ) (! (= (type (Inv0_TIMap arg0@@26)) TyType)
 :qid |funType:Inv0_TIMap|
 :pattern ( (Inv0_TIMap arg0@@26))
))))
(assert (forall ((t@@5 T@U) (u@@1 T@U) ) (!  (=> (and (= (type t@@5) TyType) (= (type u@@1) TyType)) (= (Inv0_TIMap (TIMap t@@5 u@@1)) t@@5))
 :qid |DafnyPreludebpl.49:15|
 :skolemid |354|
 :pattern ( (TIMap t@@5 u@@1))
)))
(assert (forall ((arg0@@27 T@U) ) (! (= (type (Inv1_TIMap arg0@@27)) TyType)
 :qid |funType:Inv1_TIMap|
 :pattern ( (Inv1_TIMap arg0@@27))
)))
(assert (forall ((t@@6 T@U) (u@@2 T@U) ) (!  (=> (and (= (type t@@6) TyType) (= (type u@@2) TyType)) (= (Inv1_TIMap (TIMap t@@6 u@@2)) u@@2))
 :qid |DafnyPreludebpl.50:15|
 :skolemid |355|
 :pattern ( (TIMap t@@6 u@@2))
)))
(assert (forall ((arg0@@28 T@U) ) (! (= (type (Tag arg0@@28)) TyTagType)
 :qid |funType:Tag|
 :pattern ( (Tag arg0@@28))
)))
(assert (= (Tag TBool) TagBool))
(assert (= (Tag TChar) TagChar))
(assert (= (Tag TInt) TagInt))
(assert (= (Tag TReal) TagReal))
(assert (= (Tag TORDINAL) TagORDINAL))
(assert (forall ((t@@7 T@U) ) (!  (=> (= (type t@@7) TyType) (= (Tag (TSet t@@7)) TagSet))
 :qid |DafnyPreludebpl.76:15|
 :skolemid |356|
 :pattern ( (TSet t@@7))
)))
(assert (forall ((t@@8 T@U) ) (!  (=> (= (type t@@8) TyType) (= (Tag (TISet t@@8)) TagISet))
 :qid |DafnyPreludebpl.77:15|
 :skolemid |357|
 :pattern ( (TISet t@@8))
)))
(assert (forall ((t@@9 T@U) ) (!  (=> (= (type t@@9) TyType) (= (Tag (TMultiSet t@@9)) TagMultiSet))
 :qid |DafnyPreludebpl.78:15|
 :skolemid |358|
 :pattern ( (TMultiSet t@@9))
)))
(assert (forall ((t@@10 T@U) ) (!  (=> (= (type t@@10) TyType) (= (Tag (TSeq t@@10)) TagSeq))
 :qid |DafnyPreludebpl.79:15|
 :skolemid |359|
 :pattern ( (TSeq t@@10))
)))
(assert (forall ((t@@11 T@U) (u@@3 T@U) ) (!  (=> (and (= (type t@@11) TyType) (= (type u@@3) TyType)) (= (Tag (TMap t@@11 u@@3)) TagMap))
 :qid |DafnyPreludebpl.80:15|
 :skolemid |360|
 :pattern ( (TMap t@@11 u@@3))
)))
(assert (forall ((t@@12 T@U) (u@@4 T@U) ) (!  (=> (and (= (type t@@12) TyType) (= (type u@@4) TyType)) (= (Tag (TIMap t@@12 u@@4)) TagIMap))
 :qid |DafnyPreludebpl.81:15|
 :skolemid |361|
 :pattern ( (TIMap t@@12 u@@4))
)))
(assert (forall ((arg0@@29 T@U) ) (! (let ((T (type arg0@@29)))
(= (type (Lit arg0@@29)) T))
 :qid |funType:Lit|
 :pattern ( (Lit arg0@@29))
)))
(assert (forall ((x@@8 T@U) ) (! (= (Lit x@@8) x@@8)
 :qid |DafnyPreludebpl.89:29|
 :skolemid |362|
 :pattern ( (Lit x@@8))
)))
(assert  (and (= (Ctor BoxType) 13) (forall ((arg0@@30 T@U) ) (! (= (type ($Box arg0@@30)) BoxType)
 :qid |funType:$Box|
 :pattern ( ($Box arg0@@30))
))))
(assert (forall ((x@@9 T@U) ) (! (= ($Box (Lit x@@9)) (Lit ($Box x@@9)))
 :qid |DafnyPreludebpl.90:18|
 :skolemid |363|
 :pattern ( ($Box (Lit x@@9)))
)))
(assert (forall ((x@@10 Int) ) (! (= (LitInt x@@10) x@@10)
 :qid |DafnyPreludebpl.95:29|
 :skolemid |364|
 :pattern ( (LitInt x@@10))
)))
(assert (forall ((x@@11 Int) ) (! (= ($Box (int_2_U (LitInt x@@11))) (Lit ($Box (int_2_U x@@11))))
 :qid |DafnyPreludebpl.96:15|
 :skolemid |365|
 :pattern ( ($Box (int_2_U (LitInt x@@11))))
)))
(assert (forall ((x@@12 Real) ) (! (= (LitReal x@@12) x@@12)
 :qid |DafnyPreludebpl.97:30|
 :skolemid |366|
 :pattern ( (LitReal x@@12))
)))
(assert (forall ((x@@13 Real) ) (! (= ($Box (real_2_U (LitReal x@@13))) (Lit ($Box (real_2_U x@@13))))
 :qid |DafnyPreludebpl.98:15|
 :skolemid |367|
 :pattern ( ($Box (real_2_U (LitReal x@@13))))
)))
(assert  (and (= (Ctor charType) 14) (forall ((arg0@@31 Int) ) (! (= (type (|char#FromInt| arg0@@31)) charType)
 :qid |funType:char#FromInt|
 :pattern ( (|char#FromInt| arg0@@31))
))))
(assert (forall ((ch T@U) ) (!  (=> (= (type ch) charType) (and (and (= (|char#FromInt| (|char#ToInt| ch)) ch) (<= 0 (|char#ToInt| ch))) (< (|char#ToInt| ch) 65536)))
 :qid |DafnyPreludebpl.107:15|
 :skolemid |368|
 :pattern ( (|char#ToInt| ch))
)))
(assert (forall ((n Int) ) (!  (=> (and (<= 0 n) (< n 65536)) (= (|char#ToInt| (|char#FromInt| n)) n))
 :qid |DafnyPreludebpl.111:15|
 :skolemid |369|
 :pattern ( (|char#FromInt| n))
)))
(assert (forall ((arg0@@32 T@U) (arg1@@1 T@U) ) (! (= (type (|char#Plus| arg0@@32 arg1@@1)) charType)
 :qid |funType:char#Plus|
 :pattern ( (|char#Plus| arg0@@32 arg1@@1))
)))
(assert (forall ((a T@U) (b T@U) ) (!  (=> (and (= (type a) charType) (= (type b) charType)) (= (|char#Plus| a b) (|char#FromInt| (+ (|char#ToInt| a) (|char#ToInt| b)))))
 :qid |DafnyPreludebpl.117:15|
 :skolemid |370|
 :pattern ( (|char#Plus| a b))
)))
(assert (forall ((arg0@@33 T@U) (arg1@@2 T@U) ) (! (= (type (|char#Minus| arg0@@33 arg1@@2)) charType)
 :qid |funType:char#Minus|
 :pattern ( (|char#Minus| arg0@@33 arg1@@2))
)))
(assert (forall ((a@@0 T@U) (b@@0 T@U) ) (!  (=> (and (= (type a@@0) charType) (= (type b@@0) charType)) (= (|char#Minus| a@@0 b@@0) (|char#FromInt| (- (|char#ToInt| a@@0) (|char#ToInt| b@@0)))))
 :qid |DafnyPreludebpl.120:15|
 :skolemid |371|
 :pattern ( (|char#Minus| a@@0 b@@0))
)))
(assert (forall ((T@@0 T@T) (arg0@@34 T@U) ) (! (= (type ($Unbox T@@0 arg0@@34)) T@@0)
 :qid |funType:$Unbox|
 :pattern ( ($Unbox T@@0 arg0@@34))
)))
(assert (forall ((x@@14 T@U) ) (! (let ((T@@1 (type x@@14)))
(= ($Unbox T@@1 ($Box x@@14)) x@@14))
 :qid |DafnyPreludebpl.141:18|
 :skolemid |372|
 :pattern ( ($Box x@@14))
)))
(assert (forall ((bx T@U) ) (!  (=> (and (= (type bx) BoxType) ($IsBox bx TInt)) (and (= ($Box ($Unbox intType bx)) bx) ($Is ($Unbox intType bx) TInt)))
 :qid |DafnyPreludebpl.143:15|
 :skolemid |373|
 :pattern ( ($IsBox bx TInt))
)))
(assert (forall ((bx@@0 T@U) ) (!  (=> (and (= (type bx@@0) BoxType) ($IsBox bx@@0 TReal)) (and (= ($Box ($Unbox realType bx@@0)) bx@@0) ($Is ($Unbox realType bx@@0) TReal)))
 :qid |DafnyPreludebpl.146:15|
 :skolemid |374|
 :pattern ( ($IsBox bx@@0 TReal))
)))
(assert (forall ((bx@@1 T@U) ) (!  (=> (and (= (type bx@@1) BoxType) ($IsBox bx@@1 TBool)) (and (= ($Box ($Unbox boolType bx@@1)) bx@@1) ($Is ($Unbox boolType bx@@1) TBool)))
 :qid |DafnyPreludebpl.149:15|
 :skolemid |375|
 :pattern ( ($IsBox bx@@1 TBool))
)))
(assert (forall ((bx@@2 T@U) ) (!  (=> (and (= (type bx@@2) BoxType) ($IsBox bx@@2 TChar)) (and (= ($Box ($Unbox charType bx@@2)) bx@@2) ($Is ($Unbox charType bx@@2) TChar)))
 :qid |DafnyPreludebpl.152:15|
 :skolemid |376|
 :pattern ( ($IsBox bx@@2 TChar))
)))
(assert  (and (and (and (and (and (and (forall ((arg0@@35 T@T) (arg1@@3 T@T) ) (! (= (Ctor (MapType0Type arg0@@35 arg1@@3)) 15)
 :qid |ctor:MapType0Type|
)) (forall ((arg0@@36 T@T) (arg1@@4 T@T) ) (! (= (MapType0TypeInv0 (MapType0Type arg0@@36 arg1@@4)) arg0@@36)
 :qid |typeInv:MapType0TypeInv0|
 :pattern ( (MapType0Type arg0@@36 arg1@@4))
))) (forall ((arg0@@37 T@T) (arg1@@5 T@T) ) (! (= (MapType0TypeInv1 (MapType0Type arg0@@37 arg1@@5)) arg1@@5)
 :qid |typeInv:MapType0TypeInv1|
 :pattern ( (MapType0Type arg0@@37 arg1@@5))
))) (forall ((arg0@@38 T@U) (arg1@@6 T@U) ) (! (let ((aVar1 (MapType0TypeInv1 (type arg0@@38))))
(= (type (MapType0Select arg0@@38 arg1@@6)) aVar1))
 :qid |funType:MapType0Select|
 :pattern ( (MapType0Select arg0@@38 arg1@@6))
))) (forall ((arg0@@39 T@U) (arg1@@7 T@U) (arg2 T@U) ) (! (let ((aVar1@@0 (type arg2)))
(let ((aVar0 (type arg1@@7)))
(= (type (MapType0Store arg0@@39 arg1@@7 arg2)) (MapType0Type aVar0 aVar1@@0))))
 :qid |funType:MapType0Store|
 :pattern ( (MapType0Store arg0@@39 arg1@@7 arg2))
))) (forall ((m T@U) (x0 T@U) (val T@U) ) (! (let ((aVar1@@1 (MapType0TypeInv1 (type m))))
 (=> (= (type val) aVar1@@1) (= (MapType0Select (MapType0Store m x0 val) x0) val)))
 :qid |mapAx0:MapType0Select|
 :weight 0
))) (and (forall ((val@@0 T@U) (m@@0 T@U) (x0@@0 T@U) (y0 T@U) ) (!  (or (= x0@@0 y0) (= (MapType0Select (MapType0Store m@@0 x0@@0 val@@0) y0) (MapType0Select m@@0 y0)))
 :qid |mapAx1:MapType0Select:0|
 :weight 0
)) (forall ((val@@1 T@U) (m@@1 T@U) (x0@@1 T@U) (y0@@0 T@U) ) (!  (or true (= (MapType0Select (MapType0Store m@@1 x0@@1 val@@1) y0@@0) (MapType0Select m@@1 y0@@0)))
 :qid |mapAx2:MapType0Select|
 :weight 0
)))))
(assert (forall ((bx@@3 T@U) ) (!  (=> (and (= (type bx@@3) BoxType) ($IsBox bx@@3 (TBitvector 0))) (and (= ($Box ($Unbox intType bx@@3)) bx@@3) ($Is ($Unbox (MapType0Type BoxType boolType) bx@@3) (TBitvector 0))))
 :qid |DafnyPreludebpl.158:15|
 :skolemid |377|
 :pattern ( ($IsBox bx@@3 (TBitvector 0)))
)))
(assert (forall ((bx@@4 T@U) (t@@13 T@U) ) (!  (=> (and (and (= (type bx@@4) BoxType) (= (type t@@13) TyType)) ($IsBox bx@@4 (TSet t@@13))) (and (= ($Box ($Unbox (MapType0Type BoxType boolType) bx@@4)) bx@@4) ($Is ($Unbox (MapType0Type BoxType boolType) bx@@4) (TSet t@@13))))
 :qid |DafnyPreludebpl.162:15|
 :skolemid |378|
 :pattern ( ($IsBox bx@@4 (TSet t@@13)))
)))
(assert (forall ((bx@@5 T@U) (t@@14 T@U) ) (!  (=> (and (and (= (type bx@@5) BoxType) (= (type t@@14) TyType)) ($IsBox bx@@5 (TISet t@@14))) (and (= ($Box ($Unbox (MapType0Type BoxType boolType) bx@@5)) bx@@5) ($Is ($Unbox (MapType0Type BoxType boolType) bx@@5) (TISet t@@14))))
 :qid |DafnyPreludebpl.165:15|
 :skolemid |379|
 :pattern ( ($IsBox bx@@5 (TISet t@@14)))
)))
(assert (forall ((bx@@6 T@U) (t@@15 T@U) ) (!  (=> (and (and (= (type bx@@6) BoxType) (= (type t@@15) TyType)) ($IsBox bx@@6 (TMultiSet t@@15))) (and (= ($Box ($Unbox (MapType0Type BoxType intType) bx@@6)) bx@@6) ($Is ($Unbox (MapType0Type BoxType intType) bx@@6) (TMultiSet t@@15))))
 :qid |DafnyPreludebpl.168:15|
 :skolemid |380|
 :pattern ( ($IsBox bx@@6 (TMultiSet t@@15)))
)))
(assert  (and (forall ((arg0@@40 T@T) ) (! (= (Ctor (SeqType arg0@@40)) 16)
 :qid |ctor:SeqType|
)) (forall ((arg0@@41 T@T) ) (! (= (SeqTypeInv0 (SeqType arg0@@41)) arg0@@41)
 :qid |typeInv:SeqTypeInv0|
 :pattern ( (SeqType arg0@@41))
))))
(assert (forall ((bx@@7 T@U) (t@@16 T@U) ) (!  (=> (and (and (= (type bx@@7) BoxType) (= (type t@@16) TyType)) ($IsBox bx@@7 (TSeq t@@16))) (and (= ($Box ($Unbox (SeqType BoxType) bx@@7)) bx@@7) ($Is ($Unbox (SeqType BoxType) bx@@7) (TSeq t@@16))))
 :qid |DafnyPreludebpl.171:15|
 :skolemid |381|
 :pattern ( ($IsBox bx@@7 (TSeq t@@16)))
)))
(assert  (and (and (forall ((arg0@@42 T@T) (arg1@@8 T@T) ) (! (= (Ctor (MapType arg0@@42 arg1@@8)) 17)
 :qid |ctor:MapType|
)) (forall ((arg0@@43 T@T) (arg1@@9 T@T) ) (! (= (MapTypeInv0 (MapType arg0@@43 arg1@@9)) arg0@@43)
 :qid |typeInv:MapTypeInv0|
 :pattern ( (MapType arg0@@43 arg1@@9))
))) (forall ((arg0@@44 T@T) (arg1@@10 T@T) ) (! (= (MapTypeInv1 (MapType arg0@@44 arg1@@10)) arg1@@10)
 :qid |typeInv:MapTypeInv1|
 :pattern ( (MapType arg0@@44 arg1@@10))
))))
(assert (forall ((bx@@8 T@U) (s T@U) (t@@17 T@U) ) (!  (=> (and (and (and (= (type bx@@8) BoxType) (= (type s) TyType)) (= (type t@@17) TyType)) ($IsBox bx@@8 (TMap s t@@17))) (and (= ($Box ($Unbox (MapType BoxType BoxType) bx@@8)) bx@@8) ($Is ($Unbox (MapType BoxType BoxType) bx@@8) (TMap s t@@17))))
 :qid |DafnyPreludebpl.174:15|
 :skolemid |382|
 :pattern ( ($IsBox bx@@8 (TMap s t@@17)))
)))
(assert  (and (and (forall ((arg0@@45 T@T) (arg1@@11 T@T) ) (! (= (Ctor (IMapType arg0@@45 arg1@@11)) 18)
 :qid |ctor:IMapType|
)) (forall ((arg0@@46 T@T) (arg1@@12 T@T) ) (! (= (IMapTypeInv0 (IMapType arg0@@46 arg1@@12)) arg0@@46)
 :qid |typeInv:IMapTypeInv0|
 :pattern ( (IMapType arg0@@46 arg1@@12))
))) (forall ((arg0@@47 T@T) (arg1@@13 T@T) ) (! (= (IMapTypeInv1 (IMapType arg0@@47 arg1@@13)) arg1@@13)
 :qid |typeInv:IMapTypeInv1|
 :pattern ( (IMapType arg0@@47 arg1@@13))
))))
(assert (forall ((bx@@9 T@U) (s@@0 T@U) (t@@18 T@U) ) (!  (=> (and (and (and (= (type bx@@9) BoxType) (= (type s@@0) TyType)) (= (type t@@18) TyType)) ($IsBox bx@@9 (TIMap s@@0 t@@18))) (and (= ($Box ($Unbox (IMapType BoxType BoxType) bx@@9)) bx@@9) ($Is ($Unbox (IMapType BoxType BoxType) bx@@9) (TIMap s@@0 t@@18))))
 :qid |DafnyPreludebpl.177:15|
 :skolemid |383|
 :pattern ( ($IsBox bx@@9 (TIMap s@@0 t@@18)))
)))
(assert (forall ((v T@U) (t@@19 T@U) ) (!  (=> (= (type t@@19) TyType) (= ($IsBox ($Box v) t@@19) ($Is v t@@19)))
 :qid |DafnyPreludebpl.181:18|
 :skolemid |384|
 :pattern ( ($IsBox ($Box v) t@@19))
)))
(assert  (and (and (and (and (and (forall ((arg0@@48 T@U) (arg1@@14 T@U) ) (! (let ((alpha@@1 (FieldTypeInv0 (type arg1@@14))))
(= (type (MapType1Select arg0@@48 arg1@@14)) alpha@@1))
 :qid |funType:MapType1Select|
 :pattern ( (MapType1Select arg0@@48 arg1@@14))
)) (= (Ctor MapType1Type) 19)) (forall ((arg0@@49 T@U) (arg1@@15 T@U) (arg2@@0 T@U) ) (! (= (type (MapType1Store arg0@@49 arg1@@15 arg2@@0)) MapType1Type)
 :qid |funType:MapType1Store|
 :pattern ( (MapType1Store arg0@@49 arg1@@15 arg2@@0))
))) (forall ((m@@2 T@U) (x0@@2 T@U) (val@@2 T@U) ) (! (let ((alpha@@2 (FieldTypeInv0 (type x0@@2))))
 (=> (= (type val@@2) alpha@@2) (= (MapType1Select (MapType1Store m@@2 x0@@2 val@@2) x0@@2) val@@2)))
 :qid |mapAx0:MapType1Select|
 :weight 0
))) (and (forall ((val@@3 T@U) (m@@3 T@U) (x0@@3 T@U) (y0@@1 T@U) ) (!  (or (= x0@@3 y0@@1) (= (MapType1Select (MapType1Store m@@3 x0@@3 val@@3) y0@@1) (MapType1Select m@@3 y0@@1)))
 :qid |mapAx1:MapType1Select:0|
 :weight 0
)) (forall ((val@@4 T@U) (m@@4 T@U) (x0@@4 T@U) (y0@@2 T@U) ) (!  (or true (= (MapType1Select (MapType1Store m@@4 x0@@4 val@@4) y0@@2) (MapType1Select m@@4 y0@@2)))
 :qid |mapAx2:MapType1Select|
 :weight 0
)))) (= (Ctor refType) 20)))
(assert (forall ((v@@0 T@U) (t@@20 T@U) (h T@U) ) (!  (=> (and (= (type t@@20) TyType) (= (type h) (MapType0Type refType MapType1Type))) (= ($IsAllocBox ($Box v@@0) t@@20 h) ($IsAlloc v@@0 t@@20 h)))
 :qid |DafnyPreludebpl.184:18|
 :skolemid |385|
 :pattern ( ($IsAllocBox ($Box v@@0) t@@20 h))
)))
(assert (forall ((v@@1 T@U) ) (!  (=> (= (type v@@1) intType) ($Is v@@1 TInt))
 :qid |DafnyPreludebpl.202:14|
 :skolemid |386|
 :pattern ( ($Is v@@1 TInt))
)))
(assert (forall ((v@@2 T@U) ) (!  (=> (= (type v@@2) realType) ($Is v@@2 TReal))
 :qid |DafnyPreludebpl.203:14|
 :skolemid |387|
 :pattern ( ($Is v@@2 TReal))
)))
(assert (forall ((v@@3 T@U) ) (!  (=> (= (type v@@3) boolType) ($Is v@@3 TBool))
 :qid |DafnyPreludebpl.204:14|
 :skolemid |388|
 :pattern ( ($Is v@@3 TBool))
)))
(assert (forall ((v@@4 T@U) ) (!  (=> (= (type v@@4) charType) ($Is v@@4 TChar))
 :qid |DafnyPreludebpl.205:14|
 :skolemid |389|
 :pattern ( ($Is v@@4 TChar))
)))
(assert (forall ((v@@5 T@U) ) (!  (=> (= (type v@@5) BoxType) ($Is v@@5 TORDINAL))
 :qid |DafnyPreludebpl.206:14|
 :skolemid |390|
 :pattern ( ($Is v@@5 TORDINAL))
)))
(assert (forall ((h@@0 T@U) (v@@6 T@U) ) (!  (=> (and (= (type h@@0) (MapType0Type refType MapType1Type)) (= (type v@@6) intType)) ($IsAlloc v@@6 TInt h@@0))
 :qid |DafnyPreludebpl.208:14|
 :skolemid |391|
 :pattern ( ($IsAlloc v@@6 TInt h@@0))
)))
(assert (forall ((h@@1 T@U) (v@@7 T@U) ) (!  (=> (and (= (type h@@1) (MapType0Type refType MapType1Type)) (= (type v@@7) realType)) ($IsAlloc v@@7 TReal h@@1))
 :qid |DafnyPreludebpl.209:14|
 :skolemid |392|
 :pattern ( ($IsAlloc v@@7 TReal h@@1))
)))
(assert (forall ((h@@2 T@U) (v@@8 T@U) ) (!  (=> (and (= (type h@@2) (MapType0Type refType MapType1Type)) (= (type v@@8) boolType)) ($IsAlloc v@@8 TBool h@@2))
 :qid |DafnyPreludebpl.210:14|
 :skolemid |393|
 :pattern ( ($IsAlloc v@@8 TBool h@@2))
)))
(assert (forall ((h@@3 T@U) (v@@9 T@U) ) (!  (=> (and (= (type h@@3) (MapType0Type refType MapType1Type)) (= (type v@@9) charType)) ($IsAlloc v@@9 TChar h@@3))
 :qid |DafnyPreludebpl.211:14|
 :skolemid |394|
 :pattern ( ($IsAlloc v@@9 TChar h@@3))
)))
(assert (forall ((h@@4 T@U) (v@@10 T@U) ) (!  (=> (and (= (type h@@4) (MapType0Type refType MapType1Type)) (= (type v@@10) BoxType)) ($IsAlloc v@@10 TORDINAL h@@4))
 :qid |DafnyPreludebpl.212:14|
 :skolemid |395|
 :pattern ( ($IsAlloc v@@10 TORDINAL h@@4))
)))
(assert (forall ((v@@11 T@U) ) (!  (=> (= (type v@@11) intType) ($Is v@@11 (TBitvector 0)))
 :qid |DafnyPreludebpl.216:15|
 :skolemid |396|
 :pattern ( ($Is v@@11 (TBitvector 0)))
)))
(assert (forall ((v@@12 T@U) (h@@5 T@U) ) (!  (=> (and (= (type v@@12) intType) (= (type h@@5) (MapType0Type refType MapType1Type))) ($IsAlloc v@@12 (TBitvector 0) h@@5))
 :qid |DafnyPreludebpl.217:15|
 :skolemid |397|
 :pattern ( ($IsAlloc v@@12 (TBitvector 0) h@@5))
)))
(assert (forall ((v@@13 T@U) (t0 T@U) ) (!  (=> (and (= (type v@@13) (MapType0Type BoxType boolType)) (= (type t0) TyType)) (= ($Is v@@13 (TSet t0)) (forall ((bx@@10 T@U) ) (!  (=> (and (= (type bx@@10) BoxType) (U_2_bool (MapType0Select v@@13 bx@@10))) ($IsBox bx@@10 t0))
 :qid |DafnyPreludebpl.221:11|
 :skolemid |398|
 :pattern ( (MapType0Select v@@13 bx@@10))
))))
 :qid |DafnyPreludebpl.219:15|
 :skolemid |399|
 :pattern ( ($Is v@@13 (TSet t0)))
)))
(assert (forall ((v@@14 T@U) (t0@@0 T@U) ) (!  (=> (and (= (type v@@14) (MapType0Type BoxType boolType)) (= (type t0@@0) TyType)) (= ($Is v@@14 (TISet t0@@0)) (forall ((bx@@11 T@U) ) (!  (=> (and (= (type bx@@11) BoxType) (U_2_bool (MapType0Select v@@14 bx@@11))) ($IsBox bx@@11 t0@@0))
 :qid |DafnyPreludebpl.225:11|
 :skolemid |400|
 :pattern ( (MapType0Select v@@14 bx@@11))
))))
 :qid |DafnyPreludebpl.223:15|
 :skolemid |401|
 :pattern ( ($Is v@@14 (TISet t0@@0)))
)))
(assert (forall ((v@@15 T@U) (t0@@1 T@U) ) (!  (=> (and (= (type v@@15) (MapType0Type BoxType intType)) (= (type t0@@1) TyType)) (= ($Is v@@15 (TMultiSet t0@@1)) (forall ((bx@@12 T@U) ) (!  (=> (and (= (type bx@@12) BoxType) (< 0 (U_2_int (MapType0Select v@@15 bx@@12)))) ($IsBox bx@@12 t0@@1))
 :qid |DafnyPreludebpl.229:11|
 :skolemid |402|
 :pattern ( (MapType0Select v@@15 bx@@12))
))))
 :qid |DafnyPreludebpl.227:15|
 :skolemid |403|
 :pattern ( ($Is v@@15 (TMultiSet t0@@1)))
)))
(assert (forall ((v@@16 T@U) (t0@@2 T@U) ) (!  (=> (and (and (= (type v@@16) (MapType0Type BoxType intType)) (= (type t0@@2) TyType)) ($Is v@@16 (TMultiSet t0@@2))) ($IsGoodMultiSet v@@16))
 :qid |DafnyPreludebpl.231:15|
 :skolemid |404|
 :pattern ( ($Is v@@16 (TMultiSet t0@@2)))
)))
(assert (forall ((arg0@@50 T@U) (arg1@@16 Int) ) (! (let ((T@@2 (SeqTypeInv0 (type arg0@@50))))
(= (type (|Seq#Index| arg0@@50 arg1@@16)) T@@2))
 :qid |funType:Seq#Index|
 :pattern ( (|Seq#Index| arg0@@50 arg1@@16))
)))
(assert (forall ((v@@17 T@U) (t0@@3 T@U) ) (!  (=> (and (= (type v@@17) (SeqType BoxType)) (= (type t0@@3) TyType)) (= ($Is v@@17 (TSeq t0@@3)) (forall ((i Int) ) (!  (=> (and (<= 0 i) (< i (|Seq#Length| v@@17))) ($IsBox (|Seq#Index| v@@17 i) t0@@3))
 :qid |DafnyPreludebpl.235:11|
 :skolemid |405|
 :pattern ( (|Seq#Index| v@@17 i))
))))
 :qid |DafnyPreludebpl.233:15|
 :skolemid |406|
 :pattern ( ($Is v@@17 (TSeq t0@@3)))
)))
(assert (forall ((v@@18 T@U) (t0@@4 T@U) (h@@6 T@U) ) (!  (=> (and (and (= (type v@@18) (MapType0Type BoxType boolType)) (= (type t0@@4) TyType)) (= (type h@@6) (MapType0Type refType MapType1Type))) (= ($IsAlloc v@@18 (TSet t0@@4) h@@6) (forall ((bx@@13 T@U) ) (!  (=> (and (= (type bx@@13) BoxType) (U_2_bool (MapType0Select v@@18 bx@@13))) ($IsAllocBox bx@@13 t0@@4 h@@6))
 :qid |DafnyPreludebpl.240:11|
 :skolemid |407|
 :pattern ( (MapType0Select v@@18 bx@@13))
))))
 :qid |DafnyPreludebpl.238:15|
 :skolemid |408|
 :pattern ( ($IsAlloc v@@18 (TSet t0@@4) h@@6))
)))
(assert (forall ((v@@19 T@U) (t0@@5 T@U) (h@@7 T@U) ) (!  (=> (and (and (= (type v@@19) (MapType0Type BoxType boolType)) (= (type t0@@5) TyType)) (= (type h@@7) (MapType0Type refType MapType1Type))) (= ($IsAlloc v@@19 (TISet t0@@5) h@@7) (forall ((bx@@14 T@U) ) (!  (=> (and (= (type bx@@14) BoxType) (U_2_bool (MapType0Select v@@19 bx@@14))) ($IsAllocBox bx@@14 t0@@5 h@@7))
 :qid |DafnyPreludebpl.244:11|
 :skolemid |409|
 :pattern ( (MapType0Select v@@19 bx@@14))
))))
 :qid |DafnyPreludebpl.242:15|
 :skolemid |410|
 :pattern ( ($IsAlloc v@@19 (TISet t0@@5) h@@7))
)))
(assert (forall ((v@@20 T@U) (t0@@6 T@U) (h@@8 T@U) ) (!  (=> (and (and (= (type v@@20) (MapType0Type BoxType intType)) (= (type t0@@6) TyType)) (= (type h@@8) (MapType0Type refType MapType1Type))) (= ($IsAlloc v@@20 (TMultiSet t0@@6) h@@8) (forall ((bx@@15 T@U) ) (!  (=> (and (= (type bx@@15) BoxType) (< 0 (U_2_int (MapType0Select v@@20 bx@@15)))) ($IsAllocBox bx@@15 t0@@6 h@@8))
 :qid |DafnyPreludebpl.248:11|
 :skolemid |411|
 :pattern ( (MapType0Select v@@20 bx@@15))
))))
 :qid |DafnyPreludebpl.246:15|
 :skolemid |412|
 :pattern ( ($IsAlloc v@@20 (TMultiSet t0@@6) h@@8))
)))
(assert (forall ((v@@21 T@U) (t0@@7 T@U) (h@@9 T@U) ) (!  (=> (and (and (= (type v@@21) (SeqType BoxType)) (= (type t0@@7) TyType)) (= (type h@@9) (MapType0Type refType MapType1Type))) (= ($IsAlloc v@@21 (TSeq t0@@7) h@@9) (forall ((i@@0 Int) ) (!  (=> (and (<= 0 i@@0) (< i@@0 (|Seq#Length| v@@21))) ($IsAllocBox (|Seq#Index| v@@21 i@@0) t0@@7 h@@9))
 :qid |DafnyPreludebpl.252:11|
 :skolemid |413|
 :pattern ( (|Seq#Index| v@@21 i@@0))
))))
 :qid |DafnyPreludebpl.250:15|
 :skolemid |414|
 :pattern ( ($IsAlloc v@@21 (TSeq t0@@7) h@@9))
)))
(assert  (and (forall ((arg0@@51 T@U) ) (! (let ((V (MapTypeInv1 (type arg0@@51))))
(let ((U (MapTypeInv0 (type arg0@@51))))
(= (type (|Map#Elements| arg0@@51)) (MapType0Type U V))))
 :qid |funType:Map#Elements|
 :pattern ( (|Map#Elements| arg0@@51))
)) (forall ((arg0@@52 T@U) ) (! (let ((U@@0 (MapTypeInv0 (type arg0@@52))))
(= (type (|Map#Domain| arg0@@52)) (MapType0Type U@@0 boolType)))
 :qid |funType:Map#Domain|
 :pattern ( (|Map#Domain| arg0@@52))
))))
(assert (forall ((v@@22 T@U) (t0@@8 T@U) (t1 T@U) ) (!  (=> (and (and (= (type v@@22) (MapType BoxType BoxType)) (= (type t0@@8) TyType)) (= (type t1) TyType)) (= ($Is v@@22 (TMap t0@@8 t1)) (forall ((bx@@16 T@U) ) (!  (=> (and (= (type bx@@16) BoxType) (U_2_bool (MapType0Select (|Map#Domain| v@@22) bx@@16))) (and ($IsBox (MapType0Select (|Map#Elements| v@@22) bx@@16) t1) ($IsBox bx@@16 t0@@8)))
 :qid |DafnyPreludebpl.259:19|
 :skolemid |415|
 :pattern ( (MapType0Select (|Map#Elements| v@@22) bx@@16))
 :pattern ( (MapType0Select (|Map#Domain| v@@22) bx@@16))
))))
 :qid |DafnyPreludebpl.256:15|
 :skolemid |416|
 :pattern ( ($Is v@@22 (TMap t0@@8 t1)))
)))
(assert (forall ((v@@23 T@U) (t0@@9 T@U) (t1@@0 T@U) (h@@10 T@U) ) (!  (=> (and (and (and (= (type v@@23) (MapType BoxType BoxType)) (= (type t0@@9) TyType)) (= (type t1@@0) TyType)) (= (type h@@10) (MapType0Type refType MapType1Type))) (= ($IsAlloc v@@23 (TMap t0@@9 t1@@0) h@@10) (forall ((bx@@17 T@U) ) (!  (=> (and (= (type bx@@17) BoxType) (U_2_bool (MapType0Select (|Map#Domain| v@@23) bx@@17))) (and ($IsAllocBox (MapType0Select (|Map#Elements| v@@23) bx@@17) t1@@0 h@@10) ($IsAllocBox bx@@17 t0@@9 h@@10)))
 :qid |DafnyPreludebpl.267:19|
 :skolemid |417|
 :pattern ( (MapType0Select (|Map#Elements| v@@23) bx@@17))
 :pattern ( (MapType0Select (|Map#Domain| v@@23) bx@@17))
))))
 :qid |DafnyPreludebpl.264:15|
 :skolemid |418|
 :pattern ( ($IsAlloc v@@23 (TMap t0@@9 t1@@0) h@@10))
)))
(assert  (and (and (forall ((arg0@@53 T@U) ) (! (let ((V@@0 (MapTypeInv1 (type arg0@@53))))
(= (type (|Map#Values| arg0@@53)) (MapType0Type V@@0 boolType)))
 :qid |funType:Map#Values|
 :pattern ( (|Map#Values| arg0@@53))
)) (forall ((arg0@@54 T@U) ) (! (= (type (|Map#Items| arg0@@54)) (MapType0Type BoxType boolType))
 :qid |funType:Map#Items|
 :pattern ( (|Map#Items| arg0@@54))
))) (forall ((arg0@@55 T@U) (arg1@@17 T@U) ) (! (= (type (Tclass._System.Tuple2 arg0@@55 arg1@@17)) TyType)
 :qid |funType:Tclass._System.Tuple2|
 :pattern ( (Tclass._System.Tuple2 arg0@@55 arg1@@17))
))))
(assert (forall ((v@@24 T@U) (t0@@10 T@U) (t1@@1 T@U) ) (!  (=> (and (and (and (= (type v@@24) (MapType BoxType BoxType)) (= (type t0@@10) TyType)) (= (type t1@@1) TyType)) ($Is v@@24 (TMap t0@@10 t1@@1))) (and (and ($Is (|Map#Domain| v@@24) (TSet t0@@10)) ($Is (|Map#Values| v@@24) (TSet t1@@1))) ($Is (|Map#Items| v@@24) (TSet (Tclass._System.Tuple2 t0@@10 t1@@1)))))
 :qid |DafnyPreludebpl.272:15|
 :skolemid |419|
 :pattern ( ($Is v@@24 (TMap t0@@10 t1@@1)))
)))
(assert  (and (forall ((arg0@@56 T@U) ) (! (let ((V@@1 (IMapTypeInv1 (type arg0@@56))))
(let ((U@@1 (IMapTypeInv0 (type arg0@@56))))
(= (type (|IMap#Elements| arg0@@56)) (MapType0Type U@@1 V@@1))))
 :qid |funType:IMap#Elements|
 :pattern ( (|IMap#Elements| arg0@@56))
)) (forall ((arg0@@57 T@U) ) (! (let ((U@@2 (IMapTypeInv0 (type arg0@@57))))
(= (type (|IMap#Domain| arg0@@57)) (MapType0Type U@@2 boolType)))
 :qid |funType:IMap#Domain|
 :pattern ( (|IMap#Domain| arg0@@57))
))))
(assert (forall ((v@@25 T@U) (t0@@11 T@U) (t1@@2 T@U) ) (!  (=> (and (and (= (type v@@25) (IMapType BoxType BoxType)) (= (type t0@@11) TyType)) (= (type t1@@2) TyType)) (= ($Is v@@25 (TIMap t0@@11 t1@@2)) (forall ((bx@@18 T@U) ) (!  (=> (and (= (type bx@@18) BoxType) (U_2_bool (MapType0Select (|IMap#Domain| v@@25) bx@@18))) (and ($IsBox (MapType0Select (|IMap#Elements| v@@25) bx@@18) t1@@2) ($IsBox bx@@18 t0@@11)))
 :qid |DafnyPreludebpl.282:19|
 :skolemid |420|
 :pattern ( (MapType0Select (|IMap#Elements| v@@25) bx@@18))
 :pattern ( (MapType0Select (|IMap#Domain| v@@25) bx@@18))
))))
 :qid |DafnyPreludebpl.279:15|
 :skolemid |421|
 :pattern ( ($Is v@@25 (TIMap t0@@11 t1@@2)))
)))
(assert (forall ((v@@26 T@U) (t0@@12 T@U) (t1@@3 T@U) (h@@11 T@U) ) (!  (=> (and (and (and (= (type v@@26) (IMapType BoxType BoxType)) (= (type t0@@12) TyType)) (= (type t1@@3) TyType)) (= (type h@@11) (MapType0Type refType MapType1Type))) (= ($IsAlloc v@@26 (TIMap t0@@12 t1@@3) h@@11) (forall ((bx@@19 T@U) ) (!  (=> (and (= (type bx@@19) BoxType) (U_2_bool (MapType0Select (|IMap#Domain| v@@26) bx@@19))) (and ($IsAllocBox (MapType0Select (|IMap#Elements| v@@26) bx@@19) t1@@3 h@@11) ($IsAllocBox bx@@19 t0@@12 h@@11)))
 :qid |DafnyPreludebpl.290:19|
 :skolemid |422|
 :pattern ( (MapType0Select (|IMap#Elements| v@@26) bx@@19))
 :pattern ( (MapType0Select (|IMap#Domain| v@@26) bx@@19))
))))
 :qid |DafnyPreludebpl.287:15|
 :skolemid |423|
 :pattern ( ($IsAlloc v@@26 (TIMap t0@@12 t1@@3) h@@11))
)))
(assert  (and (forall ((arg0@@58 T@U) ) (! (let ((V@@2 (IMapTypeInv1 (type arg0@@58))))
(= (type (|IMap#Values| arg0@@58)) (MapType0Type V@@2 boolType)))
 :qid |funType:IMap#Values|
 :pattern ( (|IMap#Values| arg0@@58))
)) (forall ((arg0@@59 T@U) ) (! (= (type (|IMap#Items| arg0@@59)) (MapType0Type BoxType boolType))
 :qid |funType:IMap#Items|
 :pattern ( (|IMap#Items| arg0@@59))
))))
(assert (forall ((v@@27 T@U) (t0@@13 T@U) (t1@@4 T@U) ) (!  (=> (and (and (and (= (type v@@27) (IMapType BoxType BoxType)) (= (type t0@@13) TyType)) (= (type t1@@4) TyType)) ($Is v@@27 (TIMap t0@@13 t1@@4))) (and (and ($Is (|IMap#Domain| v@@27) (TISet t0@@13)) ($Is (|IMap#Values| v@@27) (TISet t1@@4))) ($Is (|IMap#Items| v@@27) (TISet (Tclass._System.Tuple2 t0@@13 t1@@4)))))
 :qid |DafnyPreludebpl.295:15|
 :skolemid |424|
 :pattern ( ($Is v@@27 (TIMap t0@@13 t1@@4)))
)))
(assert  (and (and (forall ((arg0@@60 T@U) (arg1@@18 T@U) ) (! (= (type (TypeTuple arg0@@60 arg1@@18)) ClassNameType)
 :qid |funType:TypeTuple|
 :pattern ( (TypeTuple arg0@@60 arg1@@18))
)) (forall ((arg0@@61 T@U) ) (! (= (type (TypeTupleCar arg0@@61)) ClassNameType)
 :qid |funType:TypeTupleCar|
 :pattern ( (TypeTupleCar arg0@@61))
))) (forall ((arg0@@62 T@U) ) (! (= (type (TypeTupleCdr arg0@@62)) ClassNameType)
 :qid |funType:TypeTupleCdr|
 :pattern ( (TypeTupleCdr arg0@@62))
))))
(assert (forall ((a@@1 T@U) (b@@1 T@U) ) (!  (=> (and (= (type a@@1) ClassNameType) (= (type b@@1) ClassNameType)) (and (= (TypeTupleCar (TypeTuple a@@1 b@@1)) a@@1) (= (TypeTupleCdr (TypeTuple a@@1 b@@1)) b@@1)))
 :qid |DafnyPreludebpl.322:15|
 :skolemid |425|
 :pattern ( (TypeTuple a@@1 b@@1))
)))
(assert (forall ((arg0@@63 T@U) ) (! (= (type (SetRef_to_SetBox arg0@@63)) (MapType0Type BoxType boolType))
 :qid |funType:SetRef_to_SetBox|
 :pattern ( (SetRef_to_SetBox arg0@@63))
)))
(assert (forall ((s@@1 T@U) (bx@@20 T@U) ) (!  (=> (and (= (type s@@1) (MapType0Type refType boolType)) (= (type bx@@20) BoxType)) (= (U_2_bool (MapType0Select (SetRef_to_SetBox s@@1) bx@@20)) (U_2_bool (MapType0Select s@@1 ($Unbox refType bx@@20)))))
 :qid |DafnyPreludebpl.331:15|
 :skolemid |426|
 :pattern ( (MapType0Select (SetRef_to_SetBox s@@1) bx@@20))
)))
(assert (= (type Tclass._System.object?) TyType))
(assert (forall ((s@@2 T@U) ) (!  (=> (= (type s@@2) (MapType0Type refType boolType)) ($Is (SetRef_to_SetBox s@@2) (TSet Tclass._System.object?)))
 :qid |DafnyPreludebpl.333:15|
 :skolemid |427|
 :pattern ( (SetRef_to_SetBox s@@2))
)))
(assert (= (Ctor DatatypeTypeType) 21))
(assert (forall ((d T@U) ) (!  (=> (= (type d) DatatypeTypeType) (= (BoxRank ($Box d)) (DtRank d)))
 :qid |DafnyPreludebpl.352:15|
 :skolemid |428|
 :pattern ( (BoxRank ($Box d)))
)))
(assert (forall ((o T@U) ) (!  (=> (= (type o) BoxType) (<= 0 (|ORD#Offset| o)))
 :qid |DafnyPreludebpl.367:15|
 :skolemid |429|
 :pattern ( (|ORD#Offset| o))
)))
(assert (forall ((arg0@@64 Int) ) (! (= (type (|ORD#FromNat| arg0@@64)) BoxType)
 :qid |funType:ORD#FromNat|
 :pattern ( (|ORD#FromNat| arg0@@64))
)))
(assert (forall ((n@@0 Int) ) (!  (=> (<= 0 n@@0) (and (|ORD#IsNat| (|ORD#FromNat| n@@0)) (= (|ORD#Offset| (|ORD#FromNat| n@@0)) n@@0)))
 :qid |DafnyPreludebpl.373:15|
 :skolemid |430|
 :pattern ( (|ORD#FromNat| n@@0))
)))
(assert (forall ((o@@0 T@U) ) (!  (=> (and (= (type o@@0) BoxType) (|ORD#IsNat| o@@0)) (= o@@0 (|ORD#FromNat| (|ORD#Offset| o@@0))))
 :qid |DafnyPreludebpl.375:15|
 :skolemid |431|
 :pattern ( (|ORD#Offset| o@@0))
 :pattern ( (|ORD#IsNat| o@@0))
)))
(assert (forall ((o@@1 T@U) (p T@U) ) (!  (=> (and (= (type o@@1) BoxType) (= (type p) BoxType)) (and (and (and (=> (|ORD#Less| o@@1 p) (not (= o@@1 p))) (=> (and (|ORD#IsNat| o@@1) (not (|ORD#IsNat| p))) (|ORD#Less| o@@1 p))) (=> (and (|ORD#IsNat| o@@1) (|ORD#IsNat| p)) (= (|ORD#Less| o@@1 p) (< (|ORD#Offset| o@@1) (|ORD#Offset| p))))) (=> (and (|ORD#Less| o@@1 p) (|ORD#IsNat| p)) (|ORD#IsNat| o@@1))))
 :qid |DafnyPreludebpl.379:15|
 :skolemid |432|
 :pattern ( (|ORD#Less| o@@1 p))
)))
(assert (forall ((o@@2 T@U) (p@@0 T@U) ) (!  (=> (and (= (type o@@2) BoxType) (= (type p@@0) BoxType)) (or (or (|ORD#Less| o@@2 p@@0) (= o@@2 p@@0)) (|ORD#Less| p@@0 o@@2)))
 :qid |DafnyPreludebpl.385:15|
 :skolemid |433|
 :pattern ( (|ORD#Less| o@@2 p@@0) (|ORD#Less| p@@0 o@@2))
)))
(assert (forall ((o@@3 T@U) (p@@1 T@U) (r T@U) ) (!  (=> (and (and (and (= (type o@@3) BoxType) (= (type p@@1) BoxType)) (= (type r) BoxType)) (and (|ORD#Less| o@@3 p@@1) (|ORD#Less| p@@1 r))) (|ORD#Less| o@@3 r))
 :qid |DafnyPreludebpl.388:15|
 :skolemid |434|
 :pattern ( (|ORD#Less| o@@3 p@@1) (|ORD#Less| p@@1 r))
 :pattern ( (|ORD#Less| o@@3 p@@1) (|ORD#Less| o@@3 r))
)))
(assert (forall ((o@@4 T@U) (p@@2 T@U) ) (!  (=> (and (= (type o@@4) BoxType) (= (type p@@2) BoxType)) (= (|ORD#LessThanLimit| o@@4 p@@2) (|ORD#Less| o@@4 p@@2)))
 :qid |DafnyPreludebpl.395:15|
 :skolemid |435|
 :pattern ( (|ORD#LessThanLimit| o@@4 p@@2))
)))
(assert (forall ((arg0@@65 T@U) (arg1@@19 T@U) ) (! (= (type (|ORD#Plus| arg0@@65 arg1@@19)) BoxType)
 :qid |funType:ORD#Plus|
 :pattern ( (|ORD#Plus| arg0@@65 arg1@@19))
)))
(assert (forall ((o@@5 T@U) (p@@3 T@U) ) (!  (=> (and (= (type o@@5) BoxType) (= (type p@@3) BoxType)) (and (=> (|ORD#IsNat| (|ORD#Plus| o@@5 p@@3)) (and (|ORD#IsNat| o@@5) (|ORD#IsNat| p@@3))) (=> (|ORD#IsNat| p@@3) (and (= (|ORD#IsNat| (|ORD#Plus| o@@5 p@@3)) (|ORD#IsNat| o@@5)) (= (|ORD#Offset| (|ORD#Plus| o@@5 p@@3)) (+ (|ORD#Offset| o@@5) (|ORD#Offset| p@@3)))))))
 :qid |DafnyPreludebpl.399:15|
 :skolemid |436|
 :pattern ( (|ORD#Plus| o@@5 p@@3))
)))
(assert (forall ((o@@6 T@U) (p@@4 T@U) ) (!  (=> (and (= (type o@@6) BoxType) (= (type p@@4) BoxType)) (and (or (= o@@6 (|ORD#Plus| o@@6 p@@4)) (|ORD#Less| o@@6 (|ORD#Plus| o@@6 p@@4))) (or (= p@@4 (|ORD#Plus| o@@6 p@@4)) (|ORD#Less| p@@4 (|ORD#Plus| o@@6 p@@4)))))
 :qid |DafnyPreludebpl.404:15|
 :skolemid |437|
 :pattern ( (|ORD#Plus| o@@6 p@@4))
)))
(assert (forall ((o@@7 T@U) (p@@5 T@U) ) (!  (=> (and (= (type o@@7) BoxType) (= (type p@@5) BoxType)) (and (=> (= o@@7 (|ORD#FromNat| 0)) (= (|ORD#Plus| o@@7 p@@5) p@@5)) (=> (= p@@5 (|ORD#FromNat| 0)) (= (|ORD#Plus| o@@7 p@@5) o@@7))))
 :qid |DafnyPreludebpl.407:15|
 :skolemid |438|
 :pattern ( (|ORD#Plus| o@@7 p@@5))
)))
(assert (forall ((arg0@@66 T@U) (arg1@@20 T@U) ) (! (= (type (|ORD#Minus| arg0@@66 arg1@@20)) BoxType)
 :qid |funType:ORD#Minus|
 :pattern ( (|ORD#Minus| arg0@@66 arg1@@20))
)))
(assert (forall ((o@@8 T@U) (p@@6 T@U) ) (!  (=> (and (and (= (type o@@8) BoxType) (= (type p@@6) BoxType)) (and (|ORD#IsNat| p@@6) (<= (|ORD#Offset| p@@6) (|ORD#Offset| o@@8)))) (and (= (|ORD#IsNat| (|ORD#Minus| o@@8 p@@6)) (|ORD#IsNat| o@@8)) (= (|ORD#Offset| (|ORD#Minus| o@@8 p@@6)) (- (|ORD#Offset| o@@8) (|ORD#Offset| p@@6)))))
 :qid |DafnyPreludebpl.412:15|
 :skolemid |439|
 :pattern ( (|ORD#Minus| o@@8 p@@6))
)))
(assert (forall ((o@@9 T@U) (p@@7 T@U) ) (!  (=> (and (and (= (type o@@9) BoxType) (= (type p@@7) BoxType)) (and (|ORD#IsNat| p@@7) (<= (|ORD#Offset| p@@7) (|ORD#Offset| o@@9)))) (or (and (= p@@7 (|ORD#FromNat| 0)) (= (|ORD#Minus| o@@9 p@@7) o@@9)) (and (not (= p@@7 (|ORD#FromNat| 0))) (|ORD#Less| (|ORD#Minus| o@@9 p@@7) o@@9))))
 :qid |DafnyPreludebpl.416:15|
 :skolemid |440|
 :pattern ( (|ORD#Minus| o@@9 p@@7))
)))
(assert (forall ((o@@10 T@U) (m@@5 Int) (n@@1 Int) ) (!  (=> (= (type o@@10) BoxType) (=> (and (<= 0 m@@5) (<= 0 n@@1)) (= (|ORD#Plus| (|ORD#Plus| o@@10 (|ORD#FromNat| m@@5)) (|ORD#FromNat| n@@1)) (|ORD#Plus| o@@10 (|ORD#FromNat| (+ m@@5 n@@1))))))
 :qid |DafnyPreludebpl.422:15|
 :skolemid |441|
 :pattern ( (|ORD#Plus| (|ORD#Plus| o@@10 (|ORD#FromNat| m@@5)) (|ORD#FromNat| n@@1)))
)))
(assert (forall ((o@@11 T@U) (m@@6 Int) (n@@2 Int) ) (!  (=> (= (type o@@11) BoxType) (=> (and (and (<= 0 m@@6) (<= 0 n@@2)) (<= (+ m@@6 n@@2) (|ORD#Offset| o@@11))) (= (|ORD#Minus| (|ORD#Minus| o@@11 (|ORD#FromNat| m@@6)) (|ORD#FromNat| n@@2)) (|ORD#Minus| o@@11 (|ORD#FromNat| (+ m@@6 n@@2))))))
 :qid |DafnyPreludebpl.427:15|
 :skolemid |442|
 :pattern ( (|ORD#Minus| (|ORD#Minus| o@@11 (|ORD#FromNat| m@@6)) (|ORD#FromNat| n@@2)))
)))
(assert (forall ((o@@12 T@U) (m@@7 Int) (n@@3 Int) ) (!  (=> (= (type o@@12) BoxType) (=> (and (and (<= 0 m@@7) (<= 0 n@@3)) (<= n@@3 (+ (|ORD#Offset| o@@12) m@@7))) (and (=> (<= 0 (- m@@7 n@@3)) (= (|ORD#Minus| (|ORD#Plus| o@@12 (|ORD#FromNat| m@@7)) (|ORD#FromNat| n@@3)) (|ORD#Plus| o@@12 (|ORD#FromNat| (- m@@7 n@@3))))) (=> (<= (- m@@7 n@@3) 0) (= (|ORD#Minus| (|ORD#Plus| o@@12 (|ORD#FromNat| m@@7)) (|ORD#FromNat| n@@3)) (|ORD#Minus| o@@12 (|ORD#FromNat| (- n@@3 m@@7))))))))
 :qid |DafnyPreludebpl.432:15|
 :skolemid |443|
 :pattern ( (|ORD#Minus| (|ORD#Plus| o@@12 (|ORD#FromNat| m@@7)) (|ORD#FromNat| n@@3)))
)))
(assert (forall ((o@@13 T@U) (m@@8 Int) (n@@4 Int) ) (!  (=> (= (type o@@13) BoxType) (=> (and (and (<= 0 m@@8) (<= 0 n@@4)) (<= n@@4 (+ (|ORD#Offset| o@@13) m@@8))) (and (=> (<= 0 (- m@@8 n@@4)) (= (|ORD#Plus| (|ORD#Minus| o@@13 (|ORD#FromNat| m@@8)) (|ORD#FromNat| n@@4)) (|ORD#Minus| o@@13 (|ORD#FromNat| (- m@@8 n@@4))))) (=> (<= (- m@@8 n@@4) 0) (= (|ORD#Plus| (|ORD#Minus| o@@13 (|ORD#FromNat| m@@8)) (|ORD#FromNat| n@@4)) (|ORD#Plus| o@@13 (|ORD#FromNat| (- n@@4 m@@8))))))))
 :qid |DafnyPreludebpl.438:15|
 :skolemid |444|
 :pattern ( (|ORD#Plus| (|ORD#Minus| o@@13 (|ORD#FromNat| m@@8)) (|ORD#FromNat| n@@4)))
)))
(assert  (and (= (Ctor LayerTypeType) 22) (forall ((arg0@@67 T@U) (arg1@@21 T@U) ) (! (let ((A (MapType0TypeInv1 (type arg0@@67))))
(= (type (AtLayer arg0@@67 arg1@@21)) A))
 :qid |funType:AtLayer|
 :pattern ( (AtLayer arg0@@67 arg1@@21))
))))
(assert (forall ((f T@U) (ly T@U) ) (! (let ((A@@0 (MapType0TypeInv1 (type f))))
 (=> (and (= (type f) (MapType0Type LayerTypeType A@@0)) (= (type ly) LayerTypeType)) (= (AtLayer f ly) (MapType0Select f ly))))
 :qid |DafnyPreludebpl.462:18|
 :skolemid |445|
 :pattern ( (AtLayer f ly))
)))
(assert (forall ((arg0@@68 T@U) ) (! (= (type ($LS arg0@@68)) LayerTypeType)
 :qid |funType:$LS|
 :pattern ( ($LS arg0@@68))
)))
(assert (forall ((f@@0 T@U) (ly@@0 T@U) ) (! (let ((A@@1 (MapType0TypeInv1 (type f@@0))))
 (=> (and (= (type f@@0) (MapType0Type LayerTypeType A@@1)) (= (type ly@@0) LayerTypeType)) (= (AtLayer f@@0 ($LS ly@@0)) (AtLayer f@@0 ly@@0))))
 :qid |DafnyPreludebpl.463:18|
 :skolemid |446|
 :pattern ( (AtLayer f@@0 ($LS ly@@0)))
)))
(assert (forall ((arg0@@69 Int) ) (! (= (type (IndexField arg0@@69)) (FieldType BoxType))
 :qid |funType:IndexField|
 :pattern ( (IndexField arg0@@69))
)))
(assert (forall ((i@@1 Int) ) (! (= (FDim (IndexField i@@1)) 1)
 :qid |DafnyPreludebpl.474:15|
 :skolemid |447|
 :pattern ( (IndexField i@@1))
)))
(assert (forall ((i@@2 Int) ) (! (= (IndexField_Inverse (IndexField i@@2)) i@@2)
 :qid |DafnyPreludebpl.476:15|
 :skolemid |448|
 :pattern ( (IndexField i@@2))
)))
(assert (forall ((arg0@@70 T@U) (arg1@@22 Int) ) (! (= (type (MultiIndexField arg0@@70 arg1@@22)) (FieldType BoxType))
 :qid |funType:MultiIndexField|
 :pattern ( (MultiIndexField arg0@@70 arg1@@22))
)))
(assert (forall ((f@@1 T@U) (i@@3 Int) ) (!  (=> (= (type f@@1) (FieldType BoxType)) (= (FDim (MultiIndexField f@@1 i@@3)) (+ (FDim f@@1) 1)))
 :qid |DafnyPreludebpl.479:15|
 :skolemid |449|
 :pattern ( (MultiIndexField f@@1 i@@3))
)))
(assert (forall ((arg0@@71 T@U) ) (! (let ((T@@3 (FieldTypeInv0 (type arg0@@71))))
(= (type (MultiIndexField_Inverse0 arg0@@71)) (FieldType T@@3)))
 :qid |funType:MultiIndexField_Inverse0|
 :pattern ( (MultiIndexField_Inverse0 arg0@@71))
)))
(assert (forall ((f@@2 T@U) (i@@4 Int) ) (!  (=> (= (type f@@2) (FieldType BoxType)) (and (= (MultiIndexField_Inverse0 (MultiIndexField f@@2 i@@4)) f@@2) (= (MultiIndexField_Inverse1 (MultiIndexField f@@2 i@@4)) i@@4)))
 :qid |DafnyPreludebpl.482:15|
 :skolemid |450|
 :pattern ( (MultiIndexField f@@2 i@@4))
)))
(assert  (and (and (forall ((alpha@@3 T@T) (arg0@@72 T@U) (arg1@@23 T@U) ) (! (= (type (FieldOfDecl alpha@@3 arg0@@72 arg1@@23)) (FieldType alpha@@3))
 :qid |funType:FieldOfDecl|
 :pattern ( (FieldOfDecl alpha@@3 arg0@@72 arg1@@23))
)) (forall ((arg0@@73 T@U) ) (! (= (type (DeclType arg0@@73)) ClassNameType)
 :qid |funType:DeclType|
 :pattern ( (DeclType arg0@@73))
))) (forall ((arg0@@74 T@U) ) (! (= (type (DeclName arg0@@74)) NameFamilyType)
 :qid |funType:DeclName|
 :pattern ( (DeclName arg0@@74))
))))
(assert (forall ((cl T@U) (nm T@U) (T@@4 T@T) ) (!  (=> (and (= (type cl) ClassNameType) (= (type nm) NameFamilyType)) (and (= (DeclType (FieldOfDecl T@@4 cl nm)) cl) (= (DeclName (FieldOfDecl T@@4 cl nm)) nm)))
 :qid |DafnyPreludebpl.491:18|
 :skolemid |451|
 :pattern ( (FieldOfDecl T@@4 cl nm))
)))
(assert (forall ((h@@12 T@U) (k T@U) (v@@28 T@U) (t@@21 T@U) ) (!  (=> (and (and (and (and (= (type h@@12) (MapType0Type refType MapType1Type)) (= (type k) (MapType0Type refType MapType1Type))) (= (type t@@21) TyType)) ($HeapSucc h@@12 k)) ($IsAlloc v@@28 t@@21 h@@12)) ($IsAlloc v@@28 t@@21 k))
 :qid |DafnyPreludebpl.504:17|
 :skolemid |452|
 :pattern ( ($HeapSucc h@@12 k) ($IsAlloc v@@28 t@@21 h@@12))
)))
(assert (forall ((h@@13 T@U) (k@@0 T@U) (bx@@21 T@U) (t@@22 T@U) ) (!  (=> (and (and (and (and (and (= (type h@@13) (MapType0Type refType MapType1Type)) (= (type k@@0) (MapType0Type refType MapType1Type))) (= (type bx@@21) BoxType)) (= (type t@@22) TyType)) ($HeapSucc h@@13 k@@0)) ($IsAllocBox bx@@21 t@@22 h@@13)) ($IsAllocBox bx@@21 t@@22 k@@0))
 :qid |DafnyPreludebpl.507:14|
 :skolemid |453|
 :pattern ( ($HeapSucc h@@13 k@@0) ($IsAllocBox bx@@21 t@@22 h@@13))
)))
(assert (= (FDim alloc) 0))
(assert (= (DeclName alloc) allocName))
(assert  (not ($IsGhostField alloc)))
(assert (forall ((o@@14 T@U) ) (!  (=> (= (type o@@14) refType) (<= 0 (_System.array.Length o@@14)))
 :qid |DafnyPreludebpl.524:15|
 :skolemid |454|
 :no-pattern (type o@@14)
 :no-pattern (U_2_int o@@14)
 :no-pattern (U_2_bool o@@14)
)))
(assert (forall ((x@@15 Real) ) (! (= (q@Int x@@15) (to_int x@@15))
 :qid |DafnyPreludebpl.530:14|
 :skolemid |455|
 :pattern ( (q@Int x@@15))
)))
(assert (forall ((x@@16 Int) ) (! (= (q@Real x@@16) (to_real x@@16))
 :qid |DafnyPreludebpl.531:15|
 :skolemid |456|
 :pattern ( (q@Real x@@16))
)))
(assert (forall ((i@@5 Int) ) (! (= (q@Int (q@Real i@@5)) i@@5)
 :qid |DafnyPreludebpl.532:15|
 :skolemid |457|
 :pattern ( (q@Int (q@Real i@@5)))
)))
(assert (= (type $OneHeap) (MapType0Type refType MapType1Type)))
(assert ($IsGoodHeap $OneHeap))
(assert (forall ((h@@14 T@U) (r@@0 T@U) (f@@3 T@U) (x@@17 T@U) ) (! (let ((alpha@@4 (type x@@17)))
 (=> (and (and (and (= (type h@@14) (MapType0Type refType MapType1Type)) (= (type r@@0) refType)) (= (type f@@3) (FieldType alpha@@4))) ($IsGoodHeap (MapType0Store h@@14 r@@0 (MapType1Store (MapType0Select h@@14 r@@0) f@@3 x@@17)))) ($HeapSucc h@@14 (MapType0Store h@@14 r@@0 (MapType1Store (MapType0Select h@@14 r@@0) f@@3 x@@17)))))
 :qid |DafnyPreludebpl.554:22|
 :skolemid |458|
 :pattern ( (MapType0Store h@@14 r@@0 (MapType1Store (MapType0Select h@@14 r@@0) f@@3 x@@17)))
)))
(assert (forall ((a@@2 T@U) (b@@2 T@U) (c T@U) ) (!  (=> (and (and (and (and (= (type a@@2) (MapType0Type refType MapType1Type)) (= (type b@@2) (MapType0Type refType MapType1Type))) (= (type c) (MapType0Type refType MapType1Type))) (not (= a@@2 c))) (and ($HeapSucc a@@2 b@@2) ($HeapSucc b@@2 c))) ($HeapSucc a@@2 c))
 :qid |DafnyPreludebpl.557:15|
 :skolemid |459|
 :pattern ( ($HeapSucc a@@2 b@@2) ($HeapSucc b@@2 c))
)))
(assert (forall ((h@@15 T@U) (k@@1 T@U) ) (!  (=> (and (and (= (type h@@15) (MapType0Type refType MapType1Type)) (= (type k@@1) (MapType0Type refType MapType1Type))) ($HeapSucc h@@15 k@@1)) (forall ((o@@15 T@U) ) (!  (=> (and (= (type o@@15) refType) (U_2_bool (MapType1Select (MapType0Select h@@15 o@@15) alloc))) (U_2_bool (MapType1Select (MapType0Select k@@1 o@@15) alloc)))
 :qid |DafnyPreludebpl.560:30|
 :skolemid |460|
 :pattern ( (MapType1Select (MapType0Select k@@1 o@@15) alloc))
)))
 :qid |DafnyPreludebpl.559:15|
 :skolemid |461|
 :pattern ( ($HeapSucc h@@15 k@@1))
)))
(assert (forall ((h@@16 T@U) (k@@2 T@U) ) (!  (=> (and (and (= (type h@@16) (MapType0Type refType MapType1Type)) (= (type k@@2) (MapType0Type refType MapType1Type))) ($HeapSuccGhost h@@16 k@@2)) (and ($HeapSucc h@@16 k@@2) (forall ((o@@16 T@U) (f@@4 T@U) ) (! (let ((alpha@@5 (FieldTypeInv0 (type f@@4))))
 (=> (and (and (= (type o@@16) refType) (= (type f@@4) (FieldType alpha@@5))) (not ($IsGhostField f@@4))) (= (MapType1Select (MapType0Select h@@16 o@@16) f@@4) (MapType1Select (MapType0Select k@@2 o@@16) f@@4))))
 :qid |DafnyPreludebpl.566:20|
 :skolemid |462|
 :pattern ( (MapType1Select (MapType0Select k@@2 o@@16) f@@4))
))))
 :qid |DafnyPreludebpl.563:15|
 :skolemid |463|
 :pattern ( ($HeapSuccGhost h@@16 k@@2))
)))
(assert (forall ((s@@3 T@U) ) (! (let ((T@@5 (MapType0TypeInv0 (type s@@3))))
 (=> (= (type s@@3) (MapType0Type T@@5 boolType)) (<= 0 (|Set#Card| s@@3))))
 :qid |DafnyPreludebpl.624:18|
 :skolemid |468|
 :pattern ( (|Set#Card| s@@3))
)))
(assert (forall ((T@@6 T@T) ) (! (= (type (|Set#Empty| T@@6)) (MapType0Type T@@6 boolType))
 :qid |funType:Set#Empty|
 :pattern ( (|Set#Empty| T@@6))
)))
(assert (forall ((o@@17 T@U) ) (! (let ((T@@7 (type o@@17)))
 (not (U_2_bool (MapType0Select (|Set#Empty| T@@7) o@@17))))
 :qid |DafnyPreludebpl.627:18|
 :skolemid |469|
 :pattern ( (let ((T@@7 (type o@@17)))
(MapType0Select (|Set#Empty| T@@7) o@@17)))
)))
(assert (forall ((s@@4 T@U) ) (! (let ((T@@8 (MapType0TypeInv0 (type s@@4))))
 (=> (= (type s@@4) (MapType0Type T@@8 boolType)) (and (= (= (|Set#Card| s@@4) 0) (= s@@4 (|Set#Empty| T@@8))) (=> (not (= (|Set#Card| s@@4) 0)) (exists ((x@@18 T@U) ) (!  (and (= (type x@@18) T@@8) (U_2_bool (MapType0Select s@@4 x@@18)))
 :qid |DafnyPreludebpl.630:33|
 :skolemid |470|
 :no-pattern (type x@@18)
 :no-pattern (U_2_int x@@18)
 :no-pattern (U_2_bool x@@18)
))))))
 :qid |DafnyPreludebpl.628:18|
 :skolemid |471|
 :pattern ( (|Set#Card| s@@4))
)))
(assert (forall ((arg0@@75 T@U) ) (! (let ((T@@9 (type arg0@@75)))
(= (type (|Set#Singleton| arg0@@75)) (MapType0Type T@@9 boolType)))
 :qid |funType:Set#Singleton|
 :pattern ( (|Set#Singleton| arg0@@75))
)))
(assert (forall ((r@@1 T@U) ) (! (U_2_bool (MapType0Select (|Set#Singleton| r@@1) r@@1))
 :qid |DafnyPreludebpl.636:18|
 :skolemid |472|
 :pattern ( (|Set#Singleton| r@@1))
)))
(assert (forall ((r@@2 T@U) (o@@18 T@U) ) (! (let ((T@@10 (type r@@2)))
 (=> (= (type o@@18) T@@10) (= (U_2_bool (MapType0Select (|Set#Singleton| r@@2) o@@18)) (= r@@2 o@@18))))
 :qid |DafnyPreludebpl.637:18|
 :skolemid |473|
 :pattern ( (MapType0Select (|Set#Singleton| r@@2) o@@18))
)))
(assert (forall ((r@@3 T@U) ) (! (= (|Set#Card| (|Set#Singleton| r@@3)) 1)
 :qid |DafnyPreludebpl.638:18|
 :skolemid |474|
 :pattern ( (|Set#Card| (|Set#Singleton| r@@3)))
)))
(assert (forall ((arg0@@76 T@U) (arg1@@24 T@U) ) (! (let ((T@@11 (type arg1@@24)))
(= (type (|Set#UnionOne| arg0@@76 arg1@@24)) (MapType0Type T@@11 boolType)))
 :qid |funType:Set#UnionOne|
 :pattern ( (|Set#UnionOne| arg0@@76 arg1@@24))
)))
(assert (forall ((a@@3 T@U) (x@@19 T@U) (o@@19 T@U) ) (! (let ((T@@12 (type x@@19)))
 (=> (and (= (type a@@3) (MapType0Type T@@12 boolType)) (= (type o@@19) T@@12)) (= (U_2_bool (MapType0Select (|Set#UnionOne| a@@3 x@@19) o@@19))  (or (= o@@19 x@@19) (U_2_bool (MapType0Select a@@3 o@@19))))))
 :qid |DafnyPreludebpl.641:18|
 :skolemid |475|
 :pattern ( (MapType0Select (|Set#UnionOne| a@@3 x@@19) o@@19))
)))
(assert (forall ((a@@4 T@U) (x@@20 T@U) ) (! (let ((T@@13 (type x@@20)))
 (=> (= (type a@@4) (MapType0Type T@@13 boolType)) (U_2_bool (MapType0Select (|Set#UnionOne| a@@4 x@@20) x@@20))))
 :qid |DafnyPreludebpl.643:18|
 :skolemid |476|
 :pattern ( (|Set#UnionOne| a@@4 x@@20))
)))
(assert (forall ((a@@5 T@U) (x@@21 T@U) (y@@1 T@U) ) (! (let ((T@@14 (type x@@21)))
 (=> (and (and (= (type a@@5) (MapType0Type T@@14 boolType)) (= (type y@@1) T@@14)) (U_2_bool (MapType0Select a@@5 y@@1))) (U_2_bool (MapType0Select (|Set#UnionOne| a@@5 x@@21) y@@1))))
 :qid |DafnyPreludebpl.645:18|
 :skolemid |477|
 :pattern ( (|Set#UnionOne| a@@5 x@@21) (MapType0Select a@@5 y@@1))
)))
(assert (forall ((a@@6 T@U) (x@@22 T@U) ) (! (let ((T@@15 (type x@@22)))
 (=> (and (= (type a@@6) (MapType0Type T@@15 boolType)) (U_2_bool (MapType0Select a@@6 x@@22))) (= (|Set#Card| (|Set#UnionOne| a@@6 x@@22)) (|Set#Card| a@@6))))
 :qid |DafnyPreludebpl.647:18|
 :skolemid |478|
 :pattern ( (|Set#Card| (|Set#UnionOne| a@@6 x@@22)))
)))
(assert (forall ((a@@7 T@U) (x@@23 T@U) ) (! (let ((T@@16 (type x@@23)))
 (=> (and (= (type a@@7) (MapType0Type T@@16 boolType)) (not (U_2_bool (MapType0Select a@@7 x@@23)))) (= (|Set#Card| (|Set#UnionOne| a@@7 x@@23)) (+ (|Set#Card| a@@7) 1))))
 :qid |DafnyPreludebpl.649:18|
 :skolemid |479|
 :pattern ( (|Set#Card| (|Set#UnionOne| a@@7 x@@23)))
)))
(assert (forall ((arg0@@77 T@U) (arg1@@25 T@U) ) (! (let ((T@@17 (MapType0TypeInv0 (type arg0@@77))))
(= (type (|Set#Union| arg0@@77 arg1@@25)) (MapType0Type T@@17 boolType)))
 :qid |funType:Set#Union|
 :pattern ( (|Set#Union| arg0@@77 arg1@@25))
)))
(assert (forall ((a@@8 T@U) (b@@3 T@U) (o@@20 T@U) ) (! (let ((T@@18 (type o@@20)))
 (=> (and (= (type a@@8) (MapType0Type T@@18 boolType)) (= (type b@@3) (MapType0Type T@@18 boolType))) (= (U_2_bool (MapType0Select (|Set#Union| a@@8 b@@3) o@@20))  (or (U_2_bool (MapType0Select a@@8 o@@20)) (U_2_bool (MapType0Select b@@3 o@@20))))))
 :qid |DafnyPreludebpl.653:18|
 :skolemid |480|
 :pattern ( (MapType0Select (|Set#Union| a@@8 b@@3) o@@20))
)))
(assert (forall ((a@@9 T@U) (b@@4 T@U) (y@@2 T@U) ) (! (let ((T@@19 (type y@@2)))
 (=> (and (and (= (type a@@9) (MapType0Type T@@19 boolType)) (= (type b@@4) (MapType0Type T@@19 boolType))) (U_2_bool (MapType0Select a@@9 y@@2))) (U_2_bool (MapType0Select (|Set#Union| a@@9 b@@4) y@@2))))
 :qid |DafnyPreludebpl.655:18|
 :skolemid |481|
 :pattern ( (|Set#Union| a@@9 b@@4) (MapType0Select a@@9 y@@2))
)))
(assert (forall ((a@@10 T@U) (b@@5 T@U) (y@@3 T@U) ) (! (let ((T@@20 (type y@@3)))
 (=> (and (and (= (type a@@10) (MapType0Type T@@20 boolType)) (= (type b@@5) (MapType0Type T@@20 boolType))) (U_2_bool (MapType0Select b@@5 y@@3))) (U_2_bool (MapType0Select (|Set#Union| a@@10 b@@5) y@@3))))
 :qid |DafnyPreludebpl.657:18|
 :skolemid |482|
 :pattern ( (|Set#Union| a@@10 b@@5) (MapType0Select b@@5 y@@3))
)))
(assert (forall ((arg0@@78 T@U) (arg1@@26 T@U) ) (! (let ((T@@21 (MapType0TypeInv0 (type arg0@@78))))
(= (type (|Set#Difference| arg0@@78 arg1@@26)) (MapType0Type T@@21 boolType)))
 :qid |funType:Set#Difference|
 :pattern ( (|Set#Difference| arg0@@78 arg1@@26))
)))
(assert (forall ((a@@11 T@U) (b@@6 T@U) ) (! (let ((T@@22 (MapType0TypeInv0 (type a@@11))))
 (=> (and (and (= (type a@@11) (MapType0Type T@@22 boolType)) (= (type b@@6) (MapType0Type T@@22 boolType))) (|Set#Disjoint| a@@11 b@@6)) (and (= (|Set#Difference| (|Set#Union| a@@11 b@@6) a@@11) b@@6) (= (|Set#Difference| (|Set#Union| a@@11 b@@6) b@@6) a@@11))))
 :qid |DafnyPreludebpl.659:18|
 :skolemid |483|
 :pattern ( (|Set#Union| a@@11 b@@6))
)))
(assert (forall ((arg0@@79 T@U) (arg1@@27 T@U) ) (! (let ((T@@23 (MapType0TypeInv0 (type arg0@@79))))
(= (type (|Set#Intersection| arg0@@79 arg1@@27)) (MapType0Type T@@23 boolType)))
 :qid |funType:Set#Intersection|
 :pattern ( (|Set#Intersection| arg0@@79 arg1@@27))
)))
(assert (forall ((a@@12 T@U) (b@@7 T@U) (o@@21 T@U) ) (! (let ((T@@24 (type o@@21)))
 (=> (and (= (type a@@12) (MapType0Type T@@24 boolType)) (= (type b@@7) (MapType0Type T@@24 boolType))) (= (U_2_bool (MapType0Select (|Set#Intersection| a@@12 b@@7) o@@21))  (and (U_2_bool (MapType0Select a@@12 o@@21)) (U_2_bool (MapType0Select b@@7 o@@21))))))
 :qid |DafnyPreludebpl.669:18|
 :skolemid |484|
 :pattern ( (MapType0Select (|Set#Intersection| a@@12 b@@7) o@@21))
)))
(assert (forall ((a@@13 T@U) (b@@8 T@U) ) (! (let ((T@@25 (MapType0TypeInv0 (type a@@13))))
 (=> (and (= (type a@@13) (MapType0Type T@@25 boolType)) (= (type b@@8) (MapType0Type T@@25 boolType))) (= (|Set#Union| (|Set#Union| a@@13 b@@8) b@@8) (|Set#Union| a@@13 b@@8))))
 :qid |DafnyPreludebpl.672:18|
 :skolemid |485|
 :pattern ( (|Set#Union| (|Set#Union| a@@13 b@@8) b@@8))
)))
(assert (forall ((a@@14 T@U) (b@@9 T@U) ) (! (let ((T@@26 (MapType0TypeInv0 (type a@@14))))
 (=> (and (= (type a@@14) (MapType0Type T@@26 boolType)) (= (type b@@9) (MapType0Type T@@26 boolType))) (= (|Set#Union| a@@14 (|Set#Union| a@@14 b@@9)) (|Set#Union| a@@14 b@@9))))
 :qid |DafnyPreludebpl.674:18|
 :skolemid |486|
 :pattern ( (|Set#Union| a@@14 (|Set#Union| a@@14 b@@9)))
)))
(assert (forall ((a@@15 T@U) (b@@10 T@U) ) (! (let ((T@@27 (MapType0TypeInv0 (type a@@15))))
 (=> (and (= (type a@@15) (MapType0Type T@@27 boolType)) (= (type b@@10) (MapType0Type T@@27 boolType))) (= (|Set#Intersection| (|Set#Intersection| a@@15 b@@10) b@@10) (|Set#Intersection| a@@15 b@@10))))
 :qid |DafnyPreludebpl.676:18|
 :skolemid |487|
 :pattern ( (|Set#Intersection| (|Set#Intersection| a@@15 b@@10) b@@10))
)))
(assert (forall ((a@@16 T@U) (b@@11 T@U) ) (! (let ((T@@28 (MapType0TypeInv0 (type a@@16))))
 (=> (and (= (type a@@16) (MapType0Type T@@28 boolType)) (= (type b@@11) (MapType0Type T@@28 boolType))) (= (|Set#Intersection| a@@16 (|Set#Intersection| a@@16 b@@11)) (|Set#Intersection| a@@16 b@@11))))
 :qid |DafnyPreludebpl.678:18|
 :skolemid |488|
 :pattern ( (|Set#Intersection| a@@16 (|Set#Intersection| a@@16 b@@11)))
)))
(assert (forall ((a@@17 T@U) (b@@12 T@U) ) (! (let ((T@@29 (MapType0TypeInv0 (type a@@17))))
 (=> (and (= (type a@@17) (MapType0Type T@@29 boolType)) (= (type b@@12) (MapType0Type T@@29 boolType))) (= (+ (|Set#Card| (|Set#Union| a@@17 b@@12)) (|Set#Card| (|Set#Intersection| a@@17 b@@12))) (+ (|Set#Card| a@@17) (|Set#Card| b@@12)))))
 :qid |DafnyPreludebpl.680:18|
 :skolemid |489|
 :pattern ( (|Set#Card| (|Set#Union| a@@17 b@@12)))
 :pattern ( (|Set#Card| (|Set#Intersection| a@@17 b@@12)))
)))
(assert (forall ((a@@18 T@U) (b@@13 T@U) (o@@22 T@U) ) (! (let ((T@@30 (type o@@22)))
 (=> (and (= (type a@@18) (MapType0Type T@@30 boolType)) (= (type b@@13) (MapType0Type T@@30 boolType))) (= (U_2_bool (MapType0Select (|Set#Difference| a@@18 b@@13) o@@22))  (and (U_2_bool (MapType0Select a@@18 o@@22)) (not (U_2_bool (MapType0Select b@@13 o@@22)))))))
 :qid |DafnyPreludebpl.684:18|
 :skolemid |490|
 :pattern ( (MapType0Select (|Set#Difference| a@@18 b@@13) o@@22))
)))
(assert (forall ((a@@19 T@U) (b@@14 T@U) (y@@4 T@U) ) (! (let ((T@@31 (type y@@4)))
 (=> (and (and (= (type a@@19) (MapType0Type T@@31 boolType)) (= (type b@@14) (MapType0Type T@@31 boolType))) (U_2_bool (MapType0Select b@@14 y@@4))) (not (U_2_bool (MapType0Select (|Set#Difference| a@@19 b@@14) y@@4)))))
 :qid |DafnyPreludebpl.686:18|
 :skolemid |491|
 :pattern ( (|Set#Difference| a@@19 b@@14) (MapType0Select b@@14 y@@4))
)))
(assert (forall ((a@@20 T@U) (b@@15 T@U) ) (! (let ((T@@32 (MapType0TypeInv0 (type a@@20))))
 (=> (and (= (type a@@20) (MapType0Type T@@32 boolType)) (= (type b@@15) (MapType0Type T@@32 boolType))) (and (= (+ (+ (|Set#Card| (|Set#Difference| a@@20 b@@15)) (|Set#Card| (|Set#Difference| b@@15 a@@20))) (|Set#Card| (|Set#Intersection| a@@20 b@@15))) (|Set#Card| (|Set#Union| a@@20 b@@15))) (= (|Set#Card| (|Set#Difference| a@@20 b@@15)) (- (|Set#Card| a@@20) (|Set#Card| (|Set#Intersection| a@@20 b@@15)))))))
 :qid |DafnyPreludebpl.688:18|
 :skolemid |492|
 :pattern ( (|Set#Card| (|Set#Difference| a@@20 b@@15)))
)))
(assert (forall ((a@@21 T@U) (b@@16 T@U) ) (! (let ((T@@33 (MapType0TypeInv0 (type a@@21))))
 (=> (and (= (type a@@21) (MapType0Type T@@33 boolType)) (= (type b@@16) (MapType0Type T@@33 boolType))) (= (|Set#Subset| a@@21 b@@16) (forall ((o@@23 T@U) ) (!  (=> (and (= (type o@@23) T@@33) (U_2_bool (MapType0Select a@@21 o@@23))) (U_2_bool (MapType0Select b@@16 o@@23)))
 :qid |DafnyPreludebpl.697:32|
 :skolemid |493|
 :pattern ( (MapType0Select a@@21 o@@23))
 :pattern ( (MapType0Select b@@16 o@@23))
)))))
 :qid |DafnyPreludebpl.696:17|
 :skolemid |494|
 :pattern ( (|Set#Subset| a@@21 b@@16))
)))
(assert (forall ((a@@22 T@U) (b@@17 T@U) ) (! (let ((T@@34 (MapType0TypeInv0 (type a@@22))))
 (=> (and (= (type a@@22) (MapType0Type T@@34 boolType)) (= (type b@@17) (MapType0Type T@@34 boolType))) (= (|Set#Equal| a@@22 b@@17) (forall ((o@@24 T@U) ) (!  (=> (= (type o@@24) T@@34) (= (U_2_bool (MapType0Select a@@22 o@@24)) (U_2_bool (MapType0Select b@@17 o@@24))))
 :qid |DafnyPreludebpl.705:31|
 :skolemid |495|
 :pattern ( (MapType0Select a@@22 o@@24))
 :pattern ( (MapType0Select b@@17 o@@24))
)))))
 :qid |DafnyPreludebpl.704:17|
 :skolemid |496|
 :pattern ( (|Set#Equal| a@@22 b@@17))
)))
(assert (forall ((a@@23 T@U) (b@@18 T@U) ) (! (let ((T@@35 (MapType0TypeInv0 (type a@@23))))
 (=> (and (and (= (type a@@23) (MapType0Type T@@35 boolType)) (= (type b@@18) (MapType0Type T@@35 boolType))) (|Set#Equal| a@@23 b@@18)) (= a@@23 b@@18)))
 :qid |DafnyPreludebpl.706:17|
 :skolemid |497|
 :pattern ( (|Set#Equal| a@@23 b@@18))
)))
(assert (forall ((a@@24 T@U) (b@@19 T@U) ) (! (let ((T@@36 (MapType0TypeInv0 (type a@@24))))
 (=> (and (= (type a@@24) (MapType0Type T@@36 boolType)) (= (type b@@19) (MapType0Type T@@36 boolType))) (= (|Set#Disjoint| a@@24 b@@19) (forall ((o@@25 T@U) ) (!  (=> (= (type o@@25) T@@36) (or (not (U_2_bool (MapType0Select a@@24 o@@25))) (not (U_2_bool (MapType0Select b@@19 o@@25)))))
 :qid |DafnyPreludebpl.711:34|
 :skolemid |498|
 :pattern ( (MapType0Select a@@24 o@@25))
 :pattern ( (MapType0Select b@@19 o@@25))
)))))
 :qid |DafnyPreludebpl.710:18|
 :skolemid |499|
 :pattern ( (|Set#Disjoint| a@@24 b@@19))
)))
(assert (forall ((T@@37 T@T) ) (! (= (type (|ISet#Empty| T@@37)) (MapType0Type T@@37 boolType))
 :qid |funType:ISet#Empty|
 :pattern ( (|ISet#Empty| T@@37))
)))
(assert (forall ((o@@26 T@U) ) (! (let ((T@@38 (type o@@26)))
 (not (U_2_bool (MapType0Select (|ISet#Empty| T@@38) o@@26))))
 :qid |DafnyPreludebpl.720:18|
 :skolemid |500|
 :pattern ( (let ((T@@38 (type o@@26)))
(MapType0Select (|ISet#Empty| T@@38) o@@26)))
)))
(assert (forall ((arg0@@80 T@U) (arg1@@28 T@U) ) (! (let ((T@@39 (type arg1@@28)))
(= (type (|ISet#UnionOne| arg0@@80 arg1@@28)) (MapType0Type T@@39 boolType)))
 :qid |funType:ISet#UnionOne|
 :pattern ( (|ISet#UnionOne| arg0@@80 arg1@@28))
)))
(assert (forall ((a@@25 T@U) (x@@24 T@U) (o@@27 T@U) ) (! (let ((T@@40 (type x@@24)))
 (=> (and (= (type a@@25) (MapType0Type T@@40 boolType)) (= (type o@@27) T@@40)) (= (U_2_bool (MapType0Select (|ISet#UnionOne| a@@25 x@@24) o@@27))  (or (= o@@27 x@@24) (U_2_bool (MapType0Select a@@25 o@@27))))))
 :qid |DafnyPreludebpl.727:18|
 :skolemid |501|
 :pattern ( (MapType0Select (|ISet#UnionOne| a@@25 x@@24) o@@27))
)))
(assert (forall ((a@@26 T@U) (x@@25 T@U) ) (! (let ((T@@41 (type x@@25)))
 (=> (= (type a@@26) (MapType0Type T@@41 boolType)) (U_2_bool (MapType0Select (|ISet#UnionOne| a@@26 x@@25) x@@25))))
 :qid |DafnyPreludebpl.729:18|
 :skolemid |502|
 :pattern ( (|ISet#UnionOne| a@@26 x@@25))
)))
(assert (forall ((a@@27 T@U) (x@@26 T@U) (y@@5 T@U) ) (! (let ((T@@42 (type x@@26)))
 (=> (and (and (= (type a@@27) (MapType0Type T@@42 boolType)) (= (type y@@5) T@@42)) (U_2_bool (MapType0Select a@@27 y@@5))) (U_2_bool (MapType0Select (|ISet#UnionOne| a@@27 x@@26) y@@5))))
 :qid |DafnyPreludebpl.731:18|
 :skolemid |503|
 :pattern ( (|ISet#UnionOne| a@@27 x@@26) (MapType0Select a@@27 y@@5))
)))
(assert (forall ((arg0@@81 T@U) (arg1@@29 T@U) ) (! (let ((T@@43 (MapType0TypeInv0 (type arg0@@81))))
(= (type (|ISet#Union| arg0@@81 arg1@@29)) (MapType0Type T@@43 boolType)))
 :qid |funType:ISet#Union|
 :pattern ( (|ISet#Union| arg0@@81 arg1@@29))
)))
(assert (forall ((a@@28 T@U) (b@@20 T@U) (o@@28 T@U) ) (! (let ((T@@44 (type o@@28)))
 (=> (and (= (type a@@28) (MapType0Type T@@44 boolType)) (= (type b@@20) (MapType0Type T@@44 boolType))) (= (U_2_bool (MapType0Select (|ISet#Union| a@@28 b@@20) o@@28))  (or (U_2_bool (MapType0Select a@@28 o@@28)) (U_2_bool (MapType0Select b@@20 o@@28))))))
 :qid |DafnyPreludebpl.735:18|
 :skolemid |504|
 :pattern ( (MapType0Select (|ISet#Union| a@@28 b@@20) o@@28))
)))
(assert (forall ((a@@29 T@U) (b@@21 T@U) (y@@6 T@U) ) (! (let ((T@@45 (type y@@6)))
 (=> (and (and (= (type a@@29) (MapType0Type T@@45 boolType)) (= (type b@@21) (MapType0Type T@@45 boolType))) (U_2_bool (MapType0Select a@@29 y@@6))) (U_2_bool (MapType0Select (|ISet#Union| a@@29 b@@21) y@@6))))
 :qid |DafnyPreludebpl.737:18|
 :skolemid |505|
 :pattern ( (|ISet#Union| a@@29 b@@21) (MapType0Select a@@29 y@@6))
)))
(assert (forall ((a@@30 T@U) (b@@22 T@U) (y@@7 T@U) ) (! (let ((T@@46 (type y@@7)))
 (=> (and (and (= (type a@@30) (MapType0Type T@@46 boolType)) (= (type b@@22) (MapType0Type T@@46 boolType))) (U_2_bool (MapType0Select b@@22 y@@7))) (U_2_bool (MapType0Select (|ISet#Union| a@@30 b@@22) y@@7))))
 :qid |DafnyPreludebpl.739:18|
 :skolemid |506|
 :pattern ( (|ISet#Union| a@@30 b@@22) (MapType0Select b@@22 y@@7))
)))
(assert (forall ((arg0@@82 T@U) (arg1@@30 T@U) ) (! (let ((T@@47 (MapType0TypeInv0 (type arg0@@82))))
(= (type (|ISet#Difference| arg0@@82 arg1@@30)) (MapType0Type T@@47 boolType)))
 :qid |funType:ISet#Difference|
 :pattern ( (|ISet#Difference| arg0@@82 arg1@@30))
)))
(assert (forall ((a@@31 T@U) (b@@23 T@U) ) (! (let ((T@@48 (MapType0TypeInv0 (type a@@31))))
 (=> (and (and (= (type a@@31) (MapType0Type T@@48 boolType)) (= (type b@@23) (MapType0Type T@@48 boolType))) (|ISet#Disjoint| a@@31 b@@23)) (and (= (|ISet#Difference| (|ISet#Union| a@@31 b@@23) a@@31) b@@23) (= (|ISet#Difference| (|ISet#Union| a@@31 b@@23) b@@23) a@@31))))
 :qid |DafnyPreludebpl.741:18|
 :skolemid |507|
 :pattern ( (|ISet#Union| a@@31 b@@23))
)))
(assert (forall ((arg0@@83 T@U) (arg1@@31 T@U) ) (! (let ((T@@49 (MapType0TypeInv0 (type arg0@@83))))
(= (type (|ISet#Intersection| arg0@@83 arg1@@31)) (MapType0Type T@@49 boolType)))
 :qid |funType:ISet#Intersection|
 :pattern ( (|ISet#Intersection| arg0@@83 arg1@@31))
)))
(assert (forall ((a@@32 T@U) (b@@24 T@U) (o@@29 T@U) ) (! (let ((T@@50 (type o@@29)))
 (=> (and (= (type a@@32) (MapType0Type T@@50 boolType)) (= (type b@@24) (MapType0Type T@@50 boolType))) (= (U_2_bool (MapType0Select (|ISet#Intersection| a@@32 b@@24) o@@29))  (and (U_2_bool (MapType0Select a@@32 o@@29)) (U_2_bool (MapType0Select b@@24 o@@29))))))
 :qid |DafnyPreludebpl.747:18|
 :skolemid |508|
 :pattern ( (MapType0Select (|ISet#Intersection| a@@32 b@@24) o@@29))
)))
(assert (forall ((a@@33 T@U) (b@@25 T@U) ) (! (let ((T@@51 (MapType0TypeInv0 (type a@@33))))
 (=> (and (= (type a@@33) (MapType0Type T@@51 boolType)) (= (type b@@25) (MapType0Type T@@51 boolType))) (= (|ISet#Union| (|ISet#Union| a@@33 b@@25) b@@25) (|ISet#Union| a@@33 b@@25))))
 :qid |DafnyPreludebpl.750:18|
 :skolemid |509|
 :pattern ( (|ISet#Union| (|ISet#Union| a@@33 b@@25) b@@25))
)))
(assert (forall ((a@@34 T@U) (b@@26 T@U) ) (! (let ((T@@52 (MapType0TypeInv0 (type a@@34))))
 (=> (and (= (type a@@34) (MapType0Type T@@52 boolType)) (= (type b@@26) (MapType0Type T@@52 boolType))) (= (|ISet#Union| a@@34 (|ISet#Union| a@@34 b@@26)) (|ISet#Union| a@@34 b@@26))))
 :qid |DafnyPreludebpl.752:18|
 :skolemid |510|
 :pattern ( (|ISet#Union| a@@34 (|ISet#Union| a@@34 b@@26)))
)))
(assert (forall ((a@@35 T@U) (b@@27 T@U) ) (! (let ((T@@53 (MapType0TypeInv0 (type a@@35))))
 (=> (and (= (type a@@35) (MapType0Type T@@53 boolType)) (= (type b@@27) (MapType0Type T@@53 boolType))) (= (|ISet#Intersection| (|ISet#Intersection| a@@35 b@@27) b@@27) (|ISet#Intersection| a@@35 b@@27))))
 :qid |DafnyPreludebpl.754:18|
 :skolemid |511|
 :pattern ( (|ISet#Intersection| (|ISet#Intersection| a@@35 b@@27) b@@27))
)))
(assert (forall ((a@@36 T@U) (b@@28 T@U) ) (! (let ((T@@54 (MapType0TypeInv0 (type a@@36))))
 (=> (and (= (type a@@36) (MapType0Type T@@54 boolType)) (= (type b@@28) (MapType0Type T@@54 boolType))) (= (|ISet#Intersection| a@@36 (|ISet#Intersection| a@@36 b@@28)) (|ISet#Intersection| a@@36 b@@28))))
 :qid |DafnyPreludebpl.756:18|
 :skolemid |512|
 :pattern ( (|ISet#Intersection| a@@36 (|ISet#Intersection| a@@36 b@@28)))
)))
(assert (forall ((a@@37 T@U) (b@@29 T@U) (o@@30 T@U) ) (! (let ((T@@55 (type o@@30)))
 (=> (and (= (type a@@37) (MapType0Type T@@55 boolType)) (= (type b@@29) (MapType0Type T@@55 boolType))) (= (U_2_bool (MapType0Select (|ISet#Difference| a@@37 b@@29) o@@30))  (and (U_2_bool (MapType0Select a@@37 o@@30)) (not (U_2_bool (MapType0Select b@@29 o@@30)))))))
 :qid |DafnyPreludebpl.761:18|
 :skolemid |513|
 :pattern ( (MapType0Select (|ISet#Difference| a@@37 b@@29) o@@30))
)))
(assert (forall ((a@@38 T@U) (b@@30 T@U) (y@@8 T@U) ) (! (let ((T@@56 (type y@@8)))
 (=> (and (and (= (type a@@38) (MapType0Type T@@56 boolType)) (= (type b@@30) (MapType0Type T@@56 boolType))) (U_2_bool (MapType0Select b@@30 y@@8))) (not (U_2_bool (MapType0Select (|ISet#Difference| a@@38 b@@30) y@@8)))))
 :qid |DafnyPreludebpl.763:18|
 :skolemid |514|
 :pattern ( (|ISet#Difference| a@@38 b@@30) (MapType0Select b@@30 y@@8))
)))
(assert (forall ((a@@39 T@U) (b@@31 T@U) ) (! (let ((T@@57 (MapType0TypeInv0 (type a@@39))))
 (=> (and (= (type a@@39) (MapType0Type T@@57 boolType)) (= (type b@@31) (MapType0Type T@@57 boolType))) (= (|ISet#Subset| a@@39 b@@31) (forall ((o@@31 T@U) ) (!  (=> (and (= (type o@@31) T@@57) (U_2_bool (MapType0Select a@@39 o@@31))) (U_2_bool (MapType0Select b@@31 o@@31)))
 :qid |DafnyPreludebpl.768:33|
 :skolemid |515|
 :pattern ( (MapType0Select a@@39 o@@31))
 :pattern ( (MapType0Select b@@31 o@@31))
)))))
 :qid |DafnyPreludebpl.767:17|
 :skolemid |516|
 :pattern ( (|ISet#Subset| a@@39 b@@31))
)))
(assert (forall ((a@@40 T@U) (b@@32 T@U) ) (! (let ((T@@58 (MapType0TypeInv0 (type a@@40))))
 (=> (and (= (type a@@40) (MapType0Type T@@58 boolType)) (= (type b@@32) (MapType0Type T@@58 boolType))) (= (|ISet#Equal| a@@40 b@@32) (forall ((o@@32 T@U) ) (!  (=> (= (type o@@32) T@@58) (= (U_2_bool (MapType0Select a@@40 o@@32)) (U_2_bool (MapType0Select b@@32 o@@32))))
 :qid |DafnyPreludebpl.772:32|
 :skolemid |517|
 :pattern ( (MapType0Select a@@40 o@@32))
 :pattern ( (MapType0Select b@@32 o@@32))
)))))
 :qid |DafnyPreludebpl.771:17|
 :skolemid |518|
 :pattern ( (|ISet#Equal| a@@40 b@@32))
)))
(assert (forall ((a@@41 T@U) (b@@33 T@U) ) (! (let ((T@@59 (MapType0TypeInv0 (type a@@41))))
 (=> (and (and (= (type a@@41) (MapType0Type T@@59 boolType)) (= (type b@@33) (MapType0Type T@@59 boolType))) (|ISet#Equal| a@@41 b@@33)) (= a@@41 b@@33)))
 :qid |DafnyPreludebpl.773:17|
 :skolemid |519|
 :pattern ( (|ISet#Equal| a@@41 b@@33))
)))
(assert (forall ((a@@42 T@U) (b@@34 T@U) ) (! (let ((T@@60 (MapType0TypeInv0 (type a@@42))))
 (=> (and (= (type a@@42) (MapType0Type T@@60 boolType)) (= (type b@@34) (MapType0Type T@@60 boolType))) (= (|ISet#Disjoint| a@@42 b@@34) (forall ((o@@33 T@U) ) (!  (=> (= (type o@@33) T@@60) (or (not (U_2_bool (MapType0Select a@@42 o@@33))) (not (U_2_bool (MapType0Select b@@34 o@@33)))))
 :qid |DafnyPreludebpl.778:35|
 :skolemid |520|
 :pattern ( (MapType0Select a@@42 o@@33))
 :pattern ( (MapType0Select b@@34 o@@33))
)))))
 :qid |DafnyPreludebpl.777:18|
 :skolemid |521|
 :pattern ( (|ISet#Disjoint| a@@42 b@@34))
)))
(assert (forall ((a@@43 Int) (b@@35 Int) ) (! (= (<= a@@43 b@@35) (= (|Math#min| a@@43 b@@35) a@@43))
 :qid |DafnyPreludebpl.785:15|
 :skolemid |522|
 :pattern ( (|Math#min| a@@43 b@@35))
)))
(assert (forall ((a@@44 Int) (b@@36 Int) ) (! (= (<= b@@36 a@@44) (= (|Math#min| a@@44 b@@36) b@@36))
 :qid |DafnyPreludebpl.786:15|
 :skolemid |523|
 :pattern ( (|Math#min| a@@44 b@@36))
)))
(assert (forall ((a@@45 Int) (b@@37 Int) ) (!  (or (= (|Math#min| a@@45 b@@37) a@@45) (= (|Math#min| a@@45 b@@37) b@@37))
 :qid |DafnyPreludebpl.787:15|
 :skolemid |524|
 :pattern ( (|Math#min| a@@45 b@@37))
)))
(assert (forall ((a@@46 Int) ) (!  (=> (<= 0 a@@46) (= (|Math#clip| a@@46) a@@46))
 :qid |DafnyPreludebpl.790:15|
 :skolemid |525|
 :pattern ( (|Math#clip| a@@46))
)))
(assert (forall ((a@@47 Int) ) (!  (=> (< a@@47 0) (= (|Math#clip| a@@47) 0))
 :qid |DafnyPreludebpl.791:15|
 :skolemid |526|
 :pattern ( (|Math#clip| a@@47))
)))
(assert (forall ((ms T@U) ) (! (let ((T@@61 (MapType0TypeInv0 (type ms))))
 (=> (= (type ms) (MapType0Type T@@61 intType)) (= ($IsGoodMultiSet ms) (forall ((bx@@22 T@U) ) (!  (=> (= (type bx@@22) T@@61) (and (<= 0 (U_2_int (MapType0Select ms bx@@22))) (<= (U_2_int (MapType0Select ms bx@@22)) (|MultiSet#Card| ms))))
 :qid |DafnyPreludebpl.799:11|
 :skolemid |527|
 :pattern ( (MapType0Select ms bx@@22))
)))))
 :qid |DafnyPreludebpl.797:18|
 :skolemid |528|
 :pattern ( ($IsGoodMultiSet ms))
)))
(assert (forall ((s@@5 T@U) ) (! (let ((T@@62 (MapType0TypeInv0 (type s@@5))))
 (=> (= (type s@@5) (MapType0Type T@@62 intType)) (<= 0 (|MultiSet#Card| s@@5))))
 :qid |DafnyPreludebpl.802:18|
 :skolemid |529|
 :pattern ( (|MultiSet#Card| s@@5))
)))
(assert (forall ((s@@6 T@U) (x@@27 T@U) (n@@5 T@U) ) (! (let ((T@@63 (type x@@27)))
 (=> (and (and (= (type s@@6) (MapType0Type T@@63 intType)) (= (type n@@5) intType)) (<= 0 (U_2_int n@@5))) (= (|MultiSet#Card| (MapType0Store s@@6 x@@27 n@@5)) (+ (- (|MultiSet#Card| s@@6) (U_2_int (MapType0Select s@@6 x@@27))) (U_2_int n@@5)))))
 :qid |DafnyPreludebpl.803:18|
 :skolemid |530|
 :pattern ( (|MultiSet#Card| (MapType0Store s@@6 x@@27 n@@5)))
)))
(assert (forall ((T@@64 T@T) ) (! (= (type (|MultiSet#Empty| T@@64)) (MapType0Type T@@64 intType))
 :qid |funType:MultiSet#Empty|
 :pattern ( (|MultiSet#Empty| T@@64))
)))
(assert (forall ((o@@34 T@U) ) (! (let ((T@@65 (type o@@34)))
(= (U_2_int (MapType0Select (|MultiSet#Empty| T@@65) o@@34)) 0))
 :qid |DafnyPreludebpl.807:18|
 :skolemid |531|
 :pattern ( (let ((T@@65 (type o@@34)))
(MapType0Select (|MultiSet#Empty| T@@65) o@@34)))
)))
(assert (forall ((s@@7 T@U) ) (! (let ((T@@66 (MapType0TypeInv0 (type s@@7))))
 (=> (= (type s@@7) (MapType0Type T@@66 intType)) (and (= (= (|MultiSet#Card| s@@7) 0) (= s@@7 (|MultiSet#Empty| T@@66))) (=> (not (= (|MultiSet#Card| s@@7) 0)) (exists ((x@@28 T@U) ) (!  (and (= (type x@@28) T@@66) (< 0 (U_2_int (MapType0Select s@@7 x@@28))))
 :qid |DafnyPreludebpl.810:38|
 :skolemid |532|
 :no-pattern (type x@@28)
 :no-pattern (U_2_int x@@28)
 :no-pattern (U_2_bool x@@28)
))))))
 :qid |DafnyPreludebpl.808:18|
 :skolemid |533|
 :pattern ( (|MultiSet#Card| s@@7))
)))
(assert (forall ((arg0@@84 T@U) ) (! (let ((T@@67 (type arg0@@84)))
(= (type (|MultiSet#Singleton| arg0@@84)) (MapType0Type T@@67 intType)))
 :qid |funType:MultiSet#Singleton|
 :pattern ( (|MultiSet#Singleton| arg0@@84))
)))
(assert (forall ((r@@4 T@U) (o@@35 T@U) ) (! (let ((T@@68 (type r@@4)))
 (=> (= (type o@@35) T@@68) (and (= (= (U_2_int (MapType0Select (|MultiSet#Singleton| r@@4) o@@35)) 1) (= r@@4 o@@35)) (= (= (U_2_int (MapType0Select (|MultiSet#Singleton| r@@4) o@@35)) 0) (not (= r@@4 o@@35))))))
 :qid |DafnyPreludebpl.813:18|
 :skolemid |534|
 :pattern ( (MapType0Select (|MultiSet#Singleton| r@@4) o@@35))
)))
(assert (forall ((arg0@@85 T@U) (arg1@@32 T@U) ) (! (let ((T@@69 (type arg1@@32)))
(= (type (|MultiSet#UnionOne| arg0@@85 arg1@@32)) (MapType0Type T@@69 intType)))
 :qid |funType:MultiSet#UnionOne|
 :pattern ( (|MultiSet#UnionOne| arg0@@85 arg1@@32))
)))
(assert (forall ((r@@5 T@U) ) (! (let ((T@@70 (type r@@5)))
(= (|MultiSet#Singleton| r@@5) (|MultiSet#UnionOne| (|MultiSet#Empty| T@@70) r@@5)))
 :qid |DafnyPreludebpl.815:18|
 :skolemid |535|
 :pattern ( (|MultiSet#Singleton| r@@5))
)))
(assert (forall ((a@@48 T@U) (x@@29 T@U) (o@@36 T@U) ) (! (let ((T@@71 (type x@@29)))
 (=> (and (= (type a@@48) (MapType0Type T@@71 intType)) (= (type o@@36) T@@71)) (= (< 0 (U_2_int (MapType0Select (|MultiSet#UnionOne| a@@48 x@@29) o@@36)))  (or (= o@@36 x@@29) (< 0 (U_2_int (MapType0Select a@@48 o@@36)))))))
 :qid |DafnyPreludebpl.819:18|
 :skolemid |536|
 :pattern ( (MapType0Select (|MultiSet#UnionOne| a@@48 x@@29) o@@36))
)))
(assert (forall ((a@@49 T@U) (x@@30 T@U) ) (! (let ((T@@72 (type x@@30)))
 (=> (= (type a@@49) (MapType0Type T@@72 intType)) (= (U_2_int (MapType0Select (|MultiSet#UnionOne| a@@49 x@@30) x@@30)) (+ (U_2_int (MapType0Select a@@49 x@@30)) 1))))
 :qid |DafnyPreludebpl.822:18|
 :skolemid |537|
 :pattern ( (|MultiSet#UnionOne| a@@49 x@@30))
)))
(assert (forall ((a@@50 T@U) (x@@31 T@U) (y@@9 T@U) ) (! (let ((T@@73 (type x@@31)))
 (=> (and (and (= (type a@@50) (MapType0Type T@@73 intType)) (= (type y@@9) T@@73)) (< 0 (U_2_int (MapType0Select a@@50 y@@9)))) (< 0 (U_2_int (MapType0Select (|MultiSet#UnionOne| a@@50 x@@31) y@@9)))))
 :qid |DafnyPreludebpl.825:18|
 :skolemid |538|
 :pattern ( (|MultiSet#UnionOne| a@@50 x@@31) (MapType0Select a@@50 y@@9))
)))
(assert (forall ((a@@51 T@U) (x@@32 T@U) (y@@10 T@U) ) (! (let ((T@@74 (type x@@32)))
 (=> (and (and (= (type a@@51) (MapType0Type T@@74 intType)) (= (type y@@10) T@@74)) (not (= x@@32 y@@10))) (= (U_2_int (MapType0Select a@@51 y@@10)) (U_2_int (MapType0Select (|MultiSet#UnionOne| a@@51 x@@32) y@@10)))))
 :qid |DafnyPreludebpl.828:18|
 :skolemid |539|
 :pattern ( (|MultiSet#UnionOne| a@@51 x@@32) (MapType0Select a@@51 y@@10))
)))
(assert (forall ((a@@52 T@U) (x@@33 T@U) ) (! (let ((T@@75 (type x@@33)))
 (=> (= (type a@@52) (MapType0Type T@@75 intType)) (= (|MultiSet#Card| (|MultiSet#UnionOne| a@@52 x@@33)) (+ (|MultiSet#Card| a@@52) 1))))
 :qid |DafnyPreludebpl.830:18|
 :skolemid |540|
 :pattern ( (|MultiSet#Card| (|MultiSet#UnionOne| a@@52 x@@33)))
)))
(assert (forall ((arg0@@86 T@U) (arg1@@33 T@U) ) (! (let ((T@@76 (MapType0TypeInv0 (type arg0@@86))))
(= (type (|MultiSet#Union| arg0@@86 arg1@@33)) (MapType0Type T@@76 intType)))
 :qid |funType:MultiSet#Union|
 :pattern ( (|MultiSet#Union| arg0@@86 arg1@@33))
)))
(assert (forall ((a@@53 T@U) (b@@38 T@U) (o@@37 T@U) ) (! (let ((T@@77 (type o@@37)))
 (=> (and (= (type a@@53) (MapType0Type T@@77 intType)) (= (type b@@38) (MapType0Type T@@77 intType))) (= (U_2_int (MapType0Select (|MultiSet#Union| a@@53 b@@38) o@@37)) (+ (U_2_int (MapType0Select a@@53 o@@37)) (U_2_int (MapType0Select b@@38 o@@37))))))
 :qid |DafnyPreludebpl.836:18|
 :skolemid |541|
 :pattern ( (MapType0Select (|MultiSet#Union| a@@53 b@@38) o@@37))
)))
(assert (forall ((a@@54 T@U) (b@@39 T@U) ) (! (let ((T@@78 (MapType0TypeInv0 (type a@@54))))
 (=> (and (= (type a@@54) (MapType0Type T@@78 intType)) (= (type b@@39) (MapType0Type T@@78 intType))) (= (|MultiSet#Card| (|MultiSet#Union| a@@54 b@@39)) (+ (|MultiSet#Card| a@@54) (|MultiSet#Card| b@@39)))))
 :qid |DafnyPreludebpl.838:18|
 :skolemid |542|
 :pattern ( (|MultiSet#Card| (|MultiSet#Union| a@@54 b@@39)))
)))
(assert (forall ((arg0@@87 T@U) (arg1@@34 T@U) ) (! (let ((T@@79 (MapType0TypeInv0 (type arg0@@87))))
(= (type (|MultiSet#Intersection| arg0@@87 arg1@@34)) (MapType0Type T@@79 intType)))
 :qid |funType:MultiSet#Intersection|
 :pattern ( (|MultiSet#Intersection| arg0@@87 arg1@@34))
)))
(assert (forall ((a@@55 T@U) (b@@40 T@U) (o@@38 T@U) ) (! (let ((T@@80 (type o@@38)))
 (=> (and (= (type a@@55) (MapType0Type T@@80 intType)) (= (type b@@40) (MapType0Type T@@80 intType))) (= (U_2_int (MapType0Select (|MultiSet#Intersection| a@@55 b@@40) o@@38)) (|Math#min| (U_2_int (MapType0Select a@@55 o@@38)) (U_2_int (MapType0Select b@@40 o@@38))))))
 :qid |DafnyPreludebpl.842:18|
 :skolemid |543|
 :pattern ( (MapType0Select (|MultiSet#Intersection| a@@55 b@@40) o@@38))
)))
(assert (forall ((a@@56 T@U) (b@@41 T@U) ) (! (let ((T@@81 (MapType0TypeInv0 (type a@@56))))
 (=> (and (= (type a@@56) (MapType0Type T@@81 intType)) (= (type b@@41) (MapType0Type T@@81 intType))) (= (|MultiSet#Intersection| (|MultiSet#Intersection| a@@56 b@@41) b@@41) (|MultiSet#Intersection| a@@56 b@@41))))
 :qid |DafnyPreludebpl.846:18|
 :skolemid |544|
 :pattern ( (|MultiSet#Intersection| (|MultiSet#Intersection| a@@56 b@@41) b@@41))
)))
(assert (forall ((a@@57 T@U) (b@@42 T@U) ) (! (let ((T@@82 (MapType0TypeInv0 (type a@@57))))
 (=> (and (= (type a@@57) (MapType0Type T@@82 intType)) (= (type b@@42) (MapType0Type T@@82 intType))) (= (|MultiSet#Intersection| a@@57 (|MultiSet#Intersection| a@@57 b@@42)) (|MultiSet#Intersection| a@@57 b@@42))))
 :qid |DafnyPreludebpl.848:18|
 :skolemid |545|
 :pattern ( (|MultiSet#Intersection| a@@57 (|MultiSet#Intersection| a@@57 b@@42)))
)))
(assert (forall ((arg0@@88 T@U) (arg1@@35 T@U) ) (! (let ((T@@83 (MapType0TypeInv0 (type arg0@@88))))
(= (type (|MultiSet#Difference| arg0@@88 arg1@@35)) (MapType0Type T@@83 intType)))
 :qid |funType:MultiSet#Difference|
 :pattern ( (|MultiSet#Difference| arg0@@88 arg1@@35))
)))
(assert (forall ((a@@58 T@U) (b@@43 T@U) (o@@39 T@U) ) (! (let ((T@@84 (type o@@39)))
 (=> (and (= (type a@@58) (MapType0Type T@@84 intType)) (= (type b@@43) (MapType0Type T@@84 intType))) (= (U_2_int (MapType0Select (|MultiSet#Difference| a@@58 b@@43) o@@39)) (|Math#clip| (- (U_2_int (MapType0Select a@@58 o@@39)) (U_2_int (MapType0Select b@@43 o@@39)))))))
 :qid |DafnyPreludebpl.853:18|
 :skolemid |546|
 :pattern ( (MapType0Select (|MultiSet#Difference| a@@58 b@@43) o@@39))
)))
(assert (forall ((a@@59 T@U) (b@@44 T@U) (y@@11 T@U) ) (! (let ((T@@85 (type y@@11)))
 (=> (and (and (= (type a@@59) (MapType0Type T@@85 intType)) (= (type b@@44) (MapType0Type T@@85 intType))) (<= (U_2_int (MapType0Select a@@59 y@@11)) (U_2_int (MapType0Select b@@44 y@@11)))) (= (U_2_int (MapType0Select (|MultiSet#Difference| a@@59 b@@44) y@@11)) 0)))
 :qid |DafnyPreludebpl.855:18|
 :skolemid |547|
 :pattern ( (|MultiSet#Difference| a@@59 b@@44) (MapType0Select b@@44 y@@11) (MapType0Select a@@59 y@@11))
)))
(assert (forall ((a@@60 T@U) (b@@45 T@U) ) (! (let ((T@@86 (MapType0TypeInv0 (type a@@60))))
 (=> (and (= (type a@@60) (MapType0Type T@@86 intType)) (= (type b@@45) (MapType0Type T@@86 intType))) (and (= (+ (+ (|MultiSet#Card| (|MultiSet#Difference| a@@60 b@@45)) (|MultiSet#Card| (|MultiSet#Difference| b@@45 a@@60))) (* 2 (|MultiSet#Card| (|MultiSet#Intersection| a@@60 b@@45)))) (|MultiSet#Card| (|MultiSet#Union| a@@60 b@@45))) (= (|MultiSet#Card| (|MultiSet#Difference| a@@60 b@@45)) (- (|MultiSet#Card| a@@60) (|MultiSet#Card| (|MultiSet#Intersection| a@@60 b@@45)))))))
 :qid |DafnyPreludebpl.857:18|
 :skolemid |548|
 :pattern ( (|MultiSet#Card| (|MultiSet#Difference| a@@60 b@@45)))
)))
(assert (forall ((a@@61 T@U) (b@@46 T@U) ) (! (let ((T@@87 (MapType0TypeInv0 (type a@@61))))
 (=> (and (= (type a@@61) (MapType0Type T@@87 intType)) (= (type b@@46) (MapType0Type T@@87 intType))) (= (|MultiSet#Subset| a@@61 b@@46) (forall ((o@@40 T@U) ) (!  (=> (= (type o@@40) T@@87) (<= (U_2_int (MapType0Select a@@61 o@@40)) (U_2_int (MapType0Select b@@46 o@@40))))
 :qid |DafnyPreludebpl.867:37|
 :skolemid |549|
 :pattern ( (MapType0Select a@@61 o@@40))
 :pattern ( (MapType0Select b@@46 o@@40))
)))))
 :qid |DafnyPreludebpl.866:17|
 :skolemid |550|
 :pattern ( (|MultiSet#Subset| a@@61 b@@46))
)))
(assert (forall ((a@@62 T@U) (b@@47 T@U) ) (! (let ((T@@88 (MapType0TypeInv0 (type a@@62))))
 (=> (and (= (type a@@62) (MapType0Type T@@88 intType)) (= (type b@@47) (MapType0Type T@@88 intType))) (= (|MultiSet#Equal| a@@62 b@@47) (forall ((o@@41 T@U) ) (!  (=> (= (type o@@41) T@@88) (= (U_2_int (MapType0Select a@@62 o@@41)) (U_2_int (MapType0Select b@@47 o@@41))))
 :qid |DafnyPreludebpl.871:36|
 :skolemid |551|
 :pattern ( (MapType0Select a@@62 o@@41))
 :pattern ( (MapType0Select b@@47 o@@41))
)))))
 :qid |DafnyPreludebpl.870:17|
 :skolemid |552|
 :pattern ( (|MultiSet#Equal| a@@62 b@@47))
)))
(assert (forall ((a@@63 T@U) (b@@48 T@U) ) (! (let ((T@@89 (MapType0TypeInv0 (type a@@63))))
 (=> (and (and (= (type a@@63) (MapType0Type T@@89 intType)) (= (type b@@48) (MapType0Type T@@89 intType))) (|MultiSet#Equal| a@@63 b@@48)) (= a@@63 b@@48)))
 :qid |DafnyPreludebpl.873:17|
 :skolemid |553|
 :pattern ( (|MultiSet#Equal| a@@63 b@@48))
)))
(assert (forall ((a@@64 T@U) (b@@49 T@U) ) (! (let ((T@@90 (MapType0TypeInv0 (type a@@64))))
 (=> (and (= (type a@@64) (MapType0Type T@@90 intType)) (= (type b@@49) (MapType0Type T@@90 intType))) (= (|MultiSet#Disjoint| a@@64 b@@49) (forall ((o@@42 T@U) ) (!  (=> (= (type o@@42) T@@90) (or (= (U_2_int (MapType0Select a@@64 o@@42)) 0) (= (U_2_int (MapType0Select b@@49 o@@42)) 0)))
 :qid |DafnyPreludebpl.878:39|
 :skolemid |554|
 :pattern ( (MapType0Select a@@64 o@@42))
 :pattern ( (MapType0Select b@@49 o@@42))
)))))
 :qid |DafnyPreludebpl.877:18|
 :skolemid |555|
 :pattern ( (|MultiSet#Disjoint| a@@64 b@@49))
)))
(assert (forall ((arg0@@89 T@U) ) (! (let ((T@@91 (MapType0TypeInv0 (type arg0@@89))))
(= (type (|MultiSet#FromSet| arg0@@89)) (MapType0Type T@@91 intType)))
 :qid |funType:MultiSet#FromSet|
 :pattern ( (|MultiSet#FromSet| arg0@@89))
)))
(assert (forall ((s@@8 T@U) (a@@65 T@U) ) (! (let ((T@@92 (type a@@65)))
 (=> (= (type s@@8) (MapType0Type T@@92 boolType)) (and (= (= (U_2_int (MapType0Select (|MultiSet#FromSet| s@@8) a@@65)) 0)  (not (U_2_bool (MapType0Select s@@8 a@@65)))) (= (= (U_2_int (MapType0Select (|MultiSet#FromSet| s@@8) a@@65)) 1) (U_2_bool (MapType0Select s@@8 a@@65))))))
 :qid |DafnyPreludebpl.882:18|
 :skolemid |556|
 :pattern ( (MapType0Select (|MultiSet#FromSet| s@@8) a@@65))
)))
(assert (forall ((s@@9 T@U) ) (! (let ((T@@93 (MapType0TypeInv0 (type s@@9))))
 (=> (= (type s@@9) (MapType0Type T@@93 boolType)) (= (|MultiSet#Card| (|MultiSet#FromSet| s@@9)) (|Set#Card| s@@9))))
 :qid |DafnyPreludebpl.885:18|
 :skolemid |557|
 :pattern ( (|MultiSet#Card| (|MultiSet#FromSet| s@@9)))
)))
(assert (forall ((arg0@@90 T@U) ) (! (let ((T@@94 (SeqTypeInv0 (type arg0@@90))))
(= (type (|MultiSet#FromSeq| arg0@@90)) (MapType0Type T@@94 intType)))
 :qid |funType:MultiSet#FromSeq|
 :pattern ( (|MultiSet#FromSeq| arg0@@90))
)))
(assert (forall ((s@@10 T@U) ) (! (let ((T@@95 (SeqTypeInv0 (type s@@10))))
 (=> (= (type s@@10) (SeqType T@@95)) ($IsGoodMultiSet (|MultiSet#FromSeq| s@@10))))
 :qid |DafnyPreludebpl.891:18|
 :skolemid |558|
 :pattern ( (|MultiSet#FromSeq| s@@10))
)))
(assert (forall ((s@@11 T@U) ) (! (let ((T@@96 (SeqTypeInv0 (type s@@11))))
 (=> (= (type s@@11) (SeqType T@@96)) (= (|MultiSet#Card| (|MultiSet#FromSeq| s@@11)) (|Seq#Length| s@@11))))
 :qid |DafnyPreludebpl.893:18|
 :skolemid |559|
 :pattern ( (|MultiSet#Card| (|MultiSet#FromSeq| s@@11)))
)))
(assert (forall ((arg0@@91 T@U) (arg1@@36 T@U) ) (! (let ((T@@97 (type arg1@@36)))
(= (type (|Seq#Build| arg0@@91 arg1@@36)) (SeqType T@@97)))
 :qid |funType:Seq#Build|
 :pattern ( (|Seq#Build| arg0@@91 arg1@@36))
)))
(assert (forall ((s@@12 T@U) (v@@29 T@U) ) (! (let ((T@@98 (type v@@29)))
 (=> (= (type s@@12) (SeqType T@@98)) (= (|MultiSet#FromSeq| (|Seq#Build| s@@12 v@@29)) (|MultiSet#UnionOne| (|MultiSet#FromSeq| s@@12) v@@29))))
 :qid |DafnyPreludebpl.897:18|
 :skolemid |560|
 :pattern ( (|MultiSet#FromSeq| (|Seq#Build| s@@12 v@@29)))
)))
(assert (forall ((T@@99 T@T) ) (! (= (type (|Seq#Empty| T@@99)) (SeqType T@@99))
 :qid |funType:Seq#Empty|
 :pattern ( (|Seq#Empty| T@@99))
)))
(assert (forall ((T@@100 T@T) ) (! (= (|MultiSet#FromSeq| (|Seq#Empty| T@@100)) (|MultiSet#Empty| T@@100))
 :skolemid |561|
)))
(assert (forall ((arg0@@92 T@U) (arg1@@37 T@U) ) (! (let ((T@@101 (SeqTypeInv0 (type arg0@@92))))
(= (type (|Seq#Append| arg0@@92 arg1@@37)) (SeqType T@@101)))
 :qid |funType:Seq#Append|
 :pattern ( (|Seq#Append| arg0@@92 arg1@@37))
)))
(assert (forall ((a@@66 T@U) (b@@50 T@U) ) (! (let ((T@@102 (SeqTypeInv0 (type a@@66))))
 (=> (and (= (type a@@66) (SeqType T@@102)) (= (type b@@50) (SeqType T@@102))) (= (|MultiSet#FromSeq| (|Seq#Append| a@@66 b@@50)) (|MultiSet#Union| (|MultiSet#FromSeq| a@@66) (|MultiSet#FromSeq| b@@50)))))
 :qid |DafnyPreludebpl.904:18|
 :skolemid |562|
 :pattern ( (|MultiSet#FromSeq| (|Seq#Append| a@@66 b@@50)))
)))
(assert (forall ((arg0@@93 T@U) (arg1@@38 Int) (arg2@@1 T@U) ) (! (let ((T@@103 (type arg2@@1)))
(= (type (|Seq#Update| arg0@@93 arg1@@38 arg2@@1)) (SeqType T@@103)))
 :qid |funType:Seq#Update|
 :pattern ( (|Seq#Update| arg0@@93 arg1@@38 arg2@@1))
)))
(assert (forall ((s@@13 T@U) (i@@6 Int) (v@@30 T@U) (x@@34 T@U) ) (! (let ((T@@104 (type v@@30)))
 (=> (and (and (= (type s@@13) (SeqType T@@104)) (= (type x@@34) T@@104)) (and (<= 0 i@@6) (< i@@6 (|Seq#Length| s@@13)))) (= (U_2_int (MapType0Select (|MultiSet#FromSeq| (|Seq#Update| s@@13 i@@6 v@@30)) x@@34)) (U_2_int (MapType0Select (|MultiSet#Union| (|MultiSet#Difference| (|MultiSet#FromSeq| s@@13) (|MultiSet#Singleton| (|Seq#Index| s@@13 i@@6))) (|MultiSet#Singleton| v@@30)) x@@34)))))
 :qid |DafnyPreludebpl.909:18|
 :skolemid |563|
 :pattern ( (MapType0Select (|MultiSet#FromSeq| (|Seq#Update| s@@13 i@@6 v@@30)) x@@34))
)))
(assert (forall ((s@@14 T@U) (x@@35 T@U) ) (! (let ((T@@105 (type x@@35)))
 (=> (= (type s@@14) (SeqType T@@105)) (= (exists ((i@@7 Int) ) (!  (and (and (<= 0 i@@7) (< i@@7 (|Seq#Length| s@@14))) (= x@@35 (|Seq#Index| s@@14 i@@7)))
 :qid |DafnyPreludebpl.916:11|
 :skolemid |564|
 :pattern ( (|Seq#Index| s@@14 i@@7))
)) (< 0 (U_2_int (MapType0Select (|MultiSet#FromSeq| s@@14) x@@35))))))
 :qid |DafnyPreludebpl.915:18|
 :skolemid |565|
 :pattern ( (MapType0Select (|MultiSet#FromSeq| s@@14) x@@35))
)))
(assert (forall ((s@@15 T@U) ) (! (let ((T@@106 (SeqTypeInv0 (type s@@15))))
 (=> (= (type s@@15) (SeqType T@@106)) (<= 0 (|Seq#Length| s@@15))))
 :qid |DafnyPreludebpl.925:18|
 :skolemid |566|
 :pattern ( (|Seq#Length| s@@15))
)))
(assert (forall ((T@@107 T@T) ) (! (= (|Seq#Length| (|Seq#Empty| T@@107)) 0)
 :skolemid |567|
 :pattern ( (|Seq#Empty| T@@107))
)))
(assert (forall ((s@@16 T@U) ) (! (let ((T@@108 (SeqTypeInv0 (type s@@16))))
 (=> (and (= (type s@@16) (SeqType T@@108)) (= (|Seq#Length| s@@16) 0)) (= s@@16 (|Seq#Empty| T@@108))))
 :qid |DafnyPreludebpl.929:18|
 :skolemid |568|
 :pattern ( (|Seq#Length| s@@16))
)))
(assert (forall ((arg0@@94 T@U) ) (! (let ((T@@109 (type arg0@@94)))
(= (type (|Seq#Singleton| arg0@@94)) (SeqType T@@109)))
 :qid |funType:Seq#Singleton|
 :pattern ( (|Seq#Singleton| arg0@@94))
)))
(assert (forall ((t@@23 T@U) ) (! (= (|Seq#Length| (|Seq#Singleton| t@@23)) 1)
 :qid |DafnyPreludebpl.942:18|
 :skolemid |569|
 :pattern ( (|Seq#Length| (|Seq#Singleton| t@@23)))
)))
(assert  (and (forall ((arg0@@95 T@U) ) (! (let ((T@@110 (SeqTypeInv0 (type arg0@@95))))
(= (type (|Seq#Build_inv0| arg0@@95)) (SeqType T@@110)))
 :qid |funType:Seq#Build_inv0|
 :pattern ( (|Seq#Build_inv0| arg0@@95))
)) (forall ((arg0@@96 T@U) ) (! (let ((T@@111 (SeqTypeInv0 (type arg0@@96))))
(= (type (|Seq#Build_inv1| arg0@@96)) T@@111))
 :qid |funType:Seq#Build_inv1|
 :pattern ( (|Seq#Build_inv1| arg0@@96))
))))
(assert (forall ((s@@17 T@U) (val@@5 T@U) ) (! (let ((T@@112 (type val@@5)))
 (=> (= (type s@@17) (SeqType T@@112)) (and (= (|Seq#Build_inv0| (|Seq#Build| s@@17 val@@5)) s@@17) (= (|Seq#Build_inv1| (|Seq#Build| s@@17 val@@5)) val@@5))))
 :qid |DafnyPreludebpl.947:18|
 :skolemid |570|
 :pattern ( (|Seq#Build| s@@17 val@@5))
)))
(assert (forall ((s@@18 T@U) (v@@31 T@U) ) (! (let ((T@@113 (type v@@31)))
 (=> (= (type s@@18) (SeqType T@@113)) (= (|Seq#Length| (|Seq#Build| s@@18 v@@31)) (+ 1 (|Seq#Length| s@@18)))))
 :qid |DafnyPreludebpl.952:18|
 :skolemid |571|
 :pattern ( (|Seq#Build| s@@18 v@@31))
)))
(assert (forall ((s@@19 T@U) (i@@8 Int) (v@@32 T@U) ) (! (let ((T@@114 (type v@@32)))
 (=> (= (type s@@19) (SeqType T@@114)) (and (=> (= i@@8 (|Seq#Length| s@@19)) (= (|Seq#Index| (|Seq#Build| s@@19 v@@32) i@@8) v@@32)) (=> (not (= i@@8 (|Seq#Length| s@@19))) (= (|Seq#Index| (|Seq#Build| s@@19 v@@32) i@@8) (|Seq#Index| s@@19 i@@8))))))
 :qid |DafnyPreludebpl.955:18|
 :skolemid |572|
 :pattern ( (|Seq#Index| (|Seq#Build| s@@19 v@@32) i@@8))
)))
(assert (forall ((s@@20 T@U) (bx@@23 T@U) (t@@24 T@U) ) (!  (=> (and (and (and (= (type s@@20) (SeqType BoxType)) (= (type bx@@23) BoxType)) (= (type t@@24) TyType)) (and ($Is s@@20 (TSeq t@@24)) ($IsBox bx@@23 t@@24))) ($Is (|Seq#Build| s@@20 bx@@23) (TSeq t@@24)))
 :qid |DafnyPreludebpl.960:15|
 :skolemid |573|
 :pattern ( ($Is (|Seq#Build| s@@20 bx@@23) (TSeq t@@24)))
)))
(assert  (and (= (Ctor HandleTypeType) 23) (forall ((arg0@@97 T@U) (arg1@@39 T@U) (arg2@@2 Int) (arg3 T@U) ) (! (= (type (|Seq#Create| arg0@@97 arg1@@39 arg2@@2 arg3)) (SeqType BoxType))
 :qid |funType:Seq#Create|
 :pattern ( (|Seq#Create| arg0@@97 arg1@@39 arg2@@2 arg3))
))))
(assert (forall ((ty T@U) (heap T@U) (len Int) (init T@U) ) (!  (=> (and (and (and (= (type ty) TyType) (= (type heap) (MapType0Type refType MapType1Type))) (= (type init) HandleTypeType)) (and ($IsGoodHeap heap) (<= 0 len))) (= (|Seq#Length| (|Seq#Create| ty heap len init)) len))
 :qid |DafnyPreludebpl.964:15|
 :skolemid |574|
 :pattern ( (|Seq#Length| (|Seq#Create| ty heap len init)))
)))
(assert (forall ((arg0@@98 T@U) (arg1@@40 T@U) (arg2@@3 T@U) (arg3@@0 T@U) (arg4 T@U) ) (! (= (type (Apply1 arg0@@98 arg1@@40 arg2@@3 arg3@@0 arg4)) BoxType)
 :qid |funType:Apply1|
 :pattern ( (Apply1 arg0@@98 arg1@@40 arg2@@3 arg3@@0 arg4))
)))
(assert (forall ((ty@@0 T@U) (heap@@0 T@U) (len@@0 Int) (init@@0 T@U) (i@@9 Int) ) (!  (=> (and (and (and (= (type ty@@0) TyType) (= (type heap@@0) (MapType0Type refType MapType1Type))) (= (type init@@0) HandleTypeType)) (and (and ($IsGoodHeap heap@@0) (<= 0 i@@9)) (< i@@9 len@@0))) (= (|Seq#Index| (|Seq#Create| ty@@0 heap@@0 len@@0 init@@0) i@@9) (Apply1 TInt (TSeq ty@@0) heap@@0 init@@0 ($Box (int_2_U i@@9)))))
 :qid |DafnyPreludebpl.968:15|
 :skolemid |575|
 :pattern ( (|Seq#Index| (|Seq#Create| ty@@0 heap@@0 len@@0 init@@0) i@@9))
)))
(assert (forall ((s0 T@U) (s1 T@U) ) (! (let ((T@@115 (SeqTypeInv0 (type s0))))
 (=> (and (= (type s0) (SeqType T@@115)) (= (type s1) (SeqType T@@115))) (= (|Seq#Length| (|Seq#Append| s0 s1)) (+ (|Seq#Length| s0) (|Seq#Length| s1)))))
 :qid |DafnyPreludebpl.974:18|
 :skolemid |576|
 :pattern ( (|Seq#Length| (|Seq#Append| s0 s1)))
)))
(assert (forall ((t@@25 T@U) ) (! (= (|Seq#Index| (|Seq#Singleton| t@@25) 0) t@@25)
 :qid |DafnyPreludebpl.978:18|
 :skolemid |577|
 :pattern ( (|Seq#Index| (|Seq#Singleton| t@@25) 0))
)))
(assert (forall ((s0@@0 T@U) (s1@@0 T@U) (n@@6 Int) ) (! (let ((T@@116 (SeqTypeInv0 (type s0@@0))))
 (=> (and (= (type s0@@0) (SeqType T@@116)) (= (type s1@@0) (SeqType T@@116))) (and (=> (< n@@6 (|Seq#Length| s0@@0)) (= (|Seq#Index| (|Seq#Append| s0@@0 s1@@0) n@@6) (|Seq#Index| s0@@0 n@@6))) (=> (<= (|Seq#Length| s0@@0) n@@6) (= (|Seq#Index| (|Seq#Append| s0@@0 s1@@0) n@@6) (|Seq#Index| s1@@0 (- n@@6 (|Seq#Length| s0@@0))))))))
 :qid |DafnyPreludebpl.979:18|
 :skolemid |578|
 :pattern ( (|Seq#Index| (|Seq#Append| s0@@0 s1@@0) n@@6))
)))
(assert (forall ((s@@21 T@U) (i@@10 Int) (v@@33 T@U) ) (! (let ((T@@117 (type v@@33)))
 (=> (= (type s@@21) (SeqType T@@117)) (=> (and (<= 0 i@@10) (< i@@10 (|Seq#Length| s@@21))) (= (|Seq#Length| (|Seq#Update| s@@21 i@@10 v@@33)) (|Seq#Length| s@@21)))))
 :qid |DafnyPreludebpl.984:18|
 :skolemid |579|
 :pattern ( (|Seq#Length| (|Seq#Update| s@@21 i@@10 v@@33)))
)))
(assert (forall ((s@@22 T@U) (i@@11 Int) (v@@34 T@U) (n@@7 Int) ) (! (let ((T@@118 (type v@@34)))
 (=> (= (type s@@22) (SeqType T@@118)) (=> (and (<= 0 n@@7) (< n@@7 (|Seq#Length| s@@22))) (and (=> (= i@@11 n@@7) (= (|Seq#Index| (|Seq#Update| s@@22 i@@11 v@@34) n@@7) v@@34)) (=> (not (= i@@11 n@@7)) (= (|Seq#Index| (|Seq#Update| s@@22 i@@11 v@@34) n@@7) (|Seq#Index| s@@22 n@@7)))))))
 :qid |DafnyPreludebpl.986:18|
 :skolemid |580|
 :pattern ( (|Seq#Index| (|Seq#Update| s@@22 i@@11 v@@34) n@@7))
)))
(assert (forall ((s@@23 T@U) (x@@36 T@U) ) (! (let ((T@@119 (type x@@36)))
 (=> (= (type s@@23) (SeqType T@@119)) (= (|Seq#Contains| s@@23 x@@36) (exists ((i@@12 Int) ) (!  (and (and (<= 0 i@@12) (< i@@12 (|Seq#Length| s@@23))) (= (|Seq#Index| s@@23 i@@12) x@@36))
 :qid |DafnyPreludebpl.994:13|
 :skolemid |581|
 :pattern ( (|Seq#Index| s@@23 i@@12))
)))))
 :qid |DafnyPreludebpl.992:18|
 :skolemid |582|
 :pattern ( (|Seq#Contains| s@@23 x@@36))
)))
(assert (forall ((x@@37 T@U) ) (! (let ((T@@120 (type x@@37)))
 (not (|Seq#Contains| (|Seq#Empty| T@@120) x@@37)))
 :qid |DafnyPreludebpl.995:18|
 :skolemid |583|
 :pattern ( (let ((T@@120 (type x@@37)))
(|Seq#Contains| (|Seq#Empty| T@@120) x@@37)))
)))
(assert (forall ((s0@@1 T@U) (s1@@1 T@U) (x@@38 T@U) ) (! (let ((T@@121 (type x@@38)))
 (=> (and (= (type s0@@1) (SeqType T@@121)) (= (type s1@@1) (SeqType T@@121))) (= (|Seq#Contains| (|Seq#Append| s0@@1 s1@@1) x@@38)  (or (|Seq#Contains| s0@@1 x@@38) (|Seq#Contains| s1@@1 x@@38)))))
 :qid |DafnyPreludebpl.999:18|
 :skolemid |584|
 :pattern ( (|Seq#Contains| (|Seq#Append| s0@@1 s1@@1) x@@38))
)))
(assert (forall ((s@@24 T@U) (v@@35 T@U) (x@@39 T@U) ) (! (let ((T@@122 (type v@@35)))
 (=> (and (= (type s@@24) (SeqType T@@122)) (= (type x@@39) T@@122)) (= (|Seq#Contains| (|Seq#Build| s@@24 v@@35) x@@39)  (or (= v@@35 x@@39) (|Seq#Contains| s@@24 x@@39)))))
 :qid |DafnyPreludebpl.1004:18|
 :skolemid |585|
 :pattern ( (|Seq#Contains| (|Seq#Build| s@@24 v@@35) x@@39))
)))
(assert (forall ((arg0@@99 T@U) (arg1@@41 Int) ) (! (let ((T@@123 (SeqTypeInv0 (type arg0@@99))))
(= (type (|Seq#Take| arg0@@99 arg1@@41)) (SeqType T@@123)))
 :qid |funType:Seq#Take|
 :pattern ( (|Seq#Take| arg0@@99 arg1@@41))
)))
(assert (forall ((s@@25 T@U) (n@@8 Int) (x@@40 T@U) ) (! (let ((T@@124 (type x@@40)))
 (=> (= (type s@@25) (SeqType T@@124)) (= (|Seq#Contains| (|Seq#Take| s@@25 n@@8) x@@40) (exists ((i@@13 Int) ) (!  (and (and (and (<= 0 i@@13) (< i@@13 n@@8)) (< i@@13 (|Seq#Length| s@@25))) (= (|Seq#Index| s@@25 i@@13) x@@40))
 :qid |DafnyPreludebpl.1011:13|
 :skolemid |586|
 :pattern ( (|Seq#Index| s@@25 i@@13))
)))))
 :qid |DafnyPreludebpl.1008:18|
 :skolemid |587|
 :pattern ( (|Seq#Contains| (|Seq#Take| s@@25 n@@8) x@@40))
)))
(assert (forall ((arg0@@100 T@U) (arg1@@42 Int) ) (! (let ((T@@125 (SeqTypeInv0 (type arg0@@100))))
(= (type (|Seq#Drop| arg0@@100 arg1@@42)) (SeqType T@@125)))
 :qid |funType:Seq#Drop|
 :pattern ( (|Seq#Drop| arg0@@100 arg1@@42))
)))
(assert (forall ((s@@26 T@U) (n@@9 Int) (x@@41 T@U) ) (! (let ((T@@126 (type x@@41)))
 (=> (= (type s@@26) (SeqType T@@126)) (= (|Seq#Contains| (|Seq#Drop| s@@26 n@@9) x@@41) (exists ((i@@14 Int) ) (!  (and (and (and (<= 0 n@@9) (<= n@@9 i@@14)) (< i@@14 (|Seq#Length| s@@26))) (= (|Seq#Index| s@@26 i@@14) x@@41))
 :qid |DafnyPreludebpl.1016:13|
 :skolemid |588|
 :pattern ( (|Seq#Index| s@@26 i@@14))
)))))
 :qid |DafnyPreludebpl.1013:18|
 :skolemid |589|
 :pattern ( (|Seq#Contains| (|Seq#Drop| s@@26 n@@9) x@@41))
)))
(assert (forall ((s0@@2 T@U) (s1@@2 T@U) ) (! (let ((T@@127 (SeqTypeInv0 (type s0@@2))))
 (=> (and (= (type s0@@2) (SeqType T@@127)) (= (type s1@@2) (SeqType T@@127))) (= (|Seq#Equal| s0@@2 s1@@2)  (and (= (|Seq#Length| s0@@2) (|Seq#Length| s1@@2)) (forall ((j Int) ) (!  (=> (and (<= 0 j) (< j (|Seq#Length| s0@@2))) (= (|Seq#Index| s0@@2 j) (|Seq#Index| s1@@2 j)))
 :qid |DafnyPreludebpl.1023:13|
 :skolemid |590|
 :pattern ( (|Seq#Index| s0@@2 j))
 :pattern ( (|Seq#Index| s1@@2 j))
))))))
 :qid |DafnyPreludebpl.1020:18|
 :skolemid |591|
 :pattern ( (|Seq#Equal| s0@@2 s1@@2))
)))
(assert (forall ((a@@67 T@U) (b@@51 T@U) ) (! (let ((T@@128 (SeqTypeInv0 (type a@@67))))
 (=> (and (and (= (type a@@67) (SeqType T@@128)) (= (type b@@51) (SeqType T@@128))) (|Seq#Equal| a@@67 b@@51)) (= a@@67 b@@51)))
 :qid |DafnyPreludebpl.1025:18|
 :skolemid |592|
 :pattern ( (|Seq#Equal| a@@67 b@@51))
)))
(assert (forall ((s0@@3 T@U) (s1@@3 T@U) (n@@10 Int) ) (! (let ((T@@129 (SeqTypeInv0 (type s0@@3))))
 (=> (and (= (type s0@@3) (SeqType T@@129)) (= (type s1@@3) (SeqType T@@129))) (= (|Seq#SameUntil| s0@@3 s1@@3 n@@10) (forall ((j@@0 Int) ) (!  (=> (and (<= 0 j@@0) (< j@@0 n@@10)) (= (|Seq#Index| s0@@3 j@@0) (|Seq#Index| s1@@3 j@@0)))
 :qid |DafnyPreludebpl.1031:13|
 :skolemid |593|
 :pattern ( (|Seq#Index| s0@@3 j@@0))
 :pattern ( (|Seq#Index| s1@@3 j@@0))
)))))
 :qid |DafnyPreludebpl.1029:18|
 :skolemid |594|
 :pattern ( (|Seq#SameUntil| s0@@3 s1@@3 n@@10))
)))
(assert (forall ((s@@27 T@U) (n@@11 Int) ) (! (let ((T@@130 (SeqTypeInv0 (type s@@27))))
 (=> (= (type s@@27) (SeqType T@@130)) (=> (and (<= 0 n@@11) (<= n@@11 (|Seq#Length| s@@27))) (= (|Seq#Length| (|Seq#Take| s@@27 n@@11)) n@@11))))
 :qid |DafnyPreludebpl.1035:18|
 :skolemid |595|
 :pattern ( (|Seq#Length| (|Seq#Take| s@@27 n@@11)))
)))
(assert (forall ((s@@28 T@U) (n@@12 Int) (j@@1 Int) ) (! (let ((T@@131 (SeqTypeInv0 (type s@@28))))
 (=> (= (type s@@28) (SeqType T@@131)) (=> (and (and (<= 0 j@@1) (< j@@1 n@@12)) (< j@@1 (|Seq#Length| s@@28))) (= (|Seq#Index| (|Seq#Take| s@@28 n@@12) j@@1) (|Seq#Index| s@@28 j@@1)))))
 :qid |DafnyPreludebpl.1037:18|
 :weight 25
 :skolemid |596|
 :pattern ( (|Seq#Index| (|Seq#Take| s@@28 n@@12) j@@1))
 :pattern ( (|Seq#Index| s@@28 j@@1) (|Seq#Take| s@@28 n@@12))
)))
(assert (forall ((s@@29 T@U) (n@@13 Int) ) (! (let ((T@@132 (SeqTypeInv0 (type s@@29))))
 (=> (= (type s@@29) (SeqType T@@132)) (=> (and (<= 0 n@@13) (<= n@@13 (|Seq#Length| s@@29))) (= (|Seq#Length| (|Seq#Drop| s@@29 n@@13)) (- (|Seq#Length| s@@29) n@@13)))))
 :qid |DafnyPreludebpl.1045:18|
 :skolemid |597|
 :pattern ( (|Seq#Length| (|Seq#Drop| s@@29 n@@13)))
)))
(assert (forall ((s@@30 T@U) (n@@14 Int) (j@@2 Int) ) (! (let ((T@@133 (SeqTypeInv0 (type s@@30))))
 (=> (= (type s@@30) (SeqType T@@133)) (=> (and (and (<= 0 n@@14) (<= 0 j@@2)) (< j@@2 (- (|Seq#Length| s@@30) n@@14))) (= (|Seq#Index| (|Seq#Drop| s@@30 n@@14) j@@2) (|Seq#Index| s@@30 (+ j@@2 n@@14))))))
 :qid |DafnyPreludebpl.1047:18|
 :weight 25
 :skolemid |598|
 :pattern ( (|Seq#Index| (|Seq#Drop| s@@30 n@@14) j@@2))
)))
(assert (forall ((s@@31 T@U) (n@@15 Int) (k@@3 Int) ) (! (let ((T@@134 (SeqTypeInv0 (type s@@31))))
 (=> (= (type s@@31) (SeqType T@@134)) (=> (and (and (<= 0 n@@15) (<= n@@15 k@@3)) (< k@@3 (|Seq#Length| s@@31))) (= (|Seq#Index| (|Seq#Drop| s@@31 n@@15) (- k@@3 n@@15)) (|Seq#Index| s@@31 k@@3)))))
 :qid |DafnyPreludebpl.1052:18|
 :weight 25
 :skolemid |599|
 :pattern ( (|Seq#Index| s@@31 k@@3) (|Seq#Drop| s@@31 n@@15))
)))
(assert (forall ((s@@32 T@U) (t@@26 T@U) (n@@16 Int) ) (! (let ((T@@135 (SeqTypeInv0 (type s@@32))))
 (=> (and (and (= (type s@@32) (SeqType T@@135)) (= (type t@@26) (SeqType T@@135))) (= n@@16 (|Seq#Length| s@@32))) (and (= (|Seq#Take| (|Seq#Append| s@@32 t@@26) n@@16) s@@32) (= (|Seq#Drop| (|Seq#Append| s@@32 t@@26) n@@16) t@@26))))
 :qid |DafnyPreludebpl.1058:18|
 :skolemid |600|
 :pattern ( (|Seq#Take| (|Seq#Append| s@@32 t@@26) n@@16))
 :pattern ( (|Seq#Drop| (|Seq#Append| s@@32 t@@26) n@@16))
)))
(assert (forall ((arg0@@101 T@U) (arg1@@43 T@U) ) (! (= (type (|Seq#FromArray| arg0@@101 arg1@@43)) (SeqType BoxType))
 :qid |funType:Seq#FromArray|
 :pattern ( (|Seq#FromArray| arg0@@101 arg1@@43))
)))
(assert (forall ((h@@17 T@U) (a@@68 T@U) ) (!  (=> (and (= (type h@@17) (MapType0Type refType MapType1Type)) (= (type a@@68) refType)) (= (|Seq#Length| (|Seq#FromArray| h@@17 a@@68)) (_System.array.Length a@@68)))
 :qid |DafnyPreludebpl.1067:15|
 :skolemid |601|
 :pattern ( (|Seq#Length| (|Seq#FromArray| h@@17 a@@68)))
)))
(assert (forall ((h@@18 T@U) (a@@69 T@U) ) (!  (=> (and (= (type h@@18) (MapType0Type refType MapType1Type)) (= (type a@@69) refType)) (forall ((i@@15 Int) ) (!  (=> (and (<= 0 i@@15) (< i@@15 (|Seq#Length| (|Seq#FromArray| h@@18 a@@69)))) (= (|Seq#Index| (|Seq#FromArray| h@@18 a@@69) i@@15) (MapType1Select (MapType0Select h@@18 a@@69) (IndexField i@@15))))
 :qid |DafnyPreludebpl.1072:11|
 :skolemid |602|
 :pattern ( (MapType1Select (MapType0Select h@@18 a@@69) (IndexField i@@15)))
 :pattern ( (|Seq#Index| (|Seq#FromArray| h@@18 a@@69) i@@15))
)))
 :qid |DafnyPreludebpl.1070:15|
 :skolemid |603|
 :pattern ( (|Seq#FromArray| h@@18 a@@69))
)))
(assert (forall ((h0 T@U) (h1 T@U) (a@@70 T@U) ) (!  (=> (and (and (= (type h0) (MapType0Type refType MapType1Type)) (= (type h1) (MapType0Type refType MapType1Type))) (= (type a@@70) refType)) (=> (and (and (and ($IsGoodHeap h0) ($IsGoodHeap h1)) ($HeapSucc h0 h1)) (= (MapType0Select h0 a@@70) (MapType0Select h1 a@@70))) (= (|Seq#FromArray| h0 a@@70) (|Seq#FromArray| h1 a@@70))))
 :qid |DafnyPreludebpl.1082:15|
 :skolemid |604|
 :pattern ( (|Seq#FromArray| h1 a@@70) ($HeapSucc h0 h1))
)))
(assert (forall ((h@@19 T@U) (i@@16 Int) (v@@36 T@U) (a@@71 T@U) ) (!  (=> (and (and (and (= (type h@@19) (MapType0Type refType MapType1Type)) (= (type v@@36) BoxType)) (= (type a@@71) refType)) (and (<= 0 i@@16) (< i@@16 (_System.array.Length a@@71)))) (= (|Seq#FromArray| (MapType0Store h@@19 a@@71 (MapType1Store (MapType0Select h@@19 a@@71) (IndexField i@@16) v@@36)) a@@71) (|Seq#Update| (|Seq#FromArray| h@@19 a@@71) i@@16 v@@36)))
 :qid |DafnyPreludebpl.1087:15|
 :skolemid |605|
 :pattern ( (|Seq#FromArray| (MapType0Store h@@19 a@@71 (MapType1Store (MapType0Select h@@19 a@@71) (IndexField i@@16) v@@36)) a@@71))
)))
(assert (forall ((s@@33 T@U) (i@@17 Int) (v@@37 T@U) (n@@17 Int) ) (! (let ((T@@136 (type v@@37)))
 (=> (= (type s@@33) (SeqType T@@136)) (=> (and (and (<= 0 i@@17) (< i@@17 n@@17)) (<= n@@17 (|Seq#Length| s@@33))) (= (|Seq#Take| (|Seq#Update| s@@33 i@@17 v@@37) n@@17) (|Seq#Update| (|Seq#Take| s@@33 n@@17) i@@17 v@@37)))))
 :qid |DafnyPreludebpl.1092:18|
 :skolemid |606|
 :pattern ( (|Seq#Take| (|Seq#Update| s@@33 i@@17 v@@37) n@@17))
)))
(assert (forall ((s@@34 T@U) (i@@18 Int) (v@@38 T@U) (n@@18 Int) ) (! (let ((T@@137 (type v@@38)))
 (=> (= (type s@@34) (SeqType T@@137)) (=> (and (<= n@@18 i@@18) (< i@@18 (|Seq#Length| s@@34))) (= (|Seq#Take| (|Seq#Update| s@@34 i@@18 v@@38) n@@18) (|Seq#Take| s@@34 n@@18)))))
 :qid |DafnyPreludebpl.1095:18|
 :skolemid |607|
 :pattern ( (|Seq#Take| (|Seq#Update| s@@34 i@@18 v@@38) n@@18))
)))
(assert (forall ((s@@35 T@U) (i@@19 Int) (v@@39 T@U) (n@@19 Int) ) (! (let ((T@@138 (type v@@39)))
 (=> (= (type s@@35) (SeqType T@@138)) (=> (and (and (<= 0 n@@19) (<= n@@19 i@@19)) (< i@@19 (|Seq#Length| s@@35))) (= (|Seq#Drop| (|Seq#Update| s@@35 i@@19 v@@39) n@@19) (|Seq#Update| (|Seq#Drop| s@@35 n@@19) (- i@@19 n@@19) v@@39)))))
 :qid |DafnyPreludebpl.1098:18|
 :skolemid |608|
 :pattern ( (|Seq#Drop| (|Seq#Update| s@@35 i@@19 v@@39) n@@19))
)))
(assert (forall ((s@@36 T@U) (i@@20 Int) (v@@40 T@U) (n@@20 Int) ) (! (let ((T@@139 (type v@@40)))
 (=> (= (type s@@36) (SeqType T@@139)) (=> (and (and (<= 0 i@@20) (< i@@20 n@@20)) (< n@@20 (|Seq#Length| s@@36))) (= (|Seq#Drop| (|Seq#Update| s@@36 i@@20 v@@40) n@@20) (|Seq#Drop| s@@36 n@@20)))))
 :qid |DafnyPreludebpl.1101:18|
 :skolemid |609|
 :pattern ( (|Seq#Drop| (|Seq#Update| s@@36 i@@20 v@@40) n@@20))
)))
(assert (forall ((h@@20 T@U) (a@@72 T@U) (n0 Int) (n1 Int) ) (!  (=> (and (= (type h@@20) (MapType0Type refType MapType1Type)) (= (type a@@72) refType)) (=> (and (and (= (+ n0 1) n1) (<= 0 n0)) (<= n1 (_System.array.Length a@@72))) (= (|Seq#Take| (|Seq#FromArray| h@@20 a@@72) n1) (|Seq#Build| (|Seq#Take| (|Seq#FromArray| h@@20 a@@72) n0) (MapType1Select (MapType0Select h@@20 a@@72) (IndexField n0))))))
 :qid |DafnyPreludebpl.1105:15|
 :skolemid |610|
 :pattern ( (|Seq#Take| (|Seq#FromArray| h@@20 a@@72) n0) (|Seq#Take| (|Seq#FromArray| h@@20 a@@72) n1))
)))
(assert (forall ((s@@37 T@U) (v@@41 T@U) (n@@21 Int) ) (! (let ((T@@140 (type v@@41)))
 (=> (= (type s@@37) (SeqType T@@140)) (=> (and (<= 0 n@@21) (<= n@@21 (|Seq#Length| s@@37))) (= (|Seq#Drop| (|Seq#Build| s@@37 v@@41) n@@21) (|Seq#Build| (|Seq#Drop| s@@37 n@@21) v@@41)))))
 :qid |DafnyPreludebpl.1109:18|
 :skolemid |611|
 :pattern ( (|Seq#Drop| (|Seq#Build| s@@37 v@@41) n@@21))
)))
(assert (forall ((s@@38 T@U) (i@@21 Int) ) (!  (=> (= (type s@@38) (SeqType BoxType)) (=> (and (<= 0 i@@21) (< i@@21 (|Seq#Length| s@@38))) (< (DtRank ($Unbox DatatypeTypeType (|Seq#Index| s@@38 i@@21))) (|Seq#Rank| s@@38))))
 :qid |DafnyPreludebpl.1114:15|
 :skolemid |612|
 :pattern ( (DtRank ($Unbox DatatypeTypeType (|Seq#Index| s@@38 i@@21))))
)))
(assert (forall ((s@@39 T@U) (i@@22 Int) ) (! (let ((T@@141 (SeqTypeInv0 (type s@@39))))
 (=> (= (type s@@39) (SeqType T@@141)) (=> (and (< 0 i@@22) (<= i@@22 (|Seq#Length| s@@39))) (< (|Seq#Rank| (|Seq#Drop| s@@39 i@@22)) (|Seq#Rank| s@@39)))))
 :qid |DafnyPreludebpl.1117:18|
 :skolemid |613|
 :pattern ( (|Seq#Rank| (|Seq#Drop| s@@39 i@@22)))
)))
(assert (forall ((s@@40 T@U) (i@@23 Int) ) (! (let ((T@@142 (SeqTypeInv0 (type s@@40))))
 (=> (= (type s@@40) (SeqType T@@142)) (=> (and (<= 0 i@@23) (< i@@23 (|Seq#Length| s@@40))) (< (|Seq#Rank| (|Seq#Take| s@@40 i@@23)) (|Seq#Rank| s@@40)))))
 :qid |DafnyPreludebpl.1120:18|
 :skolemid |614|
 :pattern ( (|Seq#Rank| (|Seq#Take| s@@40 i@@23)))
)))
(assert (forall ((s@@41 T@U) (i@@24 Int) (j@@3 Int) ) (! (let ((T@@143 (SeqTypeInv0 (type s@@41))))
 (=> (= (type s@@41) (SeqType T@@143)) (=> (and (and (<= 0 i@@24) (< i@@24 j@@3)) (<= j@@3 (|Seq#Length| s@@41))) (< (|Seq#Rank| (|Seq#Append| (|Seq#Take| s@@41 i@@24) (|Seq#Drop| s@@41 j@@3))) (|Seq#Rank| s@@41)))))
 :qid |DafnyPreludebpl.1123:18|
 :skolemid |615|
 :pattern ( (|Seq#Rank| (|Seq#Append| (|Seq#Take| s@@41 i@@24) (|Seq#Drop| s@@41 j@@3))))
)))
(assert (forall ((s@@42 T@U) (n@@22 Int) ) (! (let ((T@@144 (SeqTypeInv0 (type s@@42))))
 (=> (and (= (type s@@42) (SeqType T@@144)) (= n@@22 0)) (= (|Seq#Drop| s@@42 n@@22) s@@42)))
 :qid |DafnyPreludebpl.1128:18|
 :skolemid |616|
 :pattern ( (|Seq#Drop| s@@42 n@@22))
)))
(assert (forall ((s@@43 T@U) (n@@23 Int) ) (! (let ((T@@145 (SeqTypeInv0 (type s@@43))))
 (=> (and (= (type s@@43) (SeqType T@@145)) (= n@@23 0)) (= (|Seq#Take| s@@43 n@@23) (|Seq#Empty| T@@145))))
 :qid |DafnyPreludebpl.1130:18|
 :skolemid |617|
 :pattern ( (|Seq#Take| s@@43 n@@23))
)))
(assert (forall ((s@@44 T@U) (m@@9 Int) (n@@24 Int) ) (! (let ((T@@146 (SeqTypeInv0 (type s@@44))))
 (=> (= (type s@@44) (SeqType T@@146)) (=> (and (and (<= 0 m@@9) (<= 0 n@@24)) (<= (+ m@@9 n@@24) (|Seq#Length| s@@44))) (= (|Seq#Drop| (|Seq#Drop| s@@44 m@@9) n@@24) (|Seq#Drop| s@@44 (+ m@@9 n@@24))))))
 :qid |DafnyPreludebpl.1132:18|
 :skolemid |618|
 :pattern ( (|Seq#Drop| (|Seq#Drop| s@@44 m@@9) n@@24))
)))
(assert (forall ((m@@10 T@U) ) (! (let ((V@@3 (MapTypeInv1 (type m@@10))))
(let ((U@@3 (MapTypeInv0 (type m@@10))))
 (=> (= (type m@@10) (MapType U@@3 V@@3)) (<= 0 (|Map#Card| m@@10)))))
 :qid |DafnyPreludebpl.1150:20|
 :skolemid |619|
 :pattern ( (|Map#Card| m@@10))
)))
(assert (forall ((U@@4 T@T) (V@@4 T@T) ) (! (= (type (|Map#Empty| U@@4 V@@4)) (MapType U@@4 V@@4))
 :qid |funType:Map#Empty|
 :pattern ( (|Map#Empty| U@@4 V@@4))
)))
(assert (forall ((m@@11 T@U) ) (! (let ((V@@5 (MapTypeInv1 (type m@@11))))
(let ((U@@5 (MapTypeInv0 (type m@@11))))
 (=> (= (type m@@11) (MapType U@@5 V@@5)) (= (= (|Map#Card| m@@11) 0) (= m@@11 (|Map#Empty| U@@5 V@@5))))))
 :qid |DafnyPreludebpl.1152:21|
 :skolemid |620|
 :pattern ( (|Map#Card| m@@11))
)))
(assert (forall ((m@@12 T@U) ) (! (let ((V@@6 (MapTypeInv1 (type m@@12))))
(let ((U@@6 (MapTypeInv0 (type m@@12))))
 (=> (= (type m@@12) (MapType U@@6 V@@6)) (or (= m@@12 (|Map#Empty| U@@6 V@@6)) (exists ((k@@4 T@U) ) (!  (and (= (type k@@4) U@@6) (U_2_bool (MapType0Select (|Map#Domain| m@@12) k@@4)))
 :qid |DafnyPreludebpl.1158:31|
 :skolemid |621|
 :no-pattern (type k@@4)
 :no-pattern (U_2_int k@@4)
 :no-pattern (U_2_bool k@@4)
))))))
 :qid |DafnyPreludebpl.1156:21|
 :skolemid |622|
 :pattern ( (|Map#Domain| m@@12))
)))
(assert (forall ((m@@13 T@U) ) (! (let ((V@@7 (MapTypeInv1 (type m@@13))))
(let ((U@@7 (MapTypeInv0 (type m@@13))))
 (=> (= (type m@@13) (MapType U@@7 V@@7)) (or (= m@@13 (|Map#Empty| U@@7 V@@7)) (exists ((v@@42 T@U) ) (!  (and (= (type v@@42) V@@7) (U_2_bool (MapType0Select (|Map#Values| m@@13) v@@42)))
 :qid |DafnyPreludebpl.1161:31|
 :skolemid |623|
 :no-pattern (type v@@42)
 :no-pattern (U_2_int v@@42)
 :no-pattern (U_2_bool v@@42)
))))))
 :qid |DafnyPreludebpl.1159:21|
 :skolemid |624|
 :pattern ( (|Map#Values| m@@13))
)))
(assert (forall ((arg0@@102 T@U) (arg1@@44 T@U) ) (! (= (type (|#_System._tuple#2._#Make2| arg0@@102 arg1@@44)) DatatypeTypeType)
 :qid |funType:#_System._tuple#2._#Make2|
 :pattern ( (|#_System._tuple#2._#Make2| arg0@@102 arg1@@44))
)))
(assert (forall ((m@@14 T@U) ) (! (let ((V@@8 (MapTypeInv1 (type m@@14))))
(let ((U@@8 (MapTypeInv0 (type m@@14))))
 (=> (= (type m@@14) (MapType U@@8 V@@8)) (or (= m@@14 (|Map#Empty| U@@8 V@@8)) (exists ((k@@5 T@U) (v@@43 T@U) ) (!  (and (and (= (type k@@5) BoxType) (= (type v@@43) BoxType)) (U_2_bool (MapType0Select (|Map#Items| m@@14) ($Box (|#_System._tuple#2._#Make2| k@@5 v@@43)))))
 :qid |DafnyPreludebpl.1164:31|
 :skolemid |625|
 :no-pattern (type k@@5)
 :no-pattern (type v@@43)
 :no-pattern (U_2_int k@@5)
 :no-pattern (U_2_bool k@@5)
 :no-pattern (U_2_int v@@43)
 :no-pattern (U_2_bool v@@43)
))))))
 :qid |DafnyPreludebpl.1162:21|
 :skolemid |626|
 :pattern ( (|Map#Items| m@@14))
)))
(assert (forall ((m@@15 T@U) ) (! (let ((V@@9 (MapTypeInv1 (type m@@15))))
(let ((U@@9 (MapTypeInv0 (type m@@15))))
 (=> (= (type m@@15) (MapType U@@9 V@@9)) (= (|Set#Card| (|Map#Domain| m@@15)) (|Map#Card| m@@15)))))
 :qid |DafnyPreludebpl.1166:21|
 :skolemid |627|
 :pattern ( (|Set#Card| (|Map#Domain| m@@15)))
)))
(assert (forall ((m@@16 T@U) ) (! (let ((V@@10 (MapTypeInv1 (type m@@16))))
(let ((U@@10 (MapTypeInv0 (type m@@16))))
 (=> (= (type m@@16) (MapType U@@10 V@@10)) (<= (|Set#Card| (|Map#Values| m@@16)) (|Map#Card| m@@16)))))
 :qid |DafnyPreludebpl.1169:21|
 :skolemid |628|
 :pattern ( (|Set#Card| (|Map#Values| m@@16)))
)))
(assert (forall ((m@@17 T@U) ) (! (let ((V@@11 (MapTypeInv1 (type m@@17))))
(let ((U@@11 (MapTypeInv0 (type m@@17))))
 (=> (= (type m@@17) (MapType U@@11 V@@11)) (= (|Set#Card| (|Map#Items| m@@17)) (|Map#Card| m@@17)))))
 :qid |DafnyPreludebpl.1172:21|
 :skolemid |629|
 :pattern ( (|Set#Card| (|Map#Items| m@@17)))
)))
(assert (forall ((m@@18 T@U) (v@@44 T@U) ) (! (let ((V@@12 (type v@@44)))
(let ((U@@12 (MapTypeInv0 (type m@@18))))
 (=> (= (type m@@18) (MapType U@@12 V@@12)) (= (U_2_bool (MapType0Select (|Map#Values| m@@18) v@@44)) (exists ((u@@5 T@U) ) (!  (and (= (type u@@5) U@@12) (and (U_2_bool (MapType0Select (|Map#Domain| m@@18) u@@5)) (= v@@44 (MapType0Select (|Map#Elements| m@@18) u@@5))))
 :qid |DafnyPreludebpl.1185:10|
 :skolemid |630|
 :pattern ( (MapType0Select (|Map#Domain| m@@18) u@@5))
 :pattern ( (MapType0Select (|Map#Elements| m@@18) u@@5))
))))))
 :qid |DafnyPreludebpl.1183:20|
 :skolemid |631|
 :pattern ( (MapType0Select (|Map#Values| m@@18) v@@44))
)))
(assert  (and (forall ((arg0@@103 T@U) ) (! (= (type (_System.Tuple2._0 arg0@@103)) BoxType)
 :qid |funType:_System.Tuple2._0|
 :pattern ( (_System.Tuple2._0 arg0@@103))
)) (forall ((arg0@@104 T@U) ) (! (= (type (_System.Tuple2._1 arg0@@104)) BoxType)
 :qid |funType:_System.Tuple2._1|
 :pattern ( (_System.Tuple2._1 arg0@@104))
))))
(assert (forall ((m@@19 T@U) (item T@U) ) (!  (=> (and (= (type m@@19) (MapType BoxType BoxType)) (= (type item) BoxType)) (= (U_2_bool (MapType0Select (|Map#Items| m@@19) item))  (and (U_2_bool (MapType0Select (|Map#Domain| m@@19) (_System.Tuple2._0 ($Unbox DatatypeTypeType item)))) (= (MapType0Select (|Map#Elements| m@@19) (_System.Tuple2._0 ($Unbox DatatypeTypeType item))) (_System.Tuple2._1 ($Unbox DatatypeTypeType item))))))
 :qid |DafnyPreludebpl.1204:15|
 :skolemid |632|
 :pattern ( (MapType0Select (|Map#Items| m@@19) item))
)))
(assert (forall ((u@@6 T@U) (V@@13 T@T) ) (! (let ((U@@13 (type u@@6)))
 (not (U_2_bool (MapType0Select (|Map#Domain| (|Map#Empty| U@@13 V@@13)) u@@6))))
 :qid |DafnyPreludebpl.1212:21|
 :skolemid |633|
 :pattern ( (let ((U@@13 (type u@@6)))
(MapType0Select (|Map#Domain| (|Map#Empty| U@@13 V@@13)) u@@6)))
)))
(assert (forall ((arg0@@105 T@U) (arg1@@45 T@U) (arg2@@4 T@U) ) (! (let ((V@@14 (MapType0TypeInv1 (type arg1@@45))))
(let ((U@@14 (MapType0TypeInv0 (type arg0@@105))))
(= (type (|Map#Glue| arg0@@105 arg1@@45 arg2@@4)) (MapType U@@14 V@@14))))
 :qid |funType:Map#Glue|
 :pattern ( (|Map#Glue| arg0@@105 arg1@@45 arg2@@4))
)))
(assert (forall ((a@@73 T@U) (b@@52 T@U) (t@@27 T@U) ) (! (let ((V@@15 (MapType0TypeInv1 (type b@@52))))
(let ((U@@15 (MapType0TypeInv0 (type a@@73))))
 (=> (and (and (= (type a@@73) (MapType0Type U@@15 boolType)) (= (type b@@52) (MapType0Type U@@15 V@@15))) (= (type t@@27) TyType)) (= (|Map#Domain| (|Map#Glue| a@@73 b@@52 t@@27)) a@@73))))
 :qid |DafnyPreludebpl.1217:21|
 :skolemid |634|
 :pattern ( (|Map#Domain| (|Map#Glue| a@@73 b@@52 t@@27)))
)))
(assert (forall ((a@@74 T@U) (b@@53 T@U) (t@@28 T@U) ) (! (let ((V@@16 (MapType0TypeInv1 (type b@@53))))
(let ((U@@16 (MapType0TypeInv0 (type a@@74))))
 (=> (and (and (= (type a@@74) (MapType0Type U@@16 boolType)) (= (type b@@53) (MapType0Type U@@16 V@@16))) (= (type t@@28) TyType)) (= (|Map#Elements| (|Map#Glue| a@@74 b@@53 t@@28)) b@@53))))
 :qid |DafnyPreludebpl.1220:21|
 :skolemid |635|
 :pattern ( (|Map#Elements| (|Map#Glue| a@@74 b@@53 t@@28)))
)))
(assert (forall ((a@@75 T@U) (b@@54 T@U) (t0@@14 T@U) (t1@@5 T@U) ) (!  (=> (and (and (and (and (= (type a@@75) (MapType0Type BoxType boolType)) (= (type b@@54) (MapType0Type BoxType BoxType))) (= (type t0@@14) TyType)) (= (type t1@@5) TyType)) (forall ((bx@@24 T@U) ) (!  (=> (and (= (type bx@@24) BoxType) (U_2_bool (MapType0Select a@@75 bx@@24))) (and ($IsBox bx@@24 t0@@14) ($IsBox (MapType0Select b@@54 bx@@24) t1@@5)))
 :qid |DafnyPreludebpl.1226:11|
 :skolemid |636|
 :no-pattern (type bx@@24)
 :no-pattern (U_2_int bx@@24)
 :no-pattern (U_2_bool bx@@24)
))) ($Is (|Map#Glue| a@@75 b@@54 (TMap t0@@14 t1@@5)) (TMap t0@@14 t1@@5)))
 :qid |DafnyPreludebpl.1223:15|
 :skolemid |637|
 :pattern ( (|Map#Glue| a@@75 b@@54 (TMap t0@@14 t1@@5)))
)))
(assert (forall ((arg0@@106 T@U) (arg1@@46 T@U) (arg2@@5 T@U) ) (! (let ((V@@17 (type arg2@@5)))
(let ((U@@17 (type arg1@@46)))
(= (type (|Map#Build| arg0@@106 arg1@@46 arg2@@5)) (MapType U@@17 V@@17))))
 :qid |funType:Map#Build|
 :pattern ( (|Map#Build| arg0@@106 arg1@@46 arg2@@5))
)))
(assert (forall ((m@@20 T@U) (u@@7 T@U) (|u'| T@U) (v@@45 T@U) ) (! (let ((V@@18 (type v@@45)))
(let ((U@@18 (type u@@7)))
 (=> (and (= (type m@@20) (MapType U@@18 V@@18)) (= (type |u'|) U@@18)) (and (=> (= |u'| u@@7) (and (U_2_bool (MapType0Select (|Map#Domain| (|Map#Build| m@@20 u@@7 v@@45)) |u'|)) (= (MapType0Select (|Map#Elements| (|Map#Build| m@@20 u@@7 v@@45)) |u'|) v@@45))) (=> (not (= |u'| u@@7)) (and (= (U_2_bool (MapType0Select (|Map#Domain| (|Map#Build| m@@20 u@@7 v@@45)) |u'|)) (U_2_bool (MapType0Select (|Map#Domain| m@@20) |u'|))) (= (MapType0Select (|Map#Elements| (|Map#Build| m@@20 u@@7 v@@45)) |u'|) (MapType0Select (|Map#Elements| m@@20) |u'|))))))))
 :qid |DafnyPreludebpl.1237:21|
 :skolemid |638|
 :pattern ( (MapType0Select (|Map#Domain| (|Map#Build| m@@20 u@@7 v@@45)) |u'|))
 :pattern ( (MapType0Select (|Map#Elements| (|Map#Build| m@@20 u@@7 v@@45)) |u'|))
)))
(assert (forall ((m@@21 T@U) (u@@8 T@U) (v@@46 T@U) ) (! (let ((V@@19 (type v@@46)))
(let ((U@@19 (type u@@8)))
 (=> (and (= (type m@@21) (MapType U@@19 V@@19)) (U_2_bool (MapType0Select (|Map#Domain| m@@21) u@@8))) (= (|Map#Card| (|Map#Build| m@@21 u@@8 v@@46)) (|Map#Card| m@@21)))))
 :qid |DafnyPreludebpl.1243:21|
 :skolemid |639|
 :pattern ( (|Map#Card| (|Map#Build| m@@21 u@@8 v@@46)))
)))
(assert (forall ((m@@22 T@U) (u@@9 T@U) (v@@47 T@U) ) (! (let ((V@@20 (type v@@47)))
(let ((U@@20 (type u@@9)))
 (=> (and (= (type m@@22) (MapType U@@20 V@@20)) (not (U_2_bool (MapType0Select (|Map#Domain| m@@22) u@@9)))) (= (|Map#Card| (|Map#Build| m@@22 u@@9 v@@47)) (+ (|Map#Card| m@@22) 1)))))
 :qid |DafnyPreludebpl.1245:21|
 :skolemid |640|
 :pattern ( (|Map#Card| (|Map#Build| m@@22 u@@9 v@@47)))
)))
(assert (forall ((arg0@@107 T@U) (arg1@@47 T@U) ) (! (let ((V@@21 (MapTypeInv1 (type arg0@@107))))
(let ((U@@21 (MapTypeInv0 (type arg0@@107))))
(= (type (|Map#Merge| arg0@@107 arg1@@47)) (MapType U@@21 V@@21))))
 :qid |funType:Map#Merge|
 :pattern ( (|Map#Merge| arg0@@107 arg1@@47))
)))
(assert (forall ((m@@23 T@U) (n@@25 T@U) ) (! (let ((V@@22 (MapTypeInv1 (type m@@23))))
(let ((U@@22 (MapTypeInv0 (type m@@23))))
 (=> (and (= (type m@@23) (MapType U@@22 V@@22)) (= (type n@@25) (MapType U@@22 V@@22))) (= (|Map#Domain| (|Map#Merge| m@@23 n@@25)) (|Set#Union| (|Map#Domain| m@@23) (|Map#Domain| n@@25))))))
 :qid |DafnyPreludebpl.1250:21|
 :skolemid |641|
 :pattern ( (|Map#Domain| (|Map#Merge| m@@23 n@@25)))
)))
(assert (forall ((m@@24 T@U) (n@@26 T@U) (u@@10 T@U) ) (! (let ((V@@23 (MapTypeInv1 (type m@@24))))
(let ((U@@23 (type u@@10)))
 (=> (and (and (= (type m@@24) (MapType U@@23 V@@23)) (= (type n@@26) (MapType U@@23 V@@23))) (U_2_bool (MapType0Select (|Map#Domain| (|Map#Merge| m@@24 n@@26)) u@@10))) (and (=> (not (U_2_bool (MapType0Select (|Map#Domain| n@@26) u@@10))) (= (MapType0Select (|Map#Elements| (|Map#Merge| m@@24 n@@26)) u@@10) (MapType0Select (|Map#Elements| m@@24) u@@10))) (=> (U_2_bool (MapType0Select (|Map#Domain| n@@26) u@@10)) (= (MapType0Select (|Map#Elements| (|Map#Merge| m@@24 n@@26)) u@@10) (MapType0Select (|Map#Elements| n@@26) u@@10)))))))
 :qid |DafnyPreludebpl.1253:21|
 :skolemid |642|
 :pattern ( (MapType0Select (|Map#Elements| (|Map#Merge| m@@24 n@@26)) u@@10))
)))
(assert (forall ((arg0@@108 T@U) (arg1@@48 T@U) ) (! (let ((V@@24 (MapTypeInv1 (type arg0@@108))))
(let ((U@@24 (MapTypeInv0 (type arg0@@108))))
(= (type (|Map#Subtract| arg0@@108 arg1@@48)) (MapType U@@24 V@@24))))
 :qid |funType:Map#Subtract|
 :pattern ( (|Map#Subtract| arg0@@108 arg1@@48))
)))
(assert (forall ((m@@25 T@U) (s@@45 T@U) ) (! (let ((V@@25 (MapTypeInv1 (type m@@25))))
(let ((U@@25 (MapTypeInv0 (type m@@25))))
 (=> (and (= (type m@@25) (MapType U@@25 V@@25)) (= (type s@@45) (MapType0Type U@@25 boolType))) (= (|Map#Domain| (|Map#Subtract| m@@25 s@@45)) (|Set#Difference| (|Map#Domain| m@@25) s@@45)))))
 :qid |DafnyPreludebpl.1260:21|
 :skolemid |643|
 :pattern ( (|Map#Domain| (|Map#Subtract| m@@25 s@@45)))
)))
(assert (forall ((m@@26 T@U) (s@@46 T@U) (u@@11 T@U) ) (! (let ((V@@26 (MapTypeInv1 (type m@@26))))
(let ((U@@26 (type u@@11)))
 (=> (and (and (= (type m@@26) (MapType U@@26 V@@26)) (= (type s@@46) (MapType0Type U@@26 boolType))) (U_2_bool (MapType0Select (|Map#Domain| (|Map#Subtract| m@@26 s@@46)) u@@11))) (= (MapType0Select (|Map#Elements| (|Map#Subtract| m@@26 s@@46)) u@@11) (MapType0Select (|Map#Elements| m@@26) u@@11)))))
 :qid |DafnyPreludebpl.1263:21|
 :skolemid |644|
 :pattern ( (MapType0Select (|Map#Elements| (|Map#Subtract| m@@26 s@@46)) u@@11))
)))
(assert (forall ((m@@27 T@U) (|m'| T@U) ) (! (let ((V@@27 (MapTypeInv1 (type m@@27))))
(let ((U@@27 (MapTypeInv0 (type m@@27))))
 (=> (and (= (type m@@27) (MapType U@@27 V@@27)) (= (type |m'|) (MapType U@@27 V@@27))) (= (|Map#Equal| m@@27 |m'|)  (and (forall ((u@@12 T@U) ) (!  (=> (= (type u@@12) U@@27) (= (U_2_bool (MapType0Select (|Map#Domain| m@@27) u@@12)) (U_2_bool (MapType0Select (|Map#Domain| |m'|) u@@12))))
 :qid |DafnyPreludebpl.1272:35|
 :skolemid |645|
 :no-pattern (type u@@12)
 :no-pattern (U_2_int u@@12)
 :no-pattern (U_2_bool u@@12)
)) (forall ((u@@13 T@U) ) (!  (=> (and (= (type u@@13) U@@27) (U_2_bool (MapType0Select (|Map#Domain| m@@27) u@@13))) (= (MapType0Select (|Map#Elements| m@@27) u@@13) (MapType0Select (|Map#Elements| |m'|) u@@13)))
 :qid |DafnyPreludebpl.1273:35|
 :skolemid |646|
 :no-pattern (type u@@13)
 :no-pattern (U_2_int u@@13)
 :no-pattern (U_2_bool u@@13)
)))))))
 :qid |DafnyPreludebpl.1270:21|
 :skolemid |647|
 :pattern ( (|Map#Equal| m@@27 |m'|))
)))
(assert (forall ((m@@28 T@U) (|m'@@0| T@U) ) (! (let ((V@@28 (MapTypeInv1 (type m@@28))))
(let ((U@@28 (MapTypeInv0 (type m@@28))))
 (=> (and (and (= (type m@@28) (MapType U@@28 V@@28)) (= (type |m'@@0|) (MapType U@@28 V@@28))) (|Map#Equal| m@@28 |m'@@0|)) (= m@@28 |m'@@0|))))
 :qid |DafnyPreludebpl.1275:21|
 :skolemid |648|
 :pattern ( (|Map#Equal| m@@28 |m'@@0|))
)))
(assert (forall ((m@@29 T@U) (|m'@@1| T@U) ) (! (let ((V@@29 (MapTypeInv1 (type m@@29))))
(let ((U@@29 (MapTypeInv0 (type m@@29))))
 (=> (and (= (type m@@29) (MapType U@@29 V@@29)) (= (type |m'@@1|) (MapType U@@29 V@@29))) (= (|Map#Disjoint| m@@29 |m'@@1|) (forall ((o@@43 T@U) ) (!  (=> (= (type o@@43) U@@29) (or (not (U_2_bool (MapType0Select (|Map#Domain| m@@29) o@@43))) (not (U_2_bool (MapType0Select (|Map#Domain| |m'@@1|) o@@43)))))
 :qid |DafnyPreludebpl.1282:38|
 :skolemid |649|
 :pattern ( (MapType0Select (|Map#Domain| m@@29) o@@43))
 :pattern ( (MapType0Select (|Map#Domain| |m'@@1|) o@@43))
))))))
 :qid |DafnyPreludebpl.1280:21|
 :skolemid |650|
 :pattern ( (|Map#Disjoint| m@@29 |m'@@1|))
)))
(assert (forall ((U@@30 T@T) (V@@30 T@T) ) (! (= (type (|IMap#Empty| U@@30 V@@30)) (IMapType U@@30 V@@30))
 :qid |funType:IMap#Empty|
 :pattern ( (|IMap#Empty| U@@30 V@@30))
)))
(assert (forall ((m@@30 T@U) ) (! (let ((V@@31 (IMapTypeInv1 (type m@@30))))
(let ((U@@31 (IMapTypeInv0 (type m@@30))))
 (=> (= (type m@@30) (IMapType U@@31 V@@31)) (or (= m@@30 (|IMap#Empty| U@@31 V@@31)) (exists ((k@@6 T@U) ) (!  (and (= (type k@@6) U@@31) (U_2_bool (MapType0Select (|IMap#Domain| m@@30) k@@6)))
 :qid |DafnyPreludebpl.1298:32|
 :skolemid |651|
 :no-pattern (type k@@6)
 :no-pattern (U_2_int k@@6)
 :no-pattern (U_2_bool k@@6)
))))))
 :qid |DafnyPreludebpl.1296:21|
 :skolemid |652|
 :pattern ( (|IMap#Domain| m@@30))
)))
(assert (forall ((m@@31 T@U) ) (! (let ((V@@32 (IMapTypeInv1 (type m@@31))))
(let ((U@@32 (IMapTypeInv0 (type m@@31))))
 (=> (= (type m@@31) (IMapType U@@32 V@@32)) (or (= m@@31 (|IMap#Empty| U@@32 V@@32)) (exists ((v@@48 T@U) ) (!  (and (= (type v@@48) V@@32) (U_2_bool (MapType0Select (|IMap#Values| m@@31) v@@48)))
 :qid |DafnyPreludebpl.1301:32|
 :skolemid |653|
 :no-pattern (type v@@48)
 :no-pattern (U_2_int v@@48)
 :no-pattern (U_2_bool v@@48)
))))))
 :qid |DafnyPreludebpl.1299:21|
 :skolemid |654|
 :pattern ( (|IMap#Values| m@@31))
)))
(assert (forall ((m@@32 T@U) ) (! (let ((V@@33 (IMapTypeInv1 (type m@@32))))
(let ((U@@33 (IMapTypeInv0 (type m@@32))))
 (=> (= (type m@@32) (IMapType U@@33 V@@33)) (or (= m@@32 (|IMap#Empty| U@@33 V@@33)) (exists ((k@@7 T@U) (v@@49 T@U) ) (!  (and (and (= (type k@@7) BoxType) (= (type v@@49) BoxType)) (U_2_bool (MapType0Select (|IMap#Items| m@@32) ($Box (|#_System._tuple#2._#Make2| k@@7 v@@49)))))
 :qid |DafnyPreludebpl.1304:32|
 :skolemid |655|
 :no-pattern (type k@@7)
 :no-pattern (type v@@49)
 :no-pattern (U_2_int k@@7)
 :no-pattern (U_2_bool k@@7)
 :no-pattern (U_2_int v@@49)
 :no-pattern (U_2_bool v@@49)
))))))
 :qid |DafnyPreludebpl.1302:21|
 :skolemid |656|
 :pattern ( (|IMap#Items| m@@32))
)))
(assert (forall ((m@@33 T@U) ) (! (let ((V@@34 (IMapTypeInv1 (type m@@33))))
(let ((U@@34 (IMapTypeInv0 (type m@@33))))
 (=> (= (type m@@33) (IMapType U@@34 V@@34)) (= (= m@@33 (|IMap#Empty| U@@34 V@@34)) (= (|IMap#Domain| m@@33) (|ISet#Empty| U@@34))))))
 :qid |DafnyPreludebpl.1306:21|
 :skolemid |657|
 :pattern ( (|IMap#Domain| m@@33))
)))
(assert (forall ((m@@34 T@U) ) (! (let ((V@@35 (IMapTypeInv1 (type m@@34))))
(let ((U@@35 (IMapTypeInv0 (type m@@34))))
 (=> (= (type m@@34) (IMapType U@@35 V@@35)) (= (= m@@34 (|IMap#Empty| U@@35 V@@35)) (= (|IMap#Values| m@@34) (|ISet#Empty| V@@35))))))
 :qid |DafnyPreludebpl.1309:21|
 :skolemid |658|
 :pattern ( (|IMap#Values| m@@34))
)))
(assert (forall ((m@@35 T@U) ) (! (let ((V@@36 (IMapTypeInv1 (type m@@35))))
(let ((U@@36 (IMapTypeInv0 (type m@@35))))
 (=> (= (type m@@35) (IMapType U@@36 V@@36)) (= (= m@@35 (|IMap#Empty| U@@36 V@@36)) (= (|IMap#Items| m@@35) (|ISet#Empty| BoxType))))))
 :qid |DafnyPreludebpl.1312:21|
 :skolemid |659|
 :pattern ( (|IMap#Items| m@@35))
)))
(assert (forall ((m@@36 T@U) (v@@50 T@U) ) (! (let ((V@@37 (type v@@50)))
(let ((U@@37 (IMapTypeInv0 (type m@@36))))
 (=> (= (type m@@36) (IMapType U@@37 V@@37)) (= (U_2_bool (MapType0Select (|IMap#Values| m@@36) v@@50)) (exists ((u@@14 T@U) ) (!  (and (= (type u@@14) U@@37) (and (U_2_bool (MapType0Select (|IMap#Domain| m@@36) u@@14)) (= v@@50 (MapType0Select (|IMap#Elements| m@@36) u@@14))))
 :qid |DafnyPreludebpl.1325:10|
 :skolemid |660|
 :pattern ( (MapType0Select (|IMap#Domain| m@@36) u@@14))
 :pattern ( (MapType0Select (|IMap#Elements| m@@36) u@@14))
))))))
 :qid |DafnyPreludebpl.1323:20|
 :skolemid |661|
 :pattern ( (MapType0Select (|IMap#Values| m@@36) v@@50))
)))
(assert (forall ((m@@37 T@U) (item@@0 T@U) ) (!  (=> (and (= (type m@@37) (IMapType BoxType BoxType)) (= (type item@@0) BoxType)) (= (U_2_bool (MapType0Select (|IMap#Items| m@@37) item@@0))  (and (U_2_bool (MapType0Select (|IMap#Domain| m@@37) (_System.Tuple2._0 ($Unbox DatatypeTypeType item@@0)))) (= (MapType0Select (|IMap#Elements| m@@37) (_System.Tuple2._0 ($Unbox DatatypeTypeType item@@0))) (_System.Tuple2._1 ($Unbox DatatypeTypeType item@@0))))))
 :qid |DafnyPreludebpl.1340:15|
 :skolemid |662|
 :pattern ( (MapType0Select (|IMap#Items| m@@37) item@@0))
)))
(assert (forall ((u@@15 T@U) (V@@38 T@T) ) (! (let ((U@@38 (type u@@15)))
 (not (U_2_bool (MapType0Select (|IMap#Domain| (|IMap#Empty| U@@38 V@@38)) u@@15))))
 :qid |DafnyPreludebpl.1347:21|
 :skolemid |663|
 :pattern ( (let ((U@@38 (type u@@15)))
(MapType0Select (|IMap#Domain| (|IMap#Empty| U@@38 V@@38)) u@@15)))
)))
(assert (forall ((arg0@@109 T@U) (arg1@@49 T@U) (arg2@@6 T@U) ) (! (let ((V@@39 (MapType0TypeInv1 (type arg1@@49))))
(let ((U@@39 (MapType0TypeInv0 (type arg0@@109))))
(= (type (|IMap#Glue| arg0@@109 arg1@@49 arg2@@6)) (IMapType U@@39 V@@39))))
 :qid |funType:IMap#Glue|
 :pattern ( (|IMap#Glue| arg0@@109 arg1@@49 arg2@@6))
)))
(assert (forall ((a@@76 T@U) (b@@55 T@U) (t@@29 T@U) ) (! (let ((V@@40 (MapType0TypeInv1 (type b@@55))))
(let ((U@@40 (MapType0TypeInv0 (type a@@76))))
 (=> (and (and (= (type a@@76) (MapType0Type U@@40 boolType)) (= (type b@@55) (MapType0Type U@@40 V@@40))) (= (type t@@29) TyType)) (= (|IMap#Domain| (|IMap#Glue| a@@76 b@@55 t@@29)) a@@76))))
 :qid |DafnyPreludebpl.1352:21|
 :skolemid |664|
 :pattern ( (|IMap#Domain| (|IMap#Glue| a@@76 b@@55 t@@29)))
)))
(assert (forall ((a@@77 T@U) (b@@56 T@U) (t@@30 T@U) ) (! (let ((V@@41 (MapType0TypeInv1 (type b@@56))))
(let ((U@@41 (MapType0TypeInv0 (type a@@77))))
 (=> (and (and (= (type a@@77) (MapType0Type U@@41 boolType)) (= (type b@@56) (MapType0Type U@@41 V@@41))) (= (type t@@30) TyType)) (= (|IMap#Elements| (|IMap#Glue| a@@77 b@@56 t@@30)) b@@56))))
 :qid |DafnyPreludebpl.1355:21|
 :skolemid |665|
 :pattern ( (|IMap#Elements| (|IMap#Glue| a@@77 b@@56 t@@30)))
)))
(assert (forall ((a@@78 T@U) (b@@57 T@U) (t0@@15 T@U) (t1@@6 T@U) ) (!  (=> (and (and (and (and (= (type a@@78) (MapType0Type BoxType boolType)) (= (type b@@57) (MapType0Type BoxType BoxType))) (= (type t0@@15) TyType)) (= (type t1@@6) TyType)) (forall ((bx@@25 T@U) ) (!  (=> (and (= (type bx@@25) BoxType) (U_2_bool (MapType0Select a@@78 bx@@25))) (and ($IsBox bx@@25 t0@@15) ($IsBox (MapType0Select b@@57 bx@@25) t1@@6)))
 :qid |DafnyPreludebpl.1361:11|
 :skolemid |666|
 :no-pattern (type bx@@25)
 :no-pattern (U_2_int bx@@25)
 :no-pattern (U_2_bool bx@@25)
))) ($Is (|Map#Glue| a@@78 b@@57 (TIMap t0@@15 t1@@6)) (TIMap t0@@15 t1@@6)))
 :qid |DafnyPreludebpl.1358:15|
 :skolemid |667|
 :pattern ( (|IMap#Glue| a@@78 b@@57 (TIMap t0@@15 t1@@6)))
)))
(assert (forall ((arg0@@110 T@U) (arg1@@50 T@U) (arg2@@7 T@U) ) (! (let ((V@@42 (type arg2@@7)))
(let ((U@@42 (type arg1@@50)))
(= (type (|IMap#Build| arg0@@110 arg1@@50 arg2@@7)) (IMapType U@@42 V@@42))))
 :qid |funType:IMap#Build|
 :pattern ( (|IMap#Build| arg0@@110 arg1@@50 arg2@@7))
)))
(assert (forall ((m@@38 T@U) (u@@16 T@U) (|u'@@0| T@U) (v@@51 T@U) ) (! (let ((V@@43 (type v@@51)))
(let ((U@@43 (type u@@16)))
 (=> (and (= (type m@@38) (IMapType U@@43 V@@43)) (= (type |u'@@0|) U@@43)) (and (=> (= |u'@@0| u@@16) (and (U_2_bool (MapType0Select (|IMap#Domain| (|IMap#Build| m@@38 u@@16 v@@51)) |u'@@0|)) (= (MapType0Select (|IMap#Elements| (|IMap#Build| m@@38 u@@16 v@@51)) |u'@@0|) v@@51))) (=> (not (= |u'@@0| u@@16)) (and (= (U_2_bool (MapType0Select (|IMap#Domain| (|IMap#Build| m@@38 u@@16 v@@51)) |u'@@0|)) (U_2_bool (MapType0Select (|IMap#Domain| m@@38) |u'@@0|))) (= (MapType0Select (|IMap#Elements| (|IMap#Build| m@@38 u@@16 v@@51)) |u'@@0|) (MapType0Select (|IMap#Elements| m@@38) |u'@@0|))))))))
 :qid |DafnyPreludebpl.1371:21|
 :skolemid |668|
 :pattern ( (MapType0Select (|IMap#Domain| (|IMap#Build| m@@38 u@@16 v@@51)) |u'@@0|))
 :pattern ( (MapType0Select (|IMap#Elements| (|IMap#Build| m@@38 u@@16 v@@51)) |u'@@0|))
)))
(assert (forall ((m@@39 T@U) (|m'@@2| T@U) ) (! (let ((V@@44 (IMapTypeInv1 (type m@@39))))
(let ((U@@44 (IMapTypeInv0 (type m@@39))))
 (=> (and (= (type m@@39) (IMapType U@@44 V@@44)) (= (type |m'@@2|) (IMapType U@@44 V@@44))) (= (|IMap#Equal| m@@39 |m'@@2|)  (and (forall ((u@@17 T@U) ) (!  (=> (= (type u@@17) U@@44) (= (U_2_bool (MapType0Select (|IMap#Domain| m@@39) u@@17)) (U_2_bool (MapType0Select (|IMap#Domain| |m'@@2|) u@@17))))
 :qid |DafnyPreludebpl.1382:36|
 :skolemid |669|
 :no-pattern (type u@@17)
 :no-pattern (U_2_int u@@17)
 :no-pattern (U_2_bool u@@17)
)) (forall ((u@@18 T@U) ) (!  (=> (and (= (type u@@18) U@@44) (U_2_bool (MapType0Select (|IMap#Domain| m@@39) u@@18))) (= (MapType0Select (|IMap#Elements| m@@39) u@@18) (MapType0Select (|IMap#Elements| |m'@@2|) u@@18)))
 :qid |DafnyPreludebpl.1383:35|
 :skolemid |670|
 :no-pattern (type u@@18)
 :no-pattern (U_2_int u@@18)
 :no-pattern (U_2_bool u@@18)
)))))))
 :qid |DafnyPreludebpl.1380:21|
 :skolemid |671|
 :pattern ( (|IMap#Equal| m@@39 |m'@@2|))
)))
(assert (forall ((m@@40 T@U) (|m'@@3| T@U) ) (! (let ((V@@45 (IMapTypeInv1 (type m@@40))))
(let ((U@@45 (IMapTypeInv0 (type m@@40))))
 (=> (and (and (= (type m@@40) (IMapType U@@45 V@@45)) (= (type |m'@@3|) (IMapType U@@45 V@@45))) (|IMap#Equal| m@@40 |m'@@3|)) (= m@@40 |m'@@3|))))
 :qid |DafnyPreludebpl.1385:21|
 :skolemid |672|
 :pattern ( (|IMap#Equal| m@@40 |m'@@3|))
)))
(assert (forall ((arg0@@111 T@U) (arg1@@51 T@U) ) (! (let ((V@@46 (IMapTypeInv1 (type arg0@@111))))
(let ((U@@46 (IMapTypeInv0 (type arg0@@111))))
(= (type (|IMap#Merge| arg0@@111 arg1@@51)) (IMapType U@@46 V@@46))))
 :qid |funType:IMap#Merge|
 :pattern ( (|IMap#Merge| arg0@@111 arg1@@51))
)))
(assert (forall ((m@@41 T@U) (n@@27 T@U) ) (! (let ((V@@47 (IMapTypeInv1 (type m@@41))))
(let ((U@@47 (IMapTypeInv0 (type m@@41))))
 (=> (and (= (type m@@41) (IMapType U@@47 V@@47)) (= (type n@@27) (IMapType U@@47 V@@47))) (= (|IMap#Domain| (|IMap#Merge| m@@41 n@@27)) (|Set#Union| (|IMap#Domain| m@@41) (|IMap#Domain| n@@27))))))
 :qid |DafnyPreludebpl.1391:21|
 :skolemid |673|
 :pattern ( (|IMap#Domain| (|IMap#Merge| m@@41 n@@27)))
)))
(assert (forall ((m@@42 T@U) (n@@28 T@U) (u@@19 T@U) ) (! (let ((V@@48 (IMapTypeInv1 (type m@@42))))
(let ((U@@48 (type u@@19)))
 (=> (and (and (= (type m@@42) (IMapType U@@48 V@@48)) (= (type n@@28) (IMapType U@@48 V@@48))) (U_2_bool (MapType0Select (|IMap#Domain| (|IMap#Merge| m@@42 n@@28)) u@@19))) (and (=> (not (U_2_bool (MapType0Select (|IMap#Domain| n@@28) u@@19))) (= (MapType0Select (|IMap#Elements| (|IMap#Merge| m@@42 n@@28)) u@@19) (MapType0Select (|IMap#Elements| m@@42) u@@19))) (=> (U_2_bool (MapType0Select (|IMap#Domain| n@@28) u@@19)) (= (MapType0Select (|IMap#Elements| (|IMap#Merge| m@@42 n@@28)) u@@19) (MapType0Select (|IMap#Elements| n@@28) u@@19)))))))
 :qid |DafnyPreludebpl.1394:21|
 :skolemid |674|
 :pattern ( (MapType0Select (|IMap#Elements| (|IMap#Merge| m@@42 n@@28)) u@@19))
)))
(assert (forall ((arg0@@112 T@U) (arg1@@52 T@U) ) (! (let ((V@@49 (IMapTypeInv1 (type arg0@@112))))
(let ((U@@49 (IMapTypeInv0 (type arg0@@112))))
(= (type (|IMap#Subtract| arg0@@112 arg1@@52)) (IMapType U@@49 V@@49))))
 :qid |funType:IMap#Subtract|
 :pattern ( (|IMap#Subtract| arg0@@112 arg1@@52))
)))
(assert (forall ((m@@43 T@U) (s@@47 T@U) ) (! (let ((V@@50 (IMapTypeInv1 (type m@@43))))
(let ((U@@50 (IMapTypeInv0 (type m@@43))))
 (=> (and (= (type m@@43) (IMapType U@@50 V@@50)) (= (type s@@47) (MapType0Type U@@50 boolType))) (= (|IMap#Domain| (|IMap#Subtract| m@@43 s@@47)) (|Set#Difference| (|IMap#Domain| m@@43) s@@47)))))
 :qid |DafnyPreludebpl.1401:21|
 :skolemid |675|
 :pattern ( (|IMap#Domain| (|IMap#Subtract| m@@43 s@@47)))
)))
(assert (forall ((m@@44 T@U) (s@@48 T@U) (u@@20 T@U) ) (! (let ((V@@51 (IMapTypeInv1 (type m@@44))))
(let ((U@@51 (type u@@20)))
 (=> (and (and (= (type m@@44) (IMapType U@@51 V@@51)) (= (type s@@48) (MapType0Type U@@51 boolType))) (U_2_bool (MapType0Select (|IMap#Domain| (|IMap#Subtract| m@@44 s@@48)) u@@20))) (= (MapType0Select (|IMap#Elements| (|IMap#Subtract| m@@44 s@@48)) u@@20) (MapType0Select (|IMap#Elements| m@@44) u@@20)))))
 :qid |DafnyPreludebpl.1404:21|
 :skolemid |676|
 :pattern ( (MapType0Select (|IMap#Elements| (|IMap#Subtract| m@@44 s@@48)) u@@20))
)))
(assert (forall ((x@@42 Int) (y@@12 Int) ) (! (= (INTERNAL_add_boogie x@@42 y@@12) (+ x@@42 y@@12))
 :qid |DafnyPreludebpl.1413:30|
 :skolemid |677|
 :pattern ( (INTERNAL_add_boogie x@@42 y@@12))
)))
(assert (forall ((x@@43 Int) (y@@13 Int) ) (! (= (INTERNAL_sub_boogie x@@43 y@@13) (- x@@43 y@@13))
 :qid |DafnyPreludebpl.1414:30|
 :skolemid |678|
 :pattern ( (INTERNAL_sub_boogie x@@43 y@@13))
)))
(assert (forall ((x@@44 Int) (y@@14 Int) ) (! (= (INTERNAL_mul_boogie x@@44 y@@14) (* x@@44 y@@14))
 :qid |DafnyPreludebpl.1415:30|
 :skolemid |679|
 :pattern ( (INTERNAL_mul_boogie x@@44 y@@14))
)))
(assert (forall ((x@@45 Int) (y@@15 Int) ) (! (= (INTERNAL_div_boogie x@@45 y@@15) (div x@@45 y@@15))
 :qid |DafnyPreludebpl.1416:30|
 :skolemid |680|
 :pattern ( (INTERNAL_div_boogie x@@45 y@@15))
)))
(assert (forall ((x@@46 Int) (y@@16 Int) ) (! (= (INTERNAL_mod_boogie x@@46 y@@16) (mod x@@46 y@@16))
 :qid |DafnyPreludebpl.1417:30|
 :skolemid |681|
 :pattern ( (INTERNAL_mod_boogie x@@46 y@@16))
)))
(assert (forall ((x@@47 Int) (y@@17 Int) ) (! (= (INTERNAL_lt_boogie x@@47 y@@17) (< x@@47 y@@17))
 :qid |DafnyPreludebpl.1418:51|
 :skolemid |682|
 :pattern ( (INTERNAL_lt_boogie x@@47 y@@17))
)))
(assert (forall ((x@@48 Int) (y@@18 Int) ) (! (= (INTERNAL_le_boogie x@@48 y@@18) (<= x@@48 y@@18))
 :qid |DafnyPreludebpl.1419:51|
 :skolemid |683|
 :pattern ( (INTERNAL_le_boogie x@@48 y@@18))
)))
(assert (forall ((x@@49 Int) (y@@19 Int) ) (! (= (INTERNAL_gt_boogie x@@49 y@@19) (> x@@49 y@@19))
 :qid |DafnyPreludebpl.1420:51|
 :skolemid |684|
 :pattern ( (INTERNAL_gt_boogie x@@49 y@@19))
)))
(assert (forall ((x@@50 Int) (y@@20 Int) ) (! (= (INTERNAL_ge_boogie x@@50 y@@20) (>= x@@50 y@@20))
 :qid |DafnyPreludebpl.1421:51|
 :skolemid |685|
 :pattern ( (INTERNAL_ge_boogie x@@50 y@@20))
)))
(assert (forall ((x@@51 Int) (y@@21 Int) ) (! (= (Mul x@@51 y@@21) (* x@@51 y@@21))
 :qid |DafnyPreludebpl.1423:14|
 :skolemid |686|
 :pattern ( (Mul x@@51 y@@21))
)))
(assert (forall ((x@@52 Int) (y@@22 Int) ) (! (= (Div x@@52 y@@22) (div x@@52 y@@22))
 :qid |DafnyPreludebpl.1424:14|
 :skolemid |687|
 :pattern ( (Div x@@52 y@@22))
)))
(assert (forall ((x@@53 Int) (y@@23 Int) ) (! (= (Mod x@@53 y@@23) (mod x@@53 y@@23))
 :qid |DafnyPreludebpl.1425:14|
 :skolemid |688|
 :pattern ( (Mod x@@53 y@@23))
)))
(assert (forall ((x@@54 Int) (y@@24 Int) ) (! (= (Add x@@54 y@@24) (+ x@@54 y@@24))
 :qid |DafnyPreludebpl.1426:14|
 :skolemid |689|
 :pattern ( (Add x@@54 y@@24))
)))
(assert (forall ((x@@55 Int) (y@@25 Int) ) (! (= (Sub x@@55 y@@25) (- x@@55 y@@25))
 :qid |DafnyPreludebpl.1427:14|
 :skolemid |690|
 :pattern ( (Sub x@@55 y@@25))
)))
(assert (forall ((A@@2 T@U) (B T@U) (a@@79 T@U) (b@@58 T@U) ) (!  (=> (and (and (and (and (= (type A@@2) TyType) (= (type B) TyType)) (= (type a@@79) BoxType)) (= (type b@@58) BoxType)) (_System.__default.rank__is__less__than A@@2 B a@@79 b@@58)) (< (BoxRank a@@79) (BoxRank b@@58)))
 :qid |DafnyPreludebpl.1468:15|
 :skolemid |691|
 :pattern ( (_System.__default.rank__is__less__than A@@2 B a@@79 b@@58) (BoxRank a@@79))
 :pattern ( (_System.__default.rank__is__less__than A@@2 B a@@79 b@@58) (BoxRank b@@58))
)))
(assert (forall ((A@@3 T@U) (B@@0 T@U) (a@@80 T@U) (b@@59 T@U) ) (!  (=> (and (and (and (and (= (type A@@3) TyType) (= (type B@@0) TyType)) (= (type a@@80) BoxType)) (= (type b@@59) (SeqType BoxType))) (_System.__default.rank__is__less__than A@@3 B@@0 a@@80 ($Box b@@59))) (< (BoxRank a@@80) (|Seq#Rank| b@@59)))
 :qid |DafnyPreludebpl.1473:15|
 :skolemid |692|
 :pattern ( (_System.__default.rank__is__less__than A@@3 B@@0 a@@80 ($Box b@@59)) (BoxRank a@@80))
 :pattern ( (_System.__default.rank__is__less__than A@@3 B@@0 a@@80 ($Box b@@59)) (|Seq#Rank| b@@59))
)))
(assert (forall ((A@@4 T@U) (B@@1 T@U) (a@@81 T@U) (b@@60 T@U) ) (!  (=> (and (and (and (and (= (type A@@4) TyType) (= (type B@@1) TyType)) (= (type a@@81) (SeqType BoxType))) (= (type b@@60) BoxType)) (_System.__default.rank__is__less__than A@@4 B@@1 ($Box a@@81) b@@60)) (< (|Seq#Rank| a@@81) (BoxRank b@@60)))
 :qid |DafnyPreludebpl.1478:15|
 :skolemid |693|
 :pattern ( (_System.__default.rank__is__less__than A@@4 B@@1 ($Box a@@81) b@@60) (|Seq#Rank| a@@81))
 :pattern ( (_System.__default.rank__is__less__than A@@4 B@@1 ($Box a@@81) b@@60) (BoxRank b@@60))
)))
(assert (= (type Tclass._System.nat) TyType))
(assert (= (Tag Tclass._System.nat) Tagclass._System.nat))
(assert (forall ((arg0@@113 T@U) ) (! (= (type (TagFamily arg0@@113)) TyTagFamilyType)
 :qid |funType:TagFamily|
 :pattern ( (TagFamily arg0@@113))
)))
(assert (= (TagFamily Tclass._System.nat) tytagFamily$nat))
(assert (forall ((bx@@26 T@U) ) (!  (=> (and (= (type bx@@26) BoxType) ($IsBox bx@@26 Tclass._System.nat)) (and (= ($Box ($Unbox intType bx@@26)) bx@@26) ($Is ($Unbox intType bx@@26) Tclass._System.nat)))
 :qid |unknown.0:0|
 :skolemid |694|
 :pattern ( ($IsBox bx@@26 Tclass._System.nat))
)))
(assert (forall ((|x#0| T@U) ) (!  (=> (= (type |x#0|) intType) (= ($Is |x#0| Tclass._System.nat) (INTERNAL_le_boogie 0 (U_2_int |x#0|))))
 :qid |unknown.0:0|
 :skolemid |695|
 :pattern ( ($Is |x#0| Tclass._System.nat))
)))
(assert (forall ((|x#0@@0| T@U) ($h T@U) ) (!  (=> (and (= (type |x#0@@0|) intType) (= (type $h) (MapType0Type refType MapType1Type))) ($IsAlloc |x#0@@0| Tclass._System.nat $h))
 :qid |unknown.0:0|
 :skolemid |696|
 :pattern ( ($IsAlloc |x#0@@0| Tclass._System.nat $h))
)))
(assert (= (Tag Tclass._System.object?) Tagclass._System.object?))
(assert (= (TagFamily Tclass._System.object?) tytagFamily$object))
(assert (forall ((bx@@27 T@U) ) (!  (=> (and (= (type bx@@27) BoxType) ($IsBox bx@@27 Tclass._System.object?)) (and (= ($Box ($Unbox refType bx@@27)) bx@@27) ($Is ($Unbox refType bx@@27) Tclass._System.object?)))
 :qid |unknown.0:0|
 :skolemid |697|
 :pattern ( ($IsBox bx@@27 Tclass._System.object?))
)))
(assert (forall (($o T@U) ) (!  (=> (= (type $o) refType) ($Is $o Tclass._System.object?))
 :qid |unknown.0:0|
 :skolemid |698|
 :pattern ( ($Is $o Tclass._System.object?))
)))
(assert (= (type null) refType))
(assert (forall (($o@@0 T@U) ($h@@0 T@U) ) (!  (=> (and (= (type $o@@0) refType) (= (type $h@@0) (MapType0Type refType MapType1Type))) (= ($IsAlloc $o@@0 Tclass._System.object? $h@@0)  (or (= $o@@0 null) (U_2_bool (MapType1Select (MapType0Select $h@@0 $o@@0) alloc)))))
 :qid |unknown.0:0|
 :skolemid |699|
 :pattern ( ($IsAlloc $o@@0 Tclass._System.object? $h@@0))
)))
(assert (= (type Tclass._System.object) TyType))
(assert (= (Tag Tclass._System.object) Tagclass._System.object))
(assert (= (TagFamily Tclass._System.object) tytagFamily$object))
(assert (forall ((bx@@28 T@U) ) (!  (=> (and (= (type bx@@28) BoxType) ($IsBox bx@@28 Tclass._System.object)) (and (= ($Box ($Unbox refType bx@@28)) bx@@28) ($Is ($Unbox refType bx@@28) Tclass._System.object)))
 :qid |unknown.0:0|
 :skolemid |700|
 :pattern ( ($IsBox bx@@28 Tclass._System.object))
)))
(assert (forall ((|c#0| T@U) ) (!  (=> (= (type |c#0|) refType) (= ($Is |c#0| Tclass._System.object)  (and ($Is |c#0| Tclass._System.object?) (not (= |c#0| null)))))
 :qid |unknown.0:0|
 :skolemid |701|
 :pattern ( ($Is |c#0| Tclass._System.object))
)))
(assert (forall ((|c#0@@0| T@U) ($h@@1 T@U) ) (!  (=> (and (= (type |c#0@@0|) refType) (= (type $h@@1) (MapType0Type refType MapType1Type))) (= ($IsAlloc |c#0@@0| Tclass._System.object $h@@1) ($IsAlloc |c#0@@0| Tclass._System.object? $h@@1)))
 :qid |unknown.0:0|
 :skolemid |702|
 :pattern ( ($IsAlloc |c#0@@0| Tclass._System.object $h@@1))
)))
(assert (forall ((arg0@@114 T@U) ) (! (= (type (Tclass._System.array? arg0@@114)) TyType)
 :qid |funType:Tclass._System.array?|
 :pattern ( (Tclass._System.array? arg0@@114))
)))
(assert (forall ((_System.array$arg T@U) ) (!  (=> (= (type _System.array$arg) TyType) (and (= (Tag (Tclass._System.array? _System.array$arg)) Tagclass._System.array?) (= (TagFamily (Tclass._System.array? _System.array$arg)) tytagFamily$array)))
 :qid |unknown.0:0|
 :skolemid |703|
 :pattern ( (Tclass._System.array? _System.array$arg))
)))
(assert (forall ((arg0@@115 T@U) ) (! (= (type (Tclass._System.array?_0 arg0@@115)) TyType)
 :qid |funType:Tclass._System.array?_0|
 :pattern ( (Tclass._System.array?_0 arg0@@115))
)))
(assert (forall ((_System.array$arg@@0 T@U) ) (!  (=> (= (type _System.array$arg@@0) TyType) (= (Tclass._System.array?_0 (Tclass._System.array? _System.array$arg@@0)) _System.array$arg@@0))
 :qid |unknown.0:0|
 :skolemid |704|
 :pattern ( (Tclass._System.array? _System.array$arg@@0))
)))
(assert (forall ((_System.array$arg@@1 T@U) (bx@@29 T@U) ) (!  (=> (and (and (= (type _System.array$arg@@1) TyType) (= (type bx@@29) BoxType)) ($IsBox bx@@29 (Tclass._System.array? _System.array$arg@@1))) (and (= ($Box ($Unbox refType bx@@29)) bx@@29) ($Is ($Unbox refType bx@@29) (Tclass._System.array? _System.array$arg@@1))))
 :qid |unknown.0:0|
 :skolemid |705|
 :pattern ( ($IsBox bx@@29 (Tclass._System.array? _System.array$arg@@1)))
)))
(assert (forall ((arg0@@116 T@U) ) (! (= (type (dtype arg0@@116)) TyType)
 :qid |funType:dtype|
 :pattern ( (dtype arg0@@116))
)))
(assert (forall ((_System.array$arg@@2 T@U) ($h@@2 T@U) ($o@@1 T@U) ($i0 Int) ) (!  (=> (and (and (and (= (type _System.array$arg@@2) TyType) (= (type $h@@2) (MapType0Type refType MapType1Type))) (= (type $o@@1) refType)) (and (and ($IsGoodHeap $h@@2) (and (not (= $o@@1 null)) (= (dtype $o@@1) (Tclass._System.array? _System.array$arg@@2)))) (and (<= 0 $i0) (< $i0 (_System.array.Length $o@@1))))) ($IsBox (MapType1Select (MapType0Select $h@@2 $o@@1) (IndexField $i0)) _System.array$arg@@2))
 :qid |unknown.0:0|
 :skolemid |706|
 :pattern ( (MapType1Select (MapType0Select $h@@2 $o@@1) (IndexField $i0)) (Tclass._System.array? _System.array$arg@@2))
)))
(assert (forall ((_System.array$arg@@3 T@U) ($h@@3 T@U) ($o@@2 T@U) ($i0@@0 Int) ) (!  (=> (and (and (= (type _System.array$arg@@3) TyType) (= (type $h@@3) (MapType0Type refType MapType1Type))) (= (type $o@@2) refType)) (=> (and (and (and ($IsGoodHeap $h@@3) (and (not (= $o@@2 null)) (= (dtype $o@@2) (Tclass._System.array? _System.array$arg@@3)))) (and (<= 0 $i0@@0) (< $i0@@0 (_System.array.Length $o@@2)))) (U_2_bool (MapType1Select (MapType0Select $h@@3 $o@@2) alloc))) ($IsAllocBox (MapType1Select (MapType0Select $h@@3 $o@@2) (IndexField $i0@@0)) _System.array$arg@@3 $h@@3)))
 :qid |unknown.0:0|
 :skolemid |707|
 :pattern ( (MapType1Select (MapType0Select $h@@3 $o@@2) (IndexField $i0@@0)) (Tclass._System.array? _System.array$arg@@3))
)))
(assert (forall ((_System.array$arg@@4 T@U) ($o@@3 T@U) ) (!  (=> (and (= (type _System.array$arg@@4) TyType) (= (type $o@@3) refType)) (= ($Is $o@@3 (Tclass._System.array? _System.array$arg@@4))  (or (= $o@@3 null) (= (dtype $o@@3) (Tclass._System.array? _System.array$arg@@4)))))
 :qid |unknown.0:0|
 :skolemid |708|
 :pattern ( ($Is $o@@3 (Tclass._System.array? _System.array$arg@@4)))
)))
(assert (forall ((_System.array$arg@@5 T@U) ($o@@4 T@U) ($h@@4 T@U) ) (!  (=> (and (and (= (type _System.array$arg@@5) TyType) (= (type $o@@4) refType)) (= (type $h@@4) (MapType0Type refType MapType1Type))) (= ($IsAlloc $o@@4 (Tclass._System.array? _System.array$arg@@5) $h@@4)  (or (= $o@@4 null) (U_2_bool (MapType1Select (MapType0Select $h@@4 $o@@4) alloc)))))
 :qid |unknown.0:0|
 :skolemid |709|
 :pattern ( ($IsAlloc $o@@4 (Tclass._System.array? _System.array$arg@@5) $h@@4))
)))
(assert (forall ((_System.array$arg@@6 T@U) ($o@@5 T@U) ) (!  (=> (and (and (= (type _System.array$arg@@6) TyType) (= (type $o@@5) refType)) (and (not (= $o@@5 null)) (= (dtype $o@@5) (Tclass._System.array? _System.array$arg@@6)))) ($Is (int_2_U (_System.array.Length $o@@5)) TInt))
 :qid |unknown.0:0|
 :skolemid |710|
 :pattern ( (_System.array.Length $o@@5) (Tclass._System.array? _System.array$arg@@6))
)))
(assert (forall ((_System.array$arg@@7 T@U) ($h@@5 T@U) ($o@@6 T@U) ) (!  (=> (and (and (and (= (type _System.array$arg@@7) TyType) (= (type $h@@5) (MapType0Type refType MapType1Type))) (= (type $o@@6) refType)) (and (and ($IsGoodHeap $h@@5) (and (not (= $o@@6 null)) (= (dtype $o@@6) (Tclass._System.array? _System.array$arg@@7)))) (U_2_bool (MapType1Select (MapType0Select $h@@5 $o@@6) alloc)))) ($IsAlloc (int_2_U (_System.array.Length $o@@6)) TInt $h@@5))
 :qid |unknown.0:0|
 :skolemid |711|
 :pattern ( (_System.array.Length $o@@6) (MapType1Select (MapType0Select $h@@5 $o@@6) alloc) (Tclass._System.array? _System.array$arg@@7))
)))
(assert (forall ((arg0@@117 T@U) ) (! (= (type (Tclass._System.array arg0@@117)) TyType)
 :qid |funType:Tclass._System.array|
 :pattern ( (Tclass._System.array arg0@@117))
)))
(assert (forall ((_System.array$arg@@8 T@U) ) (!  (=> (= (type _System.array$arg@@8) TyType) (and (= (Tag (Tclass._System.array _System.array$arg@@8)) Tagclass._System.array) (= (TagFamily (Tclass._System.array _System.array$arg@@8)) tytagFamily$array)))
 :qid |unknown.0:0|
 :skolemid |712|
 :pattern ( (Tclass._System.array _System.array$arg@@8))
)))
(assert (forall ((arg0@@118 T@U) ) (! (= (type (Tclass._System.array_0 arg0@@118)) TyType)
 :qid |funType:Tclass._System.array_0|
 :pattern ( (Tclass._System.array_0 arg0@@118))
)))
(assert (forall ((_System.array$arg@@9 T@U) ) (!  (=> (= (type _System.array$arg@@9) TyType) (= (Tclass._System.array_0 (Tclass._System.array _System.array$arg@@9)) _System.array$arg@@9))
 :qid |unknown.0:0|
 :skolemid |713|
 :pattern ( (Tclass._System.array _System.array$arg@@9))
)))
(assert (forall ((_System.array$arg@@10 T@U) (bx@@30 T@U) ) (!  (=> (and (and (= (type _System.array$arg@@10) TyType) (= (type bx@@30) BoxType)) ($IsBox bx@@30 (Tclass._System.array _System.array$arg@@10))) (and (= ($Box ($Unbox refType bx@@30)) bx@@30) ($Is ($Unbox refType bx@@30) (Tclass._System.array _System.array$arg@@10))))
 :qid |unknown.0:0|
 :skolemid |714|
 :pattern ( ($IsBox bx@@30 (Tclass._System.array _System.array$arg@@10)))
)))
(assert (forall ((_System.array$arg@@11 T@U) (|c#0@@1| T@U) ) (!  (=> (and (= (type _System.array$arg@@11) TyType) (= (type |c#0@@1|) refType)) (= ($Is |c#0@@1| (Tclass._System.array _System.array$arg@@11))  (and ($Is |c#0@@1| (Tclass._System.array? _System.array$arg@@11)) (not (= |c#0@@1| null)))))
 :qid |unknown.0:0|
 :skolemid |715|
 :pattern ( ($Is |c#0@@1| (Tclass._System.array _System.array$arg@@11)))
)))
(assert (forall ((_System.array$arg@@12 T@U) (|c#0@@2| T@U) ($h@@6 T@U) ) (!  (=> (and (and (= (type _System.array$arg@@12) TyType) (= (type |c#0@@2|) refType)) (= (type $h@@6) (MapType0Type refType MapType1Type))) (= ($IsAlloc |c#0@@2| (Tclass._System.array _System.array$arg@@12) $h@@6) ($IsAlloc |c#0@@2| (Tclass._System.array? _System.array$arg@@12) $h@@6)))
 :qid |unknown.0:0|
 :skolemid |716|
 :pattern ( ($IsAlloc |c#0@@2| (Tclass._System.array _System.array$arg@@12) $h@@6))
)))
(assert (forall ((arg0@@119 T@U) (arg1@@53 T@U) ) (! (= (type (Tclass._System.___hFunc1 arg0@@119 arg1@@53)) TyType)
 :qid |funType:Tclass._System.___hFunc1|
 :pattern ( (Tclass._System.___hFunc1 arg0@@119 arg1@@53))
)))
(assert (forall ((|#$T0| T@U) (|#$R| T@U) ) (!  (=> (and (= (type |#$T0|) TyType) (= (type |#$R|) TyType)) (and (= (Tag (Tclass._System.___hFunc1 |#$T0| |#$R|)) Tagclass._System.___hFunc1) (= (TagFamily (Tclass._System.___hFunc1 |#$T0| |#$R|)) |tytagFamily$_#Func1|)))
 :qid |unknown.0:0|
 :skolemid |717|
 :pattern ( (Tclass._System.___hFunc1 |#$T0| |#$R|))
)))
(assert (forall ((arg0@@120 T@U) ) (! (= (type (Tclass._System.___hFunc1_0 arg0@@120)) TyType)
 :qid |funType:Tclass._System.___hFunc1_0|
 :pattern ( (Tclass._System.___hFunc1_0 arg0@@120))
)))
(assert (forall ((|#$T0@@0| T@U) (|#$R@@0| T@U) ) (!  (=> (and (= (type |#$T0@@0|) TyType) (= (type |#$R@@0|) TyType)) (= (Tclass._System.___hFunc1_0 (Tclass._System.___hFunc1 |#$T0@@0| |#$R@@0|)) |#$T0@@0|))
 :qid |unknown.0:0|
 :skolemid |718|
 :pattern ( (Tclass._System.___hFunc1 |#$T0@@0| |#$R@@0|))
)))
(assert (forall ((arg0@@121 T@U) ) (! (= (type (Tclass._System.___hFunc1_1 arg0@@121)) TyType)
 :qid |funType:Tclass._System.___hFunc1_1|
 :pattern ( (Tclass._System.___hFunc1_1 arg0@@121))
)))
(assert (forall ((|#$T0@@1| T@U) (|#$R@@1| T@U) ) (!  (=> (and (= (type |#$T0@@1|) TyType) (= (type |#$R@@1|) TyType)) (= (Tclass._System.___hFunc1_1 (Tclass._System.___hFunc1 |#$T0@@1| |#$R@@1|)) |#$R@@1|))
 :qid |unknown.0:0|
 :skolemid |719|
 :pattern ( (Tclass._System.___hFunc1 |#$T0@@1| |#$R@@1|))
)))
(assert (forall ((|#$T0@@2| T@U) (|#$R@@2| T@U) (bx@@31 T@U) ) (!  (=> (and (and (and (= (type |#$T0@@2|) TyType) (= (type |#$R@@2|) TyType)) (= (type bx@@31) BoxType)) ($IsBox bx@@31 (Tclass._System.___hFunc1 |#$T0@@2| |#$R@@2|))) (and (= ($Box ($Unbox HandleTypeType bx@@31)) bx@@31) ($Is ($Unbox HandleTypeType bx@@31) (Tclass._System.___hFunc1 |#$T0@@2| |#$R@@2|))))
 :qid |unknown.0:0|
 :skolemid |720|
 :pattern ( ($IsBox bx@@31 (Tclass._System.___hFunc1 |#$T0@@2| |#$R@@2|)))
)))
(assert  (and (and (and (and (and (and (and (and (forall ((arg0@@122 T@T) (arg1@@54 T@T) (arg2@@8 T@T) ) (! (= (Ctor (MapType2Type arg0@@122 arg1@@54 arg2@@8)) 24)
 :qid |ctor:MapType2Type|
)) (forall ((arg0@@123 T@T) (arg1@@55 T@T) (arg2@@9 T@T) ) (! (= (MapType2TypeInv0 (MapType2Type arg0@@123 arg1@@55 arg2@@9)) arg0@@123)
 :qid |typeInv:MapType2TypeInv0|
 :pattern ( (MapType2Type arg0@@123 arg1@@55 arg2@@9))
))) (forall ((arg0@@124 T@T) (arg1@@56 T@T) (arg2@@10 T@T) ) (! (= (MapType2TypeInv1 (MapType2Type arg0@@124 arg1@@56 arg2@@10)) arg1@@56)
 :qid |typeInv:MapType2TypeInv1|
 :pattern ( (MapType2Type arg0@@124 arg1@@56 arg2@@10))
))) (forall ((arg0@@125 T@T) (arg1@@57 T@T) (arg2@@11 T@T) ) (! (= (MapType2TypeInv2 (MapType2Type arg0@@125 arg1@@57 arg2@@11)) arg2@@11)
 :qid |typeInv:MapType2TypeInv2|
 :pattern ( (MapType2Type arg0@@125 arg1@@57 arg2@@11))
))) (forall ((arg0@@126 T@U) (arg1@@58 T@U) (arg2@@12 T@U) ) (! (let ((aVar2 (MapType2TypeInv2 (type arg0@@126))))
(= (type (MapType2Select arg0@@126 arg1@@58 arg2@@12)) aVar2))
 :qid |funType:MapType2Select|
 :pattern ( (MapType2Select arg0@@126 arg1@@58 arg2@@12))
))) (forall ((arg0@@127 T@U) (arg1@@59 T@U) (arg2@@13 T@U) (arg3@@1 T@U) ) (! (let ((aVar2@@0 (type arg3@@1)))
(let ((aVar1@@2 (type arg2@@13)))
(let ((aVar0@@0 (type arg1@@59)))
(= (type (MapType2Store arg0@@127 arg1@@59 arg2@@13 arg3@@1)) (MapType2Type aVar0@@0 aVar1@@2 aVar2@@0)))))
 :qid |funType:MapType2Store|
 :pattern ( (MapType2Store arg0@@127 arg1@@59 arg2@@13 arg3@@1))
))) (forall ((m@@45 T@U) (x0@@5 T@U) (x1 T@U) (val@@6 T@U) ) (! (let ((aVar2@@1 (MapType2TypeInv2 (type m@@45))))
 (=> (= (type val@@6) aVar2@@1) (= (MapType2Select (MapType2Store m@@45 x0@@5 x1 val@@6) x0@@5 x1) val@@6)))
 :qid |mapAx0:MapType2Select|
 :weight 0
))) (and (and (forall ((val@@7 T@U) (m@@46 T@U) (x0@@6 T@U) (x1@@0 T@U) (y0@@3 T@U) (y1 T@U) ) (!  (or (= x0@@6 y0@@3) (= (MapType2Select (MapType2Store m@@46 x0@@6 x1@@0 val@@7) y0@@3 y1) (MapType2Select m@@46 y0@@3 y1)))
 :qid |mapAx1:MapType2Select:0|
 :weight 0
)) (forall ((val@@8 T@U) (m@@47 T@U) (x0@@7 T@U) (x1@@1 T@U) (y0@@4 T@U) (y1@@0 T@U) ) (!  (or (= x1@@1 y1@@0) (= (MapType2Select (MapType2Store m@@47 x0@@7 x1@@1 val@@8) y0@@4 y1@@0) (MapType2Select m@@47 y0@@4 y1@@0)))
 :qid |mapAx1:MapType2Select:1|
 :weight 0
))) (forall ((val@@9 T@U) (m@@48 T@U) (x0@@8 T@U) (x1@@2 T@U) (y0@@5 T@U) (y1@@1 T@U) ) (!  (or true (= (MapType2Select (MapType2Store m@@48 x0@@8 x1@@2 val@@9) y0@@5 y1@@1) (MapType2Select m@@48 y0@@5 y1@@1)))
 :qid |mapAx2:MapType2Select|
 :weight 0
)))) (forall ((arg0@@128 T@U) (arg1@@60 T@U) (arg2@@14 T@U) ) (! (= (type (Handle1 arg0@@128 arg1@@60 arg2@@14)) HandleTypeType)
 :qid |funType:Handle1|
 :pattern ( (Handle1 arg0@@128 arg1@@60 arg2@@14))
))))
(assert (forall ((t0@@16 T@U) (t1@@7 T@U) (heap@@1 T@U) (h@@21 T@U) (r@@6 T@U) (rd T@U) (bx0 T@U) ) (!  (=> (and (and (and (and (and (and (= (type t0@@16) TyType) (= (type t1@@7) TyType)) (= (type heap@@1) (MapType0Type refType MapType1Type))) (= (type h@@21) (MapType2Type (MapType0Type refType MapType1Type) BoxType BoxType))) (= (type r@@6) (MapType2Type (MapType0Type refType MapType1Type) BoxType boolType))) (= (type rd) (MapType2Type (MapType0Type refType MapType1Type) BoxType (MapType0Type BoxType boolType)))) (= (type bx0) BoxType)) (= (Apply1 t0@@16 t1@@7 heap@@1 (Handle1 h@@21 r@@6 rd) bx0) (MapType2Select h@@21 heap@@1 bx0)))
 :qid |unknown.0:0|
 :skolemid |721|
 :pattern ( (Apply1 t0@@16 t1@@7 heap@@1 (Handle1 h@@21 r@@6 rd) bx0))
)))
(assert (forall ((t0@@17 T@U) (t1@@8 T@U) (heap@@2 T@U) (h@@22 T@U) (r@@7 T@U) (rd@@0 T@U) (bx0@@0 T@U) ) (!  (=> (and (and (and (and (and (and (and (= (type t0@@17) TyType) (= (type t1@@8) TyType)) (= (type heap@@2) (MapType0Type refType MapType1Type))) (= (type h@@22) (MapType2Type (MapType0Type refType MapType1Type) BoxType BoxType))) (= (type r@@7) (MapType2Type (MapType0Type refType MapType1Type) BoxType boolType))) (= (type rd@@0) (MapType2Type (MapType0Type refType MapType1Type) BoxType (MapType0Type BoxType boolType)))) (= (type bx0@@0) BoxType)) (U_2_bool (MapType2Select r@@7 heap@@2 bx0@@0))) (Requires1 t0@@17 t1@@8 heap@@2 (Handle1 h@@22 r@@7 rd@@0) bx0@@0))
 :qid |unknown.0:0|
 :skolemid |722|
 :pattern ( (Requires1 t0@@17 t1@@8 heap@@2 (Handle1 h@@22 r@@7 rd@@0) bx0@@0))
)))
(assert (forall ((arg0@@129 T@U) (arg1@@61 T@U) (arg2@@15 T@U) (arg3@@2 T@U) (arg4@@0 T@U) ) (! (= (type (Reads1 arg0@@129 arg1@@61 arg2@@15 arg3@@2 arg4@@0)) (MapType0Type BoxType boolType))
 :qid |funType:Reads1|
 :pattern ( (Reads1 arg0@@129 arg1@@61 arg2@@15 arg3@@2 arg4@@0))
)))
(assert (forall ((t0@@18 T@U) (t1@@9 T@U) (heap@@3 T@U) (h@@23 T@U) (r@@8 T@U) (rd@@1 T@U) (bx0@@1 T@U) (bx@@32 T@U) ) (!  (=> (and (and (and (and (and (and (and (= (type t0@@18) TyType) (= (type t1@@9) TyType)) (= (type heap@@3) (MapType0Type refType MapType1Type))) (= (type h@@23) (MapType2Type (MapType0Type refType MapType1Type) BoxType BoxType))) (= (type r@@8) (MapType2Type (MapType0Type refType MapType1Type) BoxType boolType))) (= (type rd@@1) (MapType2Type (MapType0Type refType MapType1Type) BoxType (MapType0Type BoxType boolType)))) (= (type bx0@@1) BoxType)) (= (type bx@@32) BoxType)) (= (U_2_bool (MapType0Select (Reads1 t0@@18 t1@@9 heap@@3 (Handle1 h@@23 r@@8 rd@@1) bx0@@1) bx@@32)) (U_2_bool (MapType0Select (MapType2Select rd@@1 heap@@3 bx0@@1) bx@@32))))
 :qid |unknown.0:0|
 :skolemid |723|
 :pattern ( (MapType0Select (Reads1 t0@@18 t1@@9 heap@@3 (Handle1 h@@23 r@@8 rd@@1) bx0@@1) bx@@32))
)))
(assert (forall ((t0@@19 T@U) (t1@@10 T@U) (h0@@0 T@U) (h1@@0 T@U) (f@@5 T@U) (bx0@@2 T@U) ) (!  (=> (and (and (and (and (and (and (= (type t0@@19) TyType) (= (type t1@@10) TyType)) (= (type h0@@0) (MapType0Type refType MapType1Type))) (= (type h1@@0) (MapType0Type refType MapType1Type))) (= (type f@@5) HandleTypeType)) (= (type bx0@@2) BoxType)) (and (and (and ($HeapSucc h0@@0 h1@@0) (and ($IsGoodHeap h0@@0) ($IsGoodHeap h1@@0))) (and ($IsBox bx0@@2 t0@@19) ($Is f@@5 (Tclass._System.___hFunc1 t0@@19 t1@@10)))) (forall ((o@@44 T@U) (fld T@U) ) (! (let ((a@@82 (FieldTypeInv0 (type fld))))
 (=> (and (and (= (type o@@44) refType) (= (type fld) (FieldType a@@82))) (and (not (= o@@44 null)) (U_2_bool (MapType0Select (Reads1 t0@@19 t1@@10 h0@@0 f@@5 bx0@@2) ($Box o@@44))))) (= (MapType1Select (MapType0Select h0@@0 o@@44) fld) (MapType1Select (MapType0Select h1@@0 o@@44) fld))))
 :qid |unknown.0:0|
 :skolemid |724|
 :no-pattern (type o@@44)
 :no-pattern (type fld)
 :no-pattern (U_2_int o@@44)
 :no-pattern (U_2_bool o@@44)
 :no-pattern (U_2_int fld)
 :no-pattern (U_2_bool fld)
)))) (= (Reads1 t0@@19 t1@@10 h0@@0 f@@5 bx0@@2) (Reads1 t0@@19 t1@@10 h1@@0 f@@5 bx0@@2)))
 :qid |unknown.0:0|
 :skolemid |725|
 :pattern ( ($HeapSucc h0@@0 h1@@0) (Reads1 t0@@19 t1@@10 h1@@0 f@@5 bx0@@2))
)))
(assert (forall ((t0@@20 T@U) (t1@@11 T@U) (h0@@1 T@U) (h1@@1 T@U) (f@@6 T@U) (bx0@@3 T@U) ) (!  (=> (and (and (and (and (and (and (= (type t0@@20) TyType) (= (type t1@@11) TyType)) (= (type h0@@1) (MapType0Type refType MapType1Type))) (= (type h1@@1) (MapType0Type refType MapType1Type))) (= (type f@@6) HandleTypeType)) (= (type bx0@@3) BoxType)) (and (and (and ($HeapSucc h0@@1 h1@@1) (and ($IsGoodHeap h0@@1) ($IsGoodHeap h1@@1))) (and ($IsBox bx0@@3 t0@@20) ($Is f@@6 (Tclass._System.___hFunc1 t0@@20 t1@@11)))) (forall ((o@@45 T@U) (fld@@0 T@U) ) (! (let ((a@@83 (FieldTypeInv0 (type fld@@0))))
 (=> (and (and (= (type o@@45) refType) (= (type fld@@0) (FieldType a@@83))) (and (not (= o@@45 null)) (U_2_bool (MapType0Select (Reads1 t0@@20 t1@@11 h1@@1 f@@6 bx0@@3) ($Box o@@45))))) (= (MapType1Select (MapType0Select h0@@1 o@@45) fld@@0) (MapType1Select (MapType0Select h1@@1 o@@45) fld@@0))))
 :qid |unknown.0:0|
 :skolemid |726|
 :no-pattern (type o@@45)
 :no-pattern (type fld@@0)
 :no-pattern (U_2_int o@@45)
 :no-pattern (U_2_bool o@@45)
 :no-pattern (U_2_int fld@@0)
 :no-pattern (U_2_bool fld@@0)
)))) (= (Reads1 t0@@20 t1@@11 h0@@1 f@@6 bx0@@3) (Reads1 t0@@20 t1@@11 h1@@1 f@@6 bx0@@3)))
 :qid |unknown.0:0|
 :skolemid |727|
 :pattern ( ($HeapSucc h0@@1 h1@@1) (Reads1 t0@@20 t1@@11 h1@@1 f@@6 bx0@@3))
)))
(assert (forall ((t0@@21 T@U) (t1@@12 T@U) (h0@@2 T@U) (h1@@2 T@U) (f@@7 T@U) (bx0@@4 T@U) ) (!  (=> (and (and (and (and (and (and (= (type t0@@21) TyType) (= (type t1@@12) TyType)) (= (type h0@@2) (MapType0Type refType MapType1Type))) (= (type h1@@2) (MapType0Type refType MapType1Type))) (= (type f@@7) HandleTypeType)) (= (type bx0@@4) BoxType)) (and (and (and ($HeapSucc h0@@2 h1@@2) (and ($IsGoodHeap h0@@2) ($IsGoodHeap h1@@2))) (and ($IsBox bx0@@4 t0@@21) ($Is f@@7 (Tclass._System.___hFunc1 t0@@21 t1@@12)))) (forall ((o@@46 T@U) (fld@@1 T@U) ) (! (let ((a@@84 (FieldTypeInv0 (type fld@@1))))
 (=> (and (and (= (type o@@46) refType) (= (type fld@@1) (FieldType a@@84))) (and (not (= o@@46 null)) (U_2_bool (MapType0Select (Reads1 t0@@21 t1@@12 h0@@2 f@@7 bx0@@4) ($Box o@@46))))) (= (MapType1Select (MapType0Select h0@@2 o@@46) fld@@1) (MapType1Select (MapType0Select h1@@2 o@@46) fld@@1))))
 :qid |unknown.0:0|
 :skolemid |728|
 :no-pattern (type o@@46)
 :no-pattern (type fld@@1)
 :no-pattern (U_2_int o@@46)
 :no-pattern (U_2_bool o@@46)
 :no-pattern (U_2_int fld@@1)
 :no-pattern (U_2_bool fld@@1)
)))) (= (Requires1 t0@@21 t1@@12 h0@@2 f@@7 bx0@@4) (Requires1 t0@@21 t1@@12 h1@@2 f@@7 bx0@@4)))
 :qid |unknown.0:0|
 :skolemid |729|
 :pattern ( ($HeapSucc h0@@2 h1@@2) (Requires1 t0@@21 t1@@12 h1@@2 f@@7 bx0@@4))
)))
(assert (forall ((t0@@22 T@U) (t1@@13 T@U) (h0@@3 T@U) (h1@@3 T@U) (f@@8 T@U) (bx0@@5 T@U) ) (!  (=> (and (and (and (and (and (and (= (type t0@@22) TyType) (= (type t1@@13) TyType)) (= (type h0@@3) (MapType0Type refType MapType1Type))) (= (type h1@@3) (MapType0Type refType MapType1Type))) (= (type f@@8) HandleTypeType)) (= (type bx0@@5) BoxType)) (and (and (and ($HeapSucc h0@@3 h1@@3) (and ($IsGoodHeap h0@@3) ($IsGoodHeap h1@@3))) (and ($IsBox bx0@@5 t0@@22) ($Is f@@8 (Tclass._System.___hFunc1 t0@@22 t1@@13)))) (forall ((o@@47 T@U) (fld@@2 T@U) ) (! (let ((a@@85 (FieldTypeInv0 (type fld@@2))))
 (=> (and (and (= (type o@@47) refType) (= (type fld@@2) (FieldType a@@85))) (and (not (= o@@47 null)) (U_2_bool (MapType0Select (Reads1 t0@@22 t1@@13 h1@@3 f@@8 bx0@@5) ($Box o@@47))))) (= (MapType1Select (MapType0Select h0@@3 o@@47) fld@@2) (MapType1Select (MapType0Select h1@@3 o@@47) fld@@2))))
 :qid |unknown.0:0|
 :skolemid |730|
 :no-pattern (type o@@47)
 :no-pattern (type fld@@2)
 :no-pattern (U_2_int o@@47)
 :no-pattern (U_2_bool o@@47)
 :no-pattern (U_2_int fld@@2)
 :no-pattern (U_2_bool fld@@2)
)))) (= (Requires1 t0@@22 t1@@13 h0@@3 f@@8 bx0@@5) (Requires1 t0@@22 t1@@13 h1@@3 f@@8 bx0@@5)))
 :qid |unknown.0:0|
 :skolemid |731|
 :pattern ( ($HeapSucc h0@@3 h1@@3) (Requires1 t0@@22 t1@@13 h1@@3 f@@8 bx0@@5))
)))
(assert (forall ((t0@@23 T@U) (t1@@14 T@U) (h0@@4 T@U) (h1@@4 T@U) (f@@9 T@U) (bx0@@6 T@U) ) (!  (=> (and (and (and (and (and (and (= (type t0@@23) TyType) (= (type t1@@14) TyType)) (= (type h0@@4) (MapType0Type refType MapType1Type))) (= (type h1@@4) (MapType0Type refType MapType1Type))) (= (type f@@9) HandleTypeType)) (= (type bx0@@6) BoxType)) (and (and (and ($HeapSucc h0@@4 h1@@4) (and ($IsGoodHeap h0@@4) ($IsGoodHeap h1@@4))) (and ($IsBox bx0@@6 t0@@23) ($Is f@@9 (Tclass._System.___hFunc1 t0@@23 t1@@14)))) (forall ((o@@48 T@U) (fld@@3 T@U) ) (! (let ((a@@86 (FieldTypeInv0 (type fld@@3))))
 (=> (and (and (= (type o@@48) refType) (= (type fld@@3) (FieldType a@@86))) (and (not (= o@@48 null)) (U_2_bool (MapType0Select (Reads1 t0@@23 t1@@14 h0@@4 f@@9 bx0@@6) ($Box o@@48))))) (= (MapType1Select (MapType0Select h0@@4 o@@48) fld@@3) (MapType1Select (MapType0Select h1@@4 o@@48) fld@@3))))
 :qid |unknown.0:0|
 :skolemid |732|
 :no-pattern (type o@@48)
 :no-pattern (type fld@@3)
 :no-pattern (U_2_int o@@48)
 :no-pattern (U_2_bool o@@48)
 :no-pattern (U_2_int fld@@3)
 :no-pattern (U_2_bool fld@@3)
)))) (= (Apply1 t0@@23 t1@@14 h0@@4 f@@9 bx0@@6) (Apply1 t0@@23 t1@@14 h1@@4 f@@9 bx0@@6)))
 :qid |unknown.0:0|
 :skolemid |733|
 :pattern ( ($HeapSucc h0@@4 h1@@4) (Apply1 t0@@23 t1@@14 h1@@4 f@@9 bx0@@6))
)))
(assert (forall ((t0@@24 T@U) (t1@@15 T@U) (h0@@5 T@U) (h1@@5 T@U) (f@@10 T@U) (bx0@@7 T@U) ) (!  (=> (and (and (and (and (and (and (= (type t0@@24) TyType) (= (type t1@@15) TyType)) (= (type h0@@5) (MapType0Type refType MapType1Type))) (= (type h1@@5) (MapType0Type refType MapType1Type))) (= (type f@@10) HandleTypeType)) (= (type bx0@@7) BoxType)) (and (and (and ($HeapSucc h0@@5 h1@@5) (and ($IsGoodHeap h0@@5) ($IsGoodHeap h1@@5))) (and ($IsBox bx0@@7 t0@@24) ($Is f@@10 (Tclass._System.___hFunc1 t0@@24 t1@@15)))) (forall ((o@@49 T@U) (fld@@4 T@U) ) (! (let ((a@@87 (FieldTypeInv0 (type fld@@4))))
 (=> (and (and (= (type o@@49) refType) (= (type fld@@4) (FieldType a@@87))) (and (not (= o@@49 null)) (U_2_bool (MapType0Select (Reads1 t0@@24 t1@@15 h1@@5 f@@10 bx0@@7) ($Box o@@49))))) (= (MapType1Select (MapType0Select h0@@5 o@@49) fld@@4) (MapType1Select (MapType0Select h1@@5 o@@49) fld@@4))))
 :qid |unknown.0:0|
 :skolemid |734|
 :no-pattern (type o@@49)
 :no-pattern (type fld@@4)
 :no-pattern (U_2_int o@@49)
 :no-pattern (U_2_bool o@@49)
 :no-pattern (U_2_int fld@@4)
 :no-pattern (U_2_bool fld@@4)
)))) (= (Apply1 t0@@24 t1@@15 h0@@5 f@@10 bx0@@7) (Apply1 t0@@24 t1@@15 h1@@5 f@@10 bx0@@7)))
 :qid |unknown.0:0|
 :skolemid |735|
 :pattern ( ($HeapSucc h0@@5 h1@@5) (Apply1 t0@@24 t1@@15 h1@@5 f@@10 bx0@@7))
)))
(assert (forall ((t0@@25 T@U) (t1@@16 T@U) (heap@@4 T@U) (f@@11 T@U) (bx0@@8 T@U) ) (!  (=> (and (and (and (and (and (= (type t0@@25) TyType) (= (type t1@@16) TyType)) (= (type heap@@4) (MapType0Type refType MapType1Type))) (= (type f@@11) HandleTypeType)) (= (type bx0@@8) BoxType)) (and ($IsGoodHeap heap@@4) (and ($IsBox bx0@@8 t0@@25) ($Is f@@11 (Tclass._System.___hFunc1 t0@@25 t1@@16))))) (= (|Set#Equal| (Reads1 t0@@25 t1@@16 $OneHeap f@@11 bx0@@8) (|Set#Empty| BoxType)) (|Set#Equal| (Reads1 t0@@25 t1@@16 heap@@4 f@@11 bx0@@8) (|Set#Empty| BoxType))))
 :qid |unknown.0:0|
 :skolemid |736|
 :pattern ( (Reads1 t0@@25 t1@@16 $OneHeap f@@11 bx0@@8) ($IsGoodHeap heap@@4))
 :pattern ( (Reads1 t0@@25 t1@@16 heap@@4 f@@11 bx0@@8))
)))
(assert (forall ((t0@@26 T@U) (t1@@17 T@U) (heap@@5 T@U) (f@@12 T@U) (bx0@@9 T@U) ) (!  (=> (and (and (and (and (and (= (type t0@@26) TyType) (= (type t1@@17) TyType)) (= (type heap@@5) (MapType0Type refType MapType1Type))) (= (type f@@12) HandleTypeType)) (= (type bx0@@9) BoxType)) (and (and ($IsGoodHeap heap@@5) (and ($IsBox bx0@@9 t0@@26) ($Is f@@12 (Tclass._System.___hFunc1 t0@@26 t1@@17)))) (|Set#Equal| (Reads1 t0@@26 t1@@17 $OneHeap f@@12 bx0@@9) (|Set#Empty| BoxType)))) (= (Requires1 t0@@26 t1@@17 $OneHeap f@@12 bx0@@9) (Requires1 t0@@26 t1@@17 heap@@5 f@@12 bx0@@9)))
 :qid |unknown.0:0|
 :skolemid |737|
 :pattern ( (Requires1 t0@@26 t1@@17 $OneHeap f@@12 bx0@@9) ($IsGoodHeap heap@@5))
 :pattern ( (Requires1 t0@@26 t1@@17 heap@@5 f@@12 bx0@@9))
)))
(assert (forall ((f@@13 T@U) (t0@@27 T@U) (t1@@18 T@U) ) (!  (=> (and (and (= (type f@@13) HandleTypeType) (= (type t0@@27) TyType)) (= (type t1@@18) TyType)) (= ($Is f@@13 (Tclass._System.___hFunc1 t0@@27 t1@@18)) (forall ((h@@24 T@U) (bx0@@10 T@U) ) (!  (=> (and (= (type h@@24) (MapType0Type refType MapType1Type)) (= (type bx0@@10) BoxType)) (=> (and (and ($IsGoodHeap h@@24) ($IsBox bx0@@10 t0@@27)) (Requires1 t0@@27 t1@@18 h@@24 f@@13 bx0@@10)) ($IsBox (Apply1 t0@@27 t1@@18 h@@24 f@@13 bx0@@10) t1@@18)))
 :qid |DafnyPreludebpl.545:12|
 :skolemid |738|
 :pattern ( (Apply1 t0@@27 t1@@18 h@@24 f@@13 bx0@@10))
))))
 :qid |unknown.0:0|
 :skolemid |739|
 :pattern ( ($Is f@@13 (Tclass._System.___hFunc1 t0@@27 t1@@18)))
)))
(assert (forall ((f@@14 T@U) (t0@@28 T@U) (t1@@19 T@U) (u0 T@U) (u1 T@U) ) (!  (=> (and (and (and (and (and (= (type f@@14) HandleTypeType) (= (type t0@@28) TyType)) (= (type t1@@19) TyType)) (= (type u0) TyType)) (= (type u1) TyType)) (and (and ($Is f@@14 (Tclass._System.___hFunc1 t0@@28 t1@@19)) (forall ((bx@@33 T@U) ) (!  (=> (and (= (type bx@@33) BoxType) ($IsBox bx@@33 u0)) ($IsBox bx@@33 t0@@28))
 :qid |unknown.0:0|
 :skolemid |740|
 :pattern ( ($IsBox bx@@33 u0))
 :pattern ( ($IsBox bx@@33 t0@@28))
))) (forall ((bx@@34 T@U) ) (!  (=> (and (= (type bx@@34) BoxType) ($IsBox bx@@34 t1@@19)) ($IsBox bx@@34 u1))
 :qid |unknown.0:0|
 :skolemid |741|
 :pattern ( ($IsBox bx@@34 t1@@19))
 :pattern ( ($IsBox bx@@34 u1))
)))) ($Is f@@14 (Tclass._System.___hFunc1 u0 u1)))
 :qid |unknown.0:0|
 :skolemid |742|
 :pattern ( ($Is f@@14 (Tclass._System.___hFunc1 t0@@28 t1@@19)) ($Is f@@14 (Tclass._System.___hFunc1 u0 u1)))
)))
(assert (forall ((f@@15 T@U) (t0@@29 T@U) (t1@@20 T@U) (h@@25 T@U) ) (!  (=> (and (and (and (and (= (type f@@15) HandleTypeType) (= (type t0@@29) TyType)) (= (type t1@@20) TyType)) (= (type h@@25) (MapType0Type refType MapType1Type))) ($IsGoodHeap h@@25)) (= ($IsAlloc f@@15 (Tclass._System.___hFunc1 t0@@29 t1@@20) h@@25) (forall ((bx0@@11 T@U) ) (!  (=> (= (type bx0@@11) BoxType) (=> (and (and ($IsBox bx0@@11 t0@@29) ($IsAllocBox bx0@@11 t0@@29 h@@25)) (Requires1 t0@@29 t1@@20 h@@25 f@@15 bx0@@11)) (forall ((r@@9 T@U) ) (!  (=> (= (type r@@9) refType) (=> (and (not (= r@@9 null)) (U_2_bool (MapType0Select (Reads1 t0@@29 t1@@20 h@@25 f@@15 bx0@@11) ($Box r@@9)))) (U_2_bool (MapType1Select (MapType0Select h@@25 r@@9) alloc))))
 :qid |unknown.0:0|
 :skolemid |743|
 :pattern ( (MapType0Select (Reads1 t0@@29 t1@@20 h@@25 f@@15 bx0@@11) ($Box r@@9)))
))))
 :qid |unknown.0:0|
 :skolemid |744|
 :pattern ( (Apply1 t0@@29 t1@@20 h@@25 f@@15 bx0@@11))
 :pattern ( (Reads1 t0@@29 t1@@20 h@@25 f@@15 bx0@@11))
))))
 :qid |unknown.0:0|
 :skolemid |745|
 :pattern ( ($IsAlloc f@@15 (Tclass._System.___hFunc1 t0@@29 t1@@20) h@@25))
)))
(assert (forall ((f@@16 T@U) (t0@@30 T@U) (t1@@21 T@U) (h@@26 T@U) ) (!  (=> (and (and (and (and (= (type f@@16) HandleTypeType) (= (type t0@@30) TyType)) (= (type t1@@21) TyType)) (= (type h@@26) (MapType0Type refType MapType1Type))) (and ($IsGoodHeap h@@26) ($IsAlloc f@@16 (Tclass._System.___hFunc1 t0@@30 t1@@21) h@@26))) (forall ((bx0@@12 T@U) ) (!  (=> (= (type bx0@@12) BoxType) (=> (and ($IsAllocBox bx0@@12 t0@@30 h@@26) (Requires1 t0@@30 t1@@21 h@@26 f@@16 bx0@@12)) ($IsAllocBox (Apply1 t0@@30 t1@@21 h@@26 f@@16 bx0@@12) t1@@21 h@@26)))
 :qid |unknown.0:0|
 :skolemid |746|
 :pattern ( (Apply1 t0@@30 t1@@21 h@@26 f@@16 bx0@@12))
)))
 :qid |unknown.0:0|
 :skolemid |747|
 :pattern ( ($IsAlloc f@@16 (Tclass._System.___hFunc1 t0@@30 t1@@21) h@@26))
)))
(assert (forall ((arg0@@130 T@U) (arg1@@62 T@U) ) (! (= (type (Tclass._System.___hPartialFunc1 arg0@@130 arg1@@62)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc1|
 :pattern ( (Tclass._System.___hPartialFunc1 arg0@@130 arg1@@62))
)))
(assert (forall ((|#$T0@@3| T@U) (|#$R@@3| T@U) ) (!  (=> (and (= (type |#$T0@@3|) TyType) (= (type |#$R@@3|) TyType)) (and (= (Tag (Tclass._System.___hPartialFunc1 |#$T0@@3| |#$R@@3|)) Tagclass._System.___hPartialFunc1) (= (TagFamily (Tclass._System.___hPartialFunc1 |#$T0@@3| |#$R@@3|)) |tytagFamily$_#PartialFunc1|)))
 :qid |unknown.0:0|
 :skolemid |748|
 :pattern ( (Tclass._System.___hPartialFunc1 |#$T0@@3| |#$R@@3|))
)))
(assert (forall ((arg0@@131 T@U) ) (! (= (type (Tclass._System.___hPartialFunc1_0 arg0@@131)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc1_0|
 :pattern ( (Tclass._System.___hPartialFunc1_0 arg0@@131))
)))
(assert (forall ((|#$T0@@4| T@U) (|#$R@@4| T@U) ) (!  (=> (and (= (type |#$T0@@4|) TyType) (= (type |#$R@@4|) TyType)) (= (Tclass._System.___hPartialFunc1_0 (Tclass._System.___hPartialFunc1 |#$T0@@4| |#$R@@4|)) |#$T0@@4|))
 :qid |unknown.0:0|
 :skolemid |749|
 :pattern ( (Tclass._System.___hPartialFunc1 |#$T0@@4| |#$R@@4|))
)))
(assert (forall ((arg0@@132 T@U) ) (! (= (type (Tclass._System.___hPartialFunc1_1 arg0@@132)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc1_1|
 :pattern ( (Tclass._System.___hPartialFunc1_1 arg0@@132))
)))
(assert (forall ((|#$T0@@5| T@U) (|#$R@@5| T@U) ) (!  (=> (and (= (type |#$T0@@5|) TyType) (= (type |#$R@@5|) TyType)) (= (Tclass._System.___hPartialFunc1_1 (Tclass._System.___hPartialFunc1 |#$T0@@5| |#$R@@5|)) |#$R@@5|))
 :qid |unknown.0:0|
 :skolemid |750|
 :pattern ( (Tclass._System.___hPartialFunc1 |#$T0@@5| |#$R@@5|))
)))
(assert (forall ((|#$T0@@6| T@U) (|#$R@@6| T@U) (bx@@35 T@U) ) (!  (=> (and (and (and (= (type |#$T0@@6|) TyType) (= (type |#$R@@6|) TyType)) (= (type bx@@35) BoxType)) ($IsBox bx@@35 (Tclass._System.___hPartialFunc1 |#$T0@@6| |#$R@@6|))) (and (= ($Box ($Unbox HandleTypeType bx@@35)) bx@@35) ($Is ($Unbox HandleTypeType bx@@35) (Tclass._System.___hPartialFunc1 |#$T0@@6| |#$R@@6|))))
 :qid |unknown.0:0|
 :skolemid |751|
 :pattern ( ($IsBox bx@@35 (Tclass._System.___hPartialFunc1 |#$T0@@6| |#$R@@6|)))
)))
(assert (forall ((|#$T0@@7| T@U) (|#$R@@7| T@U) (|f#0| T@U) ) (!  (=> (and (and (= (type |#$T0@@7|) TyType) (= (type |#$R@@7|) TyType)) (= (type |f#0|) HandleTypeType)) (= ($Is |f#0| (Tclass._System.___hPartialFunc1 |#$T0@@7| |#$R@@7|))  (and ($Is |f#0| (Tclass._System.___hFunc1 |#$T0@@7| |#$R@@7|)) (forall ((|x0#0| T@U) ) (!  (=> (and (= (type |x0#0|) BoxType) ($IsBox |x0#0| |#$T0@@7|)) (|Set#Equal| (Reads1 |#$T0@@7| |#$R@@7| $OneHeap |f#0| |x0#0|) (|Set#Empty| BoxType)))
 :qid |unknown.0:0|
 :skolemid |752|
 :no-pattern (type |x0#0|)
 :no-pattern (U_2_int |x0#0|)
 :no-pattern (U_2_bool |x0#0|)
)))))
 :qid |unknown.0:0|
 :skolemid |753|
 :pattern ( ($Is |f#0| (Tclass._System.___hPartialFunc1 |#$T0@@7| |#$R@@7|)))
)))
(assert (forall ((|#$T0@@8| T@U) (|#$R@@8| T@U) (|f#0@@0| T@U) ($h@@7 T@U) ) (!  (=> (and (and (and (= (type |#$T0@@8|) TyType) (= (type |#$R@@8|) TyType)) (= (type |f#0@@0|) HandleTypeType)) (= (type $h@@7) (MapType0Type refType MapType1Type))) (= ($IsAlloc |f#0@@0| (Tclass._System.___hPartialFunc1 |#$T0@@8| |#$R@@8|) $h@@7) ($IsAlloc |f#0@@0| (Tclass._System.___hFunc1 |#$T0@@8| |#$R@@8|) $h@@7)))
 :qid |unknown.0:0|
 :skolemid |754|
 :pattern ( ($IsAlloc |f#0@@0| (Tclass._System.___hPartialFunc1 |#$T0@@8| |#$R@@8|) $h@@7))
)))
(assert (forall ((arg0@@133 T@U) (arg1@@63 T@U) ) (! (= (type (Tclass._System.___hTotalFunc1 arg0@@133 arg1@@63)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc1|
 :pattern ( (Tclass._System.___hTotalFunc1 arg0@@133 arg1@@63))
)))
(assert (forall ((|#$T0@@9| T@U) (|#$R@@9| T@U) ) (!  (=> (and (= (type |#$T0@@9|) TyType) (= (type |#$R@@9|) TyType)) (and (= (Tag (Tclass._System.___hTotalFunc1 |#$T0@@9| |#$R@@9|)) Tagclass._System.___hTotalFunc1) (= (TagFamily (Tclass._System.___hTotalFunc1 |#$T0@@9| |#$R@@9|)) |tytagFamily$_#TotalFunc1|)))
 :qid |unknown.0:0|
 :skolemid |755|
 :pattern ( (Tclass._System.___hTotalFunc1 |#$T0@@9| |#$R@@9|))
)))
(assert (forall ((arg0@@134 T@U) ) (! (= (type (Tclass._System.___hTotalFunc1_0 arg0@@134)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc1_0|
 :pattern ( (Tclass._System.___hTotalFunc1_0 arg0@@134))
)))
(assert (forall ((|#$T0@@10| T@U) (|#$R@@10| T@U) ) (!  (=> (and (= (type |#$T0@@10|) TyType) (= (type |#$R@@10|) TyType)) (= (Tclass._System.___hTotalFunc1_0 (Tclass._System.___hTotalFunc1 |#$T0@@10| |#$R@@10|)) |#$T0@@10|))
 :qid |unknown.0:0|
 :skolemid |756|
 :pattern ( (Tclass._System.___hTotalFunc1 |#$T0@@10| |#$R@@10|))
)))
(assert (forall ((arg0@@135 T@U) ) (! (= (type (Tclass._System.___hTotalFunc1_1 arg0@@135)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc1_1|
 :pattern ( (Tclass._System.___hTotalFunc1_1 arg0@@135))
)))
(assert (forall ((|#$T0@@11| T@U) (|#$R@@11| T@U) ) (!  (=> (and (= (type |#$T0@@11|) TyType) (= (type |#$R@@11|) TyType)) (= (Tclass._System.___hTotalFunc1_1 (Tclass._System.___hTotalFunc1 |#$T0@@11| |#$R@@11|)) |#$R@@11|))
 :qid |unknown.0:0|
 :skolemid |757|
 :pattern ( (Tclass._System.___hTotalFunc1 |#$T0@@11| |#$R@@11|))
)))
(assert (forall ((|#$T0@@12| T@U) (|#$R@@12| T@U) (bx@@36 T@U) ) (!  (=> (and (and (and (= (type |#$T0@@12|) TyType) (= (type |#$R@@12|) TyType)) (= (type bx@@36) BoxType)) ($IsBox bx@@36 (Tclass._System.___hTotalFunc1 |#$T0@@12| |#$R@@12|))) (and (= ($Box ($Unbox HandleTypeType bx@@36)) bx@@36) ($Is ($Unbox HandleTypeType bx@@36) (Tclass._System.___hTotalFunc1 |#$T0@@12| |#$R@@12|))))
 :qid |unknown.0:0|
 :skolemid |758|
 :pattern ( ($IsBox bx@@36 (Tclass._System.___hTotalFunc1 |#$T0@@12| |#$R@@12|)))
)))
(assert (forall ((|#$T0@@13| T@U) (|#$R@@13| T@U) (|f#0@@1| T@U) ) (!  (=> (and (and (= (type |#$T0@@13|) TyType) (= (type |#$R@@13|) TyType)) (= (type |f#0@@1|) HandleTypeType)) (= ($Is |f#0@@1| (Tclass._System.___hTotalFunc1 |#$T0@@13| |#$R@@13|))  (and ($Is |f#0@@1| (Tclass._System.___hPartialFunc1 |#$T0@@13| |#$R@@13|)) (forall ((|x0#0@@0| T@U) ) (!  (=> (and (= (type |x0#0@@0|) BoxType) ($IsBox |x0#0@@0| |#$T0@@13|)) (Requires1 |#$T0@@13| |#$R@@13| $OneHeap |f#0@@1| |x0#0@@0|))
 :qid |unknown.0:0|
 :skolemid |759|
 :no-pattern (type |x0#0@@0|)
 :no-pattern (U_2_int |x0#0@@0|)
 :no-pattern (U_2_bool |x0#0@@0|)
)))))
 :qid |unknown.0:0|
 :skolemid |760|
 :pattern ( ($Is |f#0@@1| (Tclass._System.___hTotalFunc1 |#$T0@@13| |#$R@@13|)))
)))
(assert (forall ((|#$T0@@14| T@U) (|#$R@@14| T@U) (|f#0@@2| T@U) ($h@@8 T@U) ) (!  (=> (and (and (and (= (type |#$T0@@14|) TyType) (= (type |#$R@@14|) TyType)) (= (type |f#0@@2|) HandleTypeType)) (= (type $h@@8) (MapType0Type refType MapType1Type))) (= ($IsAlloc |f#0@@2| (Tclass._System.___hTotalFunc1 |#$T0@@14| |#$R@@14|) $h@@8) ($IsAlloc |f#0@@2| (Tclass._System.___hPartialFunc1 |#$T0@@14| |#$R@@14|) $h@@8)))
 :qid |unknown.0:0|
 :skolemid |761|
 :pattern ( ($IsAlloc |f#0@@2| (Tclass._System.___hTotalFunc1 |#$T0@@14| |#$R@@14|) $h@@8))
)))
(assert (forall ((arg0@@136 T@U) ) (! (= (type (Tclass._System.___hFunc0 arg0@@136)) TyType)
 :qid |funType:Tclass._System.___hFunc0|
 :pattern ( (Tclass._System.___hFunc0 arg0@@136))
)))
(assert (forall ((|#$R@@15| T@U) ) (!  (=> (= (type |#$R@@15|) TyType) (and (= (Tag (Tclass._System.___hFunc0 |#$R@@15|)) Tagclass._System.___hFunc0) (= (TagFamily (Tclass._System.___hFunc0 |#$R@@15|)) |tytagFamily$_#Func0|)))
 :qid |unknown.0:0|
 :skolemid |762|
 :pattern ( (Tclass._System.___hFunc0 |#$R@@15|))
)))
(assert (forall ((arg0@@137 T@U) ) (! (= (type (Tclass._System.___hFunc0_0 arg0@@137)) TyType)
 :qid |funType:Tclass._System.___hFunc0_0|
 :pattern ( (Tclass._System.___hFunc0_0 arg0@@137))
)))
(assert (forall ((|#$R@@16| T@U) ) (!  (=> (= (type |#$R@@16|) TyType) (= (Tclass._System.___hFunc0_0 (Tclass._System.___hFunc0 |#$R@@16|)) |#$R@@16|))
 :qid |unknown.0:0|
 :skolemid |763|
 :pattern ( (Tclass._System.___hFunc0 |#$R@@16|))
)))
(assert (forall ((|#$R@@17| T@U) (bx@@37 T@U) ) (!  (=> (and (and (= (type |#$R@@17|) TyType) (= (type bx@@37) BoxType)) ($IsBox bx@@37 (Tclass._System.___hFunc0 |#$R@@17|))) (and (= ($Box ($Unbox HandleTypeType bx@@37)) bx@@37) ($Is ($Unbox HandleTypeType bx@@37) (Tclass._System.___hFunc0 |#$R@@17|))))
 :qid |unknown.0:0|
 :skolemid |764|
 :pattern ( ($IsBox bx@@37 (Tclass._System.___hFunc0 |#$R@@17|)))
)))
(assert  (and (forall ((arg0@@138 T@U) (arg1@@64 T@U) (arg2@@16 T@U) ) (! (= (type (Apply0 arg0@@138 arg1@@64 arg2@@16)) BoxType)
 :qid |funType:Apply0|
 :pattern ( (Apply0 arg0@@138 arg1@@64 arg2@@16))
)) (forall ((arg0@@139 T@U) (arg1@@65 T@U) (arg2@@17 T@U) ) (! (= (type (Handle0 arg0@@139 arg1@@65 arg2@@17)) HandleTypeType)
 :qid |funType:Handle0|
 :pattern ( (Handle0 arg0@@139 arg1@@65 arg2@@17))
))))
(assert (forall ((t0@@31 T@U) (heap@@6 T@U) (h@@27 T@U) (r@@10 T@U) (rd@@2 T@U) ) (!  (=> (and (and (and (and (= (type t0@@31) TyType) (= (type heap@@6) (MapType0Type refType MapType1Type))) (= (type h@@27) (MapType0Type (MapType0Type refType MapType1Type) BoxType))) (= (type r@@10) (MapType0Type (MapType0Type refType MapType1Type) boolType))) (= (type rd@@2) (MapType0Type (MapType0Type refType MapType1Type) (MapType0Type BoxType boolType)))) (= (Apply0 t0@@31 heap@@6 (Handle0 h@@27 r@@10 rd@@2)) (MapType0Select h@@27 heap@@6)))
 :qid |unknown.0:0|
 :skolemid |765|
 :pattern ( (Apply0 t0@@31 heap@@6 (Handle0 h@@27 r@@10 rd@@2)))
)))
(assert (forall ((t0@@32 T@U) (heap@@7 T@U) (h@@28 T@U) (r@@11 T@U) (rd@@3 T@U) ) (!  (=> (and (and (and (and (and (= (type t0@@32) TyType) (= (type heap@@7) (MapType0Type refType MapType1Type))) (= (type h@@28) (MapType0Type (MapType0Type refType MapType1Type) BoxType))) (= (type r@@11) (MapType0Type (MapType0Type refType MapType1Type) boolType))) (= (type rd@@3) (MapType0Type (MapType0Type refType MapType1Type) (MapType0Type BoxType boolType)))) (U_2_bool (MapType0Select r@@11 heap@@7))) (Requires0 t0@@32 heap@@7 (Handle0 h@@28 r@@11 rd@@3)))
 :qid |unknown.0:0|
 :skolemid |766|
 :pattern ( (Requires0 t0@@32 heap@@7 (Handle0 h@@28 r@@11 rd@@3)))
)))
(assert (forall ((arg0@@140 T@U) (arg1@@66 T@U) (arg2@@18 T@U) ) (! (= (type (Reads0 arg0@@140 arg1@@66 arg2@@18)) (MapType0Type BoxType boolType))
 :qid |funType:Reads0|
 :pattern ( (Reads0 arg0@@140 arg1@@66 arg2@@18))
)))
(assert (forall ((t0@@33 T@U) (heap@@8 T@U) (h@@29 T@U) (r@@12 T@U) (rd@@4 T@U) (bx@@38 T@U) ) (!  (=> (and (and (and (and (and (= (type t0@@33) TyType) (= (type heap@@8) (MapType0Type refType MapType1Type))) (= (type h@@29) (MapType0Type (MapType0Type refType MapType1Type) BoxType))) (= (type r@@12) (MapType0Type (MapType0Type refType MapType1Type) boolType))) (= (type rd@@4) (MapType0Type (MapType0Type refType MapType1Type) (MapType0Type BoxType boolType)))) (= (type bx@@38) BoxType)) (= (U_2_bool (MapType0Select (Reads0 t0@@33 heap@@8 (Handle0 h@@29 r@@12 rd@@4)) bx@@38)) (U_2_bool (MapType0Select (MapType0Select rd@@4 heap@@8) bx@@38))))
 :qid |unknown.0:0|
 :skolemid |767|
 :pattern ( (MapType0Select (Reads0 t0@@33 heap@@8 (Handle0 h@@29 r@@12 rd@@4)) bx@@38))
)))
(assert (forall ((t0@@34 T@U) (h0@@6 T@U) (h1@@6 T@U) (f@@17 T@U) ) (!  (=> (and (and (and (and (= (type t0@@34) TyType) (= (type h0@@6) (MapType0Type refType MapType1Type))) (= (type h1@@6) (MapType0Type refType MapType1Type))) (= (type f@@17) HandleTypeType)) (and (and (and ($HeapSucc h0@@6 h1@@6) (and ($IsGoodHeap h0@@6) ($IsGoodHeap h1@@6))) ($Is f@@17 (Tclass._System.___hFunc0 t0@@34))) (forall ((o@@50 T@U) (fld@@5 T@U) ) (! (let ((a@@88 (FieldTypeInv0 (type fld@@5))))
 (=> (and (and (= (type o@@50) refType) (= (type fld@@5) (FieldType a@@88))) (and (not (= o@@50 null)) (U_2_bool (MapType0Select (Reads0 t0@@34 h0@@6 f@@17) ($Box o@@50))))) (= (MapType1Select (MapType0Select h0@@6 o@@50) fld@@5) (MapType1Select (MapType0Select h1@@6 o@@50) fld@@5))))
 :qid |unknown.0:0|
 :skolemid |768|
 :no-pattern (type o@@50)
 :no-pattern (type fld@@5)
 :no-pattern (U_2_int o@@50)
 :no-pattern (U_2_bool o@@50)
 :no-pattern (U_2_int fld@@5)
 :no-pattern (U_2_bool fld@@5)
)))) (= (Reads0 t0@@34 h0@@6 f@@17) (Reads0 t0@@34 h1@@6 f@@17)))
 :qid |unknown.0:0|
 :skolemid |769|
 :pattern ( ($HeapSucc h0@@6 h1@@6) (Reads0 t0@@34 h1@@6 f@@17))
)))
(assert (forall ((t0@@35 T@U) (h0@@7 T@U) (h1@@7 T@U) (f@@18 T@U) ) (!  (=> (and (and (and (and (= (type t0@@35) TyType) (= (type h0@@7) (MapType0Type refType MapType1Type))) (= (type h1@@7) (MapType0Type refType MapType1Type))) (= (type f@@18) HandleTypeType)) (and (and (and ($HeapSucc h0@@7 h1@@7) (and ($IsGoodHeap h0@@7) ($IsGoodHeap h1@@7))) ($Is f@@18 (Tclass._System.___hFunc0 t0@@35))) (forall ((o@@51 T@U) (fld@@6 T@U) ) (! (let ((a@@89 (FieldTypeInv0 (type fld@@6))))
 (=> (and (and (= (type o@@51) refType) (= (type fld@@6) (FieldType a@@89))) (and (not (= o@@51 null)) (U_2_bool (MapType0Select (Reads0 t0@@35 h1@@7 f@@18) ($Box o@@51))))) (= (MapType1Select (MapType0Select h0@@7 o@@51) fld@@6) (MapType1Select (MapType0Select h1@@7 o@@51) fld@@6))))
 :qid |unknown.0:0|
 :skolemid |770|
 :no-pattern (type o@@51)
 :no-pattern (type fld@@6)
 :no-pattern (U_2_int o@@51)
 :no-pattern (U_2_bool o@@51)
 :no-pattern (U_2_int fld@@6)
 :no-pattern (U_2_bool fld@@6)
)))) (= (Reads0 t0@@35 h0@@7 f@@18) (Reads0 t0@@35 h1@@7 f@@18)))
 :qid |unknown.0:0|
 :skolemid |771|
 :pattern ( ($HeapSucc h0@@7 h1@@7) (Reads0 t0@@35 h1@@7 f@@18))
)))
(assert (forall ((t0@@36 T@U) (h0@@8 T@U) (h1@@8 T@U) (f@@19 T@U) ) (!  (=> (and (and (and (and (= (type t0@@36) TyType) (= (type h0@@8) (MapType0Type refType MapType1Type))) (= (type h1@@8) (MapType0Type refType MapType1Type))) (= (type f@@19) HandleTypeType)) (and (and (and ($HeapSucc h0@@8 h1@@8) (and ($IsGoodHeap h0@@8) ($IsGoodHeap h1@@8))) ($Is f@@19 (Tclass._System.___hFunc0 t0@@36))) (forall ((o@@52 T@U) (fld@@7 T@U) ) (! (let ((a@@90 (FieldTypeInv0 (type fld@@7))))
 (=> (and (and (= (type o@@52) refType) (= (type fld@@7) (FieldType a@@90))) (and (not (= o@@52 null)) (U_2_bool (MapType0Select (Reads0 t0@@36 h0@@8 f@@19) ($Box o@@52))))) (= (MapType1Select (MapType0Select h0@@8 o@@52) fld@@7) (MapType1Select (MapType0Select h1@@8 o@@52) fld@@7))))
 :qid |unknown.0:0|
 :skolemid |772|
 :no-pattern (type o@@52)
 :no-pattern (type fld@@7)
 :no-pattern (U_2_int o@@52)
 :no-pattern (U_2_bool o@@52)
 :no-pattern (U_2_int fld@@7)
 :no-pattern (U_2_bool fld@@7)
)))) (= (Requires0 t0@@36 h0@@8 f@@19) (Requires0 t0@@36 h1@@8 f@@19)))
 :qid |unknown.0:0|
 :skolemid |773|
 :pattern ( ($HeapSucc h0@@8 h1@@8) (Requires0 t0@@36 h1@@8 f@@19))
)))
(assert (forall ((t0@@37 T@U) (h0@@9 T@U) (h1@@9 T@U) (f@@20 T@U) ) (!  (=> (and (and (and (and (= (type t0@@37) TyType) (= (type h0@@9) (MapType0Type refType MapType1Type))) (= (type h1@@9) (MapType0Type refType MapType1Type))) (= (type f@@20) HandleTypeType)) (and (and (and ($HeapSucc h0@@9 h1@@9) (and ($IsGoodHeap h0@@9) ($IsGoodHeap h1@@9))) ($Is f@@20 (Tclass._System.___hFunc0 t0@@37))) (forall ((o@@53 T@U) (fld@@8 T@U) ) (! (let ((a@@91 (FieldTypeInv0 (type fld@@8))))
 (=> (and (and (= (type o@@53) refType) (= (type fld@@8) (FieldType a@@91))) (and (not (= o@@53 null)) (U_2_bool (MapType0Select (Reads0 t0@@37 h1@@9 f@@20) ($Box o@@53))))) (= (MapType1Select (MapType0Select h0@@9 o@@53) fld@@8) (MapType1Select (MapType0Select h1@@9 o@@53) fld@@8))))
 :qid |unknown.0:0|
 :skolemid |774|
 :no-pattern (type o@@53)
 :no-pattern (type fld@@8)
 :no-pattern (U_2_int o@@53)
 :no-pattern (U_2_bool o@@53)
 :no-pattern (U_2_int fld@@8)
 :no-pattern (U_2_bool fld@@8)
)))) (= (Requires0 t0@@37 h0@@9 f@@20) (Requires0 t0@@37 h1@@9 f@@20)))
 :qid |unknown.0:0|
 :skolemid |775|
 :pattern ( ($HeapSucc h0@@9 h1@@9) (Requires0 t0@@37 h1@@9 f@@20))
)))
(assert (forall ((t0@@38 T@U) (h0@@10 T@U) (h1@@10 T@U) (f@@21 T@U) ) (!  (=> (and (and (and (and (= (type t0@@38) TyType) (= (type h0@@10) (MapType0Type refType MapType1Type))) (= (type h1@@10) (MapType0Type refType MapType1Type))) (= (type f@@21) HandleTypeType)) (and (and (and ($HeapSucc h0@@10 h1@@10) (and ($IsGoodHeap h0@@10) ($IsGoodHeap h1@@10))) ($Is f@@21 (Tclass._System.___hFunc0 t0@@38))) (forall ((o@@54 T@U) (fld@@9 T@U) ) (! (let ((a@@92 (FieldTypeInv0 (type fld@@9))))
 (=> (and (and (= (type o@@54) refType) (= (type fld@@9) (FieldType a@@92))) (and (not (= o@@54 null)) (U_2_bool (MapType0Select (Reads0 t0@@38 h0@@10 f@@21) ($Box o@@54))))) (= (MapType1Select (MapType0Select h0@@10 o@@54) fld@@9) (MapType1Select (MapType0Select h1@@10 o@@54) fld@@9))))
 :qid |unknown.0:0|
 :skolemid |776|
 :no-pattern (type o@@54)
 :no-pattern (type fld@@9)
 :no-pattern (U_2_int o@@54)
 :no-pattern (U_2_bool o@@54)
 :no-pattern (U_2_int fld@@9)
 :no-pattern (U_2_bool fld@@9)
)))) (= (Apply0 t0@@38 h0@@10 f@@21) (Apply0 t0@@38 h1@@10 f@@21)))
 :qid |unknown.0:0|
 :skolemid |777|
 :pattern ( ($HeapSucc h0@@10 h1@@10) (Apply0 t0@@38 h1@@10 f@@21))
)))
(assert (forall ((t0@@39 T@U) (h0@@11 T@U) (h1@@11 T@U) (f@@22 T@U) ) (!  (=> (and (and (and (and (= (type t0@@39) TyType) (= (type h0@@11) (MapType0Type refType MapType1Type))) (= (type h1@@11) (MapType0Type refType MapType1Type))) (= (type f@@22) HandleTypeType)) (and (and (and ($HeapSucc h0@@11 h1@@11) (and ($IsGoodHeap h0@@11) ($IsGoodHeap h1@@11))) ($Is f@@22 (Tclass._System.___hFunc0 t0@@39))) (forall ((o@@55 T@U) (fld@@10 T@U) ) (! (let ((a@@93 (FieldTypeInv0 (type fld@@10))))
 (=> (and (and (= (type o@@55) refType) (= (type fld@@10) (FieldType a@@93))) (and (not (= o@@55 null)) (U_2_bool (MapType0Select (Reads0 t0@@39 h1@@11 f@@22) ($Box o@@55))))) (= (MapType1Select (MapType0Select h0@@11 o@@55) fld@@10) (MapType1Select (MapType0Select h1@@11 o@@55) fld@@10))))
 :qid |unknown.0:0|
 :skolemid |778|
 :no-pattern (type o@@55)
 :no-pattern (type fld@@10)
 :no-pattern (U_2_int o@@55)
 :no-pattern (U_2_bool o@@55)
 :no-pattern (U_2_int fld@@10)
 :no-pattern (U_2_bool fld@@10)
)))) (= (Apply0 t0@@39 h0@@11 f@@22) (Apply0 t0@@39 h1@@11 f@@22)))
 :qid |unknown.0:0|
 :skolemid |779|
 :pattern ( ($HeapSucc h0@@11 h1@@11) (Apply0 t0@@39 h1@@11 f@@22))
)))
(assert (forall ((t0@@40 T@U) (heap@@9 T@U) (f@@23 T@U) ) (!  (=> (and (and (and (= (type t0@@40) TyType) (= (type heap@@9) (MapType0Type refType MapType1Type))) (= (type f@@23) HandleTypeType)) (and ($IsGoodHeap heap@@9) ($Is f@@23 (Tclass._System.___hFunc0 t0@@40)))) (= (|Set#Equal| (Reads0 t0@@40 $OneHeap f@@23) (|Set#Empty| BoxType)) (|Set#Equal| (Reads0 t0@@40 heap@@9 f@@23) (|Set#Empty| BoxType))))
 :qid |unknown.0:0|
 :skolemid |780|
 :pattern ( (Reads0 t0@@40 $OneHeap f@@23) ($IsGoodHeap heap@@9))
 :pattern ( (Reads0 t0@@40 heap@@9 f@@23))
)))
(assert (forall ((t0@@41 T@U) (heap@@10 T@U) (f@@24 T@U) ) (!  (=> (and (and (and (= (type t0@@41) TyType) (= (type heap@@10) (MapType0Type refType MapType1Type))) (= (type f@@24) HandleTypeType)) (and (and ($IsGoodHeap heap@@10) ($Is f@@24 (Tclass._System.___hFunc0 t0@@41))) (|Set#Equal| (Reads0 t0@@41 $OneHeap f@@24) (|Set#Empty| BoxType)))) (= (Requires0 t0@@41 $OneHeap f@@24) (Requires0 t0@@41 heap@@10 f@@24)))
 :qid |unknown.0:0|
 :skolemid |781|
 :pattern ( (Requires0 t0@@41 $OneHeap f@@24) ($IsGoodHeap heap@@10))
 :pattern ( (Requires0 t0@@41 heap@@10 f@@24))
)))
(assert (forall ((f@@25 T@U) (t0@@42 T@U) ) (!  (=> (and (= (type f@@25) HandleTypeType) (= (type t0@@42) TyType)) (= ($Is f@@25 (Tclass._System.___hFunc0 t0@@42)) (forall ((h@@30 T@U) ) (!  (=> (= (type h@@30) (MapType0Type refType MapType1Type)) (=> (and ($IsGoodHeap h@@30) (Requires0 t0@@42 h@@30 f@@25)) ($IsBox (Apply0 t0@@42 h@@30 f@@25) t0@@42)))
 :qid |DafnyPreludebpl.545:12|
 :skolemid |782|
 :pattern ( (Apply0 t0@@42 h@@30 f@@25))
))))
 :qid |unknown.0:0|
 :skolemid |783|
 :pattern ( ($Is f@@25 (Tclass._System.___hFunc0 t0@@42)))
)))
(assert (forall ((f@@26 T@U) (t0@@43 T@U) (u0@@0 T@U) ) (!  (=> (and (and (and (= (type f@@26) HandleTypeType) (= (type t0@@43) TyType)) (= (type u0@@0) TyType)) (and ($Is f@@26 (Tclass._System.___hFunc0 t0@@43)) (forall ((bx@@39 T@U) ) (!  (=> (and (= (type bx@@39) BoxType) ($IsBox bx@@39 t0@@43)) ($IsBox bx@@39 u0@@0))
 :qid |unknown.0:0|
 :skolemid |784|
 :pattern ( ($IsBox bx@@39 t0@@43))
 :pattern ( ($IsBox bx@@39 u0@@0))
)))) ($Is f@@26 (Tclass._System.___hFunc0 u0@@0)))
 :qid |unknown.0:0|
 :skolemid |785|
 :pattern ( ($Is f@@26 (Tclass._System.___hFunc0 t0@@43)) ($Is f@@26 (Tclass._System.___hFunc0 u0@@0)))
)))
(assert (forall ((f@@27 T@U) (t0@@44 T@U) (h@@31 T@U) ) (!  (=> (and (and (and (= (type f@@27) HandleTypeType) (= (type t0@@44) TyType)) (= (type h@@31) (MapType0Type refType MapType1Type))) ($IsGoodHeap h@@31)) (= ($IsAlloc f@@27 (Tclass._System.___hFunc0 t0@@44) h@@31)  (=> (Requires0 t0@@44 h@@31 f@@27) (forall ((r@@13 T@U) ) (!  (=> (= (type r@@13) refType) (=> (and (not (= r@@13 null)) (U_2_bool (MapType0Select (Reads0 t0@@44 h@@31 f@@27) ($Box r@@13)))) (U_2_bool (MapType1Select (MapType0Select h@@31 r@@13) alloc))))
 :qid |unknown.0:0|
 :skolemid |786|
 :pattern ( (MapType0Select (Reads0 t0@@44 h@@31 f@@27) ($Box r@@13)))
)))))
 :qid |unknown.0:0|
 :skolemid |787|
 :pattern ( ($IsAlloc f@@27 (Tclass._System.___hFunc0 t0@@44) h@@31))
)))
(assert (forall ((f@@28 T@U) (t0@@45 T@U) (h@@32 T@U) ) (!  (=> (and (and (and (and (= (type f@@28) HandleTypeType) (= (type t0@@45) TyType)) (= (type h@@32) (MapType0Type refType MapType1Type))) (and ($IsGoodHeap h@@32) ($IsAlloc f@@28 (Tclass._System.___hFunc0 t0@@45) h@@32))) (Requires0 t0@@45 h@@32 f@@28)) ($IsAllocBox (Apply0 t0@@45 h@@32 f@@28) t0@@45 h@@32))
 :qid |unknown.0:0|
 :skolemid |788|
 :pattern ( ($IsAlloc f@@28 (Tclass._System.___hFunc0 t0@@45) h@@32))
)))
(assert (forall ((arg0@@141 T@U) ) (! (= (type (Tclass._System.___hPartialFunc0 arg0@@141)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc0|
 :pattern ( (Tclass._System.___hPartialFunc0 arg0@@141))
)))
(assert (forall ((|#$R@@18| T@U) ) (!  (=> (= (type |#$R@@18|) TyType) (and (= (Tag (Tclass._System.___hPartialFunc0 |#$R@@18|)) Tagclass._System.___hPartialFunc0) (= (TagFamily (Tclass._System.___hPartialFunc0 |#$R@@18|)) |tytagFamily$_#PartialFunc0|)))
 :qid |unknown.0:0|
 :skolemid |789|
 :pattern ( (Tclass._System.___hPartialFunc0 |#$R@@18|))
)))
(assert (forall ((arg0@@142 T@U) ) (! (= (type (Tclass._System.___hPartialFunc0_0 arg0@@142)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc0_0|
 :pattern ( (Tclass._System.___hPartialFunc0_0 arg0@@142))
)))
(assert (forall ((|#$R@@19| T@U) ) (!  (=> (= (type |#$R@@19|) TyType) (= (Tclass._System.___hPartialFunc0_0 (Tclass._System.___hPartialFunc0 |#$R@@19|)) |#$R@@19|))
 :qid |unknown.0:0|
 :skolemid |790|
 :pattern ( (Tclass._System.___hPartialFunc0 |#$R@@19|))
)))
(assert (forall ((|#$R@@20| T@U) (bx@@40 T@U) ) (!  (=> (and (and (= (type |#$R@@20|) TyType) (= (type bx@@40) BoxType)) ($IsBox bx@@40 (Tclass._System.___hPartialFunc0 |#$R@@20|))) (and (= ($Box ($Unbox HandleTypeType bx@@40)) bx@@40) ($Is ($Unbox HandleTypeType bx@@40) (Tclass._System.___hPartialFunc0 |#$R@@20|))))
 :qid |unknown.0:0|
 :skolemid |791|
 :pattern ( ($IsBox bx@@40 (Tclass._System.___hPartialFunc0 |#$R@@20|)))
)))
(assert (forall ((|#$R@@21| T@U) (|f#0@@3| T@U) ) (!  (=> (and (= (type |#$R@@21|) TyType) (= (type |f#0@@3|) HandleTypeType)) (= ($Is |f#0@@3| (Tclass._System.___hPartialFunc0 |#$R@@21|))  (and ($Is |f#0@@3| (Tclass._System.___hFunc0 |#$R@@21|)) (|Set#Equal| (Reads0 |#$R@@21| $OneHeap |f#0@@3|) (|Set#Empty| BoxType)))))
 :qid |unknown.0:0|
 :skolemid |792|
 :pattern ( ($Is |f#0@@3| (Tclass._System.___hPartialFunc0 |#$R@@21|)))
)))
(assert (forall ((|#$R@@22| T@U) (|f#0@@4| T@U) ($h@@9 T@U) ) (!  (=> (and (and (= (type |#$R@@22|) TyType) (= (type |f#0@@4|) HandleTypeType)) (= (type $h@@9) (MapType0Type refType MapType1Type))) (= ($IsAlloc |f#0@@4| (Tclass._System.___hPartialFunc0 |#$R@@22|) $h@@9) ($IsAlloc |f#0@@4| (Tclass._System.___hFunc0 |#$R@@22|) $h@@9)))
 :qid |unknown.0:0|
 :skolemid |793|
 :pattern ( ($IsAlloc |f#0@@4| (Tclass._System.___hPartialFunc0 |#$R@@22|) $h@@9))
)))
(assert (forall ((arg0@@143 T@U) ) (! (= (type (Tclass._System.___hTotalFunc0 arg0@@143)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc0|
 :pattern ( (Tclass._System.___hTotalFunc0 arg0@@143))
)))
(assert (forall ((|#$R@@23| T@U) ) (!  (=> (= (type |#$R@@23|) TyType) (and (= (Tag (Tclass._System.___hTotalFunc0 |#$R@@23|)) Tagclass._System.___hTotalFunc0) (= (TagFamily (Tclass._System.___hTotalFunc0 |#$R@@23|)) |tytagFamily$_#TotalFunc0|)))
 :qid |unknown.0:0|
 :skolemid |794|
 :pattern ( (Tclass._System.___hTotalFunc0 |#$R@@23|))
)))
(assert (forall ((arg0@@144 T@U) ) (! (= (type (Tclass._System.___hTotalFunc0_0 arg0@@144)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc0_0|
 :pattern ( (Tclass._System.___hTotalFunc0_0 arg0@@144))
)))
(assert (forall ((|#$R@@24| T@U) ) (!  (=> (= (type |#$R@@24|) TyType) (= (Tclass._System.___hTotalFunc0_0 (Tclass._System.___hTotalFunc0 |#$R@@24|)) |#$R@@24|))
 :qid |unknown.0:0|
 :skolemid |795|
 :pattern ( (Tclass._System.___hTotalFunc0 |#$R@@24|))
)))
(assert (forall ((|#$R@@25| T@U) (bx@@41 T@U) ) (!  (=> (and (and (= (type |#$R@@25|) TyType) (= (type bx@@41) BoxType)) ($IsBox bx@@41 (Tclass._System.___hTotalFunc0 |#$R@@25|))) (and (= ($Box ($Unbox HandleTypeType bx@@41)) bx@@41) ($Is ($Unbox HandleTypeType bx@@41) (Tclass._System.___hTotalFunc0 |#$R@@25|))))
 :qid |unknown.0:0|
 :skolemid |796|
 :pattern ( ($IsBox bx@@41 (Tclass._System.___hTotalFunc0 |#$R@@25|)))
)))
(assert (forall ((|#$R@@26| T@U) (|f#0@@5| T@U) ) (!  (=> (and (= (type |#$R@@26|) TyType) (= (type |f#0@@5|) HandleTypeType)) (= ($Is |f#0@@5| (Tclass._System.___hTotalFunc0 |#$R@@26|))  (and ($Is |f#0@@5| (Tclass._System.___hPartialFunc0 |#$R@@26|)) (Requires0 |#$R@@26| $OneHeap |f#0@@5|))))
 :qid |unknown.0:0|
 :skolemid |797|
 :pattern ( ($Is |f#0@@5| (Tclass._System.___hTotalFunc0 |#$R@@26|)))
)))
(assert (forall ((|#$R@@27| T@U) (|f#0@@6| T@U) ($h@@10 T@U) ) (!  (=> (and (and (= (type |#$R@@27|) TyType) (= (type |f#0@@6|) HandleTypeType)) (= (type $h@@10) (MapType0Type refType MapType1Type))) (= ($IsAlloc |f#0@@6| (Tclass._System.___hTotalFunc0 |#$R@@27|) $h@@10) ($IsAlloc |f#0@@6| (Tclass._System.___hPartialFunc0 |#$R@@27|) $h@@10)))
 :qid |unknown.0:0|
 :skolemid |798|
 :pattern ( ($IsAlloc |f#0@@6| (Tclass._System.___hTotalFunc0 |#$R@@27|) $h@@10))
)))
(assert (= (type Tclass._System.__default) TyType))
(assert (= (Tag Tclass._System.__default) Tagclass._System.__default))
(assert (= (TagFamily Tclass._System.__default) tytagFamily$_default))
(assert (forall ((bx@@42 T@U) ) (!  (=> (and (= (type bx@@42) BoxType) ($IsBox bx@@42 Tclass._System.__default)) (and (= ($Box ($Unbox refType bx@@42)) bx@@42) ($Is ($Unbox refType bx@@42) Tclass._System.__default)))
 :qid |unknown.0:0|
 :skolemid |799|
 :pattern ( ($IsBox bx@@42 Tclass._System.__default))
)))
(assert (forall (($o@@7 T@U) ) (!  (=> (= (type $o@@7) refType) (= ($Is $o@@7 Tclass._System.__default)  (or (= $o@@7 null) (= (dtype $o@@7) Tclass._System.__default))))
 :qid |unknown.0:0|
 :skolemid |800|
 :pattern ( ($Is $o@@7 Tclass._System.__default))
)))
(assert (forall (($o@@8 T@U) ($h@@11 T@U) ) (!  (=> (and (= (type $o@@8) refType) (= (type $h@@11) (MapType0Type refType MapType1Type))) (= ($IsAlloc $o@@8 Tclass._System.__default $h@@11)  (or (= $o@@8 null) (U_2_bool (MapType1Select (MapType0Select $h@@11 $o@@8) alloc)))))
 :qid |unknown.0:0|
 :skolemid |801|
 :pattern ( ($IsAlloc $o@@8 Tclass._System.__default $h@@11))
)))
(assert  (=> true (forall ((|#$A| T@U) (|#$B| T@U) (|a#0| T@U) (|b#0| T@U) ) (!  (=> (and (and (and (and (= (type |#$A|) TyType) (= (type |#$B|) TyType)) (= (type |a#0|) BoxType)) (= (type |b#0|) BoxType)) (or (|_System.__default.rank__is__less__than#canCall| |#$A| |#$B| |a#0| |b#0|) (and ($IsBox |a#0| |#$A|) ($IsBox |b#0| |#$B|)))) true)
 :qid |unknown.0:0|
 :skolemid |802|
 :pattern ( (_System.__default.rank__is__less__than |#$A| |#$B| |a#0| |b#0|))
))))
(assert (forall ((|#$A@@0| T@U) (|#$B@@0| T@U) (|a#0@@0| T@U) (|b#0@@0| T@U) ) (!  (=> (and (and (and (and (= (type |#$A@@0|) TyType) (= (type |#$B@@0|) TyType)) (= (type |a#0@@0|) BoxType)) (= (type |b#0@@0|) BoxType)) (and ($IsBox |a#0@@0| |#$A@@0|) ($IsBox |b#0@@0| |#$B@@0|))) (= (|_System.__default.rank__is__less__than#requires| |#$A@@0| |#$B@@0| |a#0@@0| |b#0@@0|) true))
 :qid |unknown.0:0|
 :skolemid |803|
 :pattern ( (|_System.__default.rank__is__less__than#requires| |#$A@@0| |#$B@@0| |a#0@@0| |b#0@@0|))
)))
(assert (forall ((arg0@@145 T@U) (arg1@@67 T@U) (arg2@@19 T@U) ) (! (= (type (Tclass._System.___hFunc2 arg0@@145 arg1@@67 arg2@@19)) TyType)
 :qid |funType:Tclass._System.___hFunc2|
 :pattern ( (Tclass._System.___hFunc2 arg0@@145 arg1@@67 arg2@@19))
)))
(assert (forall ((|#$T0@@15| T@U) (|#$T1| T@U) (|#$R@@28| T@U) ) (!  (=> (and (and (= (type |#$T0@@15|) TyType) (= (type |#$T1|) TyType)) (= (type |#$R@@28|) TyType)) (and (= (Tag (Tclass._System.___hFunc2 |#$T0@@15| |#$T1| |#$R@@28|)) Tagclass._System.___hFunc2) (= (TagFamily (Tclass._System.___hFunc2 |#$T0@@15| |#$T1| |#$R@@28|)) |tytagFamily$_#Func2|)))
 :qid |unknown.0:0|
 :skolemid |804|
 :pattern ( (Tclass._System.___hFunc2 |#$T0@@15| |#$T1| |#$R@@28|))
)))
(assert (forall ((arg0@@146 T@U) ) (! (= (type (Tclass._System.___hFunc2_0 arg0@@146)) TyType)
 :qid |funType:Tclass._System.___hFunc2_0|
 :pattern ( (Tclass._System.___hFunc2_0 arg0@@146))
)))
(assert (forall ((|#$T0@@16| T@U) (|#$T1@@0| T@U) (|#$R@@29| T@U) ) (!  (=> (and (and (= (type |#$T0@@16|) TyType) (= (type |#$T1@@0|) TyType)) (= (type |#$R@@29|) TyType)) (= (Tclass._System.___hFunc2_0 (Tclass._System.___hFunc2 |#$T0@@16| |#$T1@@0| |#$R@@29|)) |#$T0@@16|))
 :qid |unknown.0:0|
 :skolemid |805|
 :pattern ( (Tclass._System.___hFunc2 |#$T0@@16| |#$T1@@0| |#$R@@29|))
)))
(assert (forall ((arg0@@147 T@U) ) (! (= (type (Tclass._System.___hFunc2_1 arg0@@147)) TyType)
 :qid |funType:Tclass._System.___hFunc2_1|
 :pattern ( (Tclass._System.___hFunc2_1 arg0@@147))
)))
(assert (forall ((|#$T0@@17| T@U) (|#$T1@@1| T@U) (|#$R@@30| T@U) ) (!  (=> (and (and (= (type |#$T0@@17|) TyType) (= (type |#$T1@@1|) TyType)) (= (type |#$R@@30|) TyType)) (= (Tclass._System.___hFunc2_1 (Tclass._System.___hFunc2 |#$T0@@17| |#$T1@@1| |#$R@@30|)) |#$T1@@1|))
 :qid |unknown.0:0|
 :skolemid |806|
 :pattern ( (Tclass._System.___hFunc2 |#$T0@@17| |#$T1@@1| |#$R@@30|))
)))
(assert (forall ((arg0@@148 T@U) ) (! (= (type (Tclass._System.___hFunc2_2 arg0@@148)) TyType)
 :qid |funType:Tclass._System.___hFunc2_2|
 :pattern ( (Tclass._System.___hFunc2_2 arg0@@148))
)))
(assert (forall ((|#$T0@@18| T@U) (|#$T1@@2| T@U) (|#$R@@31| T@U) ) (!  (=> (and (and (= (type |#$T0@@18|) TyType) (= (type |#$T1@@2|) TyType)) (= (type |#$R@@31|) TyType)) (= (Tclass._System.___hFunc2_2 (Tclass._System.___hFunc2 |#$T0@@18| |#$T1@@2| |#$R@@31|)) |#$R@@31|))
 :qid |unknown.0:0|
 :skolemid |807|
 :pattern ( (Tclass._System.___hFunc2 |#$T0@@18| |#$T1@@2| |#$R@@31|))
)))
(assert (forall ((|#$T0@@19| T@U) (|#$T1@@3| T@U) (|#$R@@32| T@U) (bx@@43 T@U) ) (!  (=> (and (and (and (and (= (type |#$T0@@19|) TyType) (= (type |#$T1@@3|) TyType)) (= (type |#$R@@32|) TyType)) (= (type bx@@43) BoxType)) ($IsBox bx@@43 (Tclass._System.___hFunc2 |#$T0@@19| |#$T1@@3| |#$R@@32|))) (and (= ($Box ($Unbox HandleTypeType bx@@43)) bx@@43) ($Is ($Unbox HandleTypeType bx@@43) (Tclass._System.___hFunc2 |#$T0@@19| |#$T1@@3| |#$R@@32|))))
 :qid |unknown.0:0|
 :skolemid |808|
 :pattern ( ($IsBox bx@@43 (Tclass._System.___hFunc2 |#$T0@@19| |#$T1@@3| |#$R@@32|)))
)))
(assert  (and (and (and (and (and (and (and (and (and (and (forall ((arg0@@149 T@T) (arg1@@68 T@T) (arg2@@20 T@T) (arg3@@3 T@T) ) (! (= (Ctor (MapType3Type arg0@@149 arg1@@68 arg2@@20 arg3@@3)) 25)
 :qid |ctor:MapType3Type|
)) (forall ((arg0@@150 T@T) (arg1@@69 T@T) (arg2@@21 T@T) (arg3@@4 T@T) ) (! (= (MapType3TypeInv0 (MapType3Type arg0@@150 arg1@@69 arg2@@21 arg3@@4)) arg0@@150)
 :qid |typeInv:MapType3TypeInv0|
 :pattern ( (MapType3Type arg0@@150 arg1@@69 arg2@@21 arg3@@4))
))) (forall ((arg0@@151 T@T) (arg1@@70 T@T) (arg2@@22 T@T) (arg3@@5 T@T) ) (! (= (MapType3TypeInv1 (MapType3Type arg0@@151 arg1@@70 arg2@@22 arg3@@5)) arg1@@70)
 :qid |typeInv:MapType3TypeInv1|
 :pattern ( (MapType3Type arg0@@151 arg1@@70 arg2@@22 arg3@@5))
))) (forall ((arg0@@152 T@T) (arg1@@71 T@T) (arg2@@23 T@T) (arg3@@6 T@T) ) (! (= (MapType3TypeInv2 (MapType3Type arg0@@152 arg1@@71 arg2@@23 arg3@@6)) arg2@@23)
 :qid |typeInv:MapType3TypeInv2|
 :pattern ( (MapType3Type arg0@@152 arg1@@71 arg2@@23 arg3@@6))
))) (forall ((arg0@@153 T@T) (arg1@@72 T@T) (arg2@@24 T@T) (arg3@@7 T@T) ) (! (= (MapType3TypeInv3 (MapType3Type arg0@@153 arg1@@72 arg2@@24 arg3@@7)) arg3@@7)
 :qid |typeInv:MapType3TypeInv3|
 :pattern ( (MapType3Type arg0@@153 arg1@@72 arg2@@24 arg3@@7))
))) (forall ((arg0@@154 T@U) (arg1@@73 T@U) (arg2@@25 T@U) (arg3@@8 T@U) ) (! (let ((aVar3 (MapType3TypeInv3 (type arg0@@154))))
(= (type (MapType3Select arg0@@154 arg1@@73 arg2@@25 arg3@@8)) aVar3))
 :qid |funType:MapType3Select|
 :pattern ( (MapType3Select arg0@@154 arg1@@73 arg2@@25 arg3@@8))
))) (forall ((arg0@@155 T@U) (arg1@@74 T@U) (arg2@@26 T@U) (arg3@@9 T@U) (arg4@@1 T@U) ) (! (let ((aVar3@@0 (type arg4@@1)))
(let ((aVar2@@2 (type arg3@@9)))
(let ((aVar1@@3 (type arg2@@26)))
(let ((aVar0@@1 (type arg1@@74)))
(= (type (MapType3Store arg0@@155 arg1@@74 arg2@@26 arg3@@9 arg4@@1)) (MapType3Type aVar0@@1 aVar1@@3 aVar2@@2 aVar3@@0))))))
 :qid |funType:MapType3Store|
 :pattern ( (MapType3Store arg0@@155 arg1@@74 arg2@@26 arg3@@9 arg4@@1))
))) (forall ((m@@49 T@U) (x0@@9 T@U) (x1@@3 T@U) (x2 T@U) (val@@10 T@U) ) (! (let ((aVar3@@1 (MapType3TypeInv3 (type m@@49))))
 (=> (= (type val@@10) aVar3@@1) (= (MapType3Select (MapType3Store m@@49 x0@@9 x1@@3 x2 val@@10) x0@@9 x1@@3 x2) val@@10)))
 :qid |mapAx0:MapType3Select|
 :weight 0
))) (and (and (and (forall ((val@@11 T@U) (m@@50 T@U) (x0@@10 T@U) (x1@@4 T@U) (x2@@0 T@U) (y0@@6 T@U) (y1@@2 T@U) (y2 T@U) ) (!  (or (= x0@@10 y0@@6) (= (MapType3Select (MapType3Store m@@50 x0@@10 x1@@4 x2@@0 val@@11) y0@@6 y1@@2 y2) (MapType3Select m@@50 y0@@6 y1@@2 y2)))
 :qid |mapAx1:MapType3Select:0|
 :weight 0
)) (forall ((val@@12 T@U) (m@@51 T@U) (x0@@11 T@U) (x1@@5 T@U) (x2@@1 T@U) (y0@@7 T@U) (y1@@3 T@U) (y2@@0 T@U) ) (!  (or (= x1@@5 y1@@3) (= (MapType3Select (MapType3Store m@@51 x0@@11 x1@@5 x2@@1 val@@12) y0@@7 y1@@3 y2@@0) (MapType3Select m@@51 y0@@7 y1@@3 y2@@0)))
 :qid |mapAx1:MapType3Select:1|
 :weight 0
))) (forall ((val@@13 T@U) (m@@52 T@U) (x0@@12 T@U) (x1@@6 T@U) (x2@@2 T@U) (y0@@8 T@U) (y1@@4 T@U) (y2@@1 T@U) ) (!  (or (= x2@@2 y2@@1) (= (MapType3Select (MapType3Store m@@52 x0@@12 x1@@6 x2@@2 val@@13) y0@@8 y1@@4 y2@@1) (MapType3Select m@@52 y0@@8 y1@@4 y2@@1)))
 :qid |mapAx1:MapType3Select:2|
 :weight 0
))) (forall ((val@@14 T@U) (m@@53 T@U) (x0@@13 T@U) (x1@@7 T@U) (x2@@3 T@U) (y0@@9 T@U) (y1@@5 T@U) (y2@@2 T@U) ) (!  (or true (= (MapType3Select (MapType3Store m@@53 x0@@13 x1@@7 x2@@3 val@@14) y0@@9 y1@@5 y2@@2) (MapType3Select m@@53 y0@@9 y1@@5 y2@@2)))
 :qid |mapAx2:MapType3Select|
 :weight 0
)))) (forall ((arg0@@156 T@U) (arg1@@75 T@U) (arg2@@27 T@U) (arg3@@10 T@U) (arg4@@2 T@U) (arg5 T@U) (arg6 T@U) ) (! (= (type (Apply2 arg0@@156 arg1@@75 arg2@@27 arg3@@10 arg4@@2 arg5 arg6)) BoxType)
 :qid |funType:Apply2|
 :pattern ( (Apply2 arg0@@156 arg1@@75 arg2@@27 arg3@@10 arg4@@2 arg5 arg6))
))) (forall ((arg0@@157 T@U) (arg1@@76 T@U) (arg2@@28 T@U) ) (! (= (type (Handle2 arg0@@157 arg1@@76 arg2@@28)) HandleTypeType)
 :qid |funType:Handle2|
 :pattern ( (Handle2 arg0@@157 arg1@@76 arg2@@28))
))))
(assert (forall ((t0@@46 T@U) (t1@@22 T@U) (t2 T@U) (heap@@11 T@U) (h@@33 T@U) (r@@14 T@U) (rd@@5 T@U) (bx0@@13 T@U) (bx1 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (= (type t0@@46) TyType) (= (type t1@@22) TyType)) (= (type t2) TyType)) (= (type heap@@11) (MapType0Type refType MapType1Type))) (= (type h@@33) (MapType3Type (MapType0Type refType MapType1Type) BoxType BoxType BoxType))) (= (type r@@14) (MapType3Type (MapType0Type refType MapType1Type) BoxType BoxType boolType))) (= (type rd@@5) (MapType3Type (MapType0Type refType MapType1Type) BoxType BoxType (MapType0Type BoxType boolType)))) (= (type bx0@@13) BoxType)) (= (type bx1) BoxType)) (= (Apply2 t0@@46 t1@@22 t2 heap@@11 (Handle2 h@@33 r@@14 rd@@5) bx0@@13 bx1) (MapType3Select h@@33 heap@@11 bx0@@13 bx1)))
 :qid |unknown.0:0|
 :skolemid |809|
 :pattern ( (Apply2 t0@@46 t1@@22 t2 heap@@11 (Handle2 h@@33 r@@14 rd@@5) bx0@@13 bx1))
)))
(assert (forall ((t0@@47 T@U) (t1@@23 T@U) (t2@@0 T@U) (heap@@12 T@U) (h@@34 T@U) (r@@15 T@U) (rd@@6 T@U) (bx0@@14 T@U) (bx1@@0 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (= (type t0@@47) TyType) (= (type t1@@23) TyType)) (= (type t2@@0) TyType)) (= (type heap@@12) (MapType0Type refType MapType1Type))) (= (type h@@34) (MapType3Type (MapType0Type refType MapType1Type) BoxType BoxType BoxType))) (= (type r@@15) (MapType3Type (MapType0Type refType MapType1Type) BoxType BoxType boolType))) (= (type rd@@6) (MapType3Type (MapType0Type refType MapType1Type) BoxType BoxType (MapType0Type BoxType boolType)))) (= (type bx0@@14) BoxType)) (= (type bx1@@0) BoxType)) (U_2_bool (MapType3Select r@@15 heap@@12 bx0@@14 bx1@@0))) (Requires2 t0@@47 t1@@23 t2@@0 heap@@12 (Handle2 h@@34 r@@15 rd@@6) bx0@@14 bx1@@0))
 :qid |unknown.0:0|
 :skolemid |810|
 :pattern ( (Requires2 t0@@47 t1@@23 t2@@0 heap@@12 (Handle2 h@@34 r@@15 rd@@6) bx0@@14 bx1@@0))
)))
(assert (forall ((arg0@@158 T@U) (arg1@@77 T@U) (arg2@@29 T@U) (arg3@@11 T@U) (arg4@@3 T@U) (arg5@@0 T@U) (arg6@@0 T@U) ) (! (= (type (Reads2 arg0@@158 arg1@@77 arg2@@29 arg3@@11 arg4@@3 arg5@@0 arg6@@0)) (MapType0Type BoxType boolType))
 :qid |funType:Reads2|
 :pattern ( (Reads2 arg0@@158 arg1@@77 arg2@@29 arg3@@11 arg4@@3 arg5@@0 arg6@@0))
)))
(assert (forall ((t0@@48 T@U) (t1@@24 T@U) (t2@@1 T@U) (heap@@13 T@U) (h@@35 T@U) (r@@16 T@U) (rd@@7 T@U) (bx0@@15 T@U) (bx1@@1 T@U) (bx@@44 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (= (type t0@@48) TyType) (= (type t1@@24) TyType)) (= (type t2@@1) TyType)) (= (type heap@@13) (MapType0Type refType MapType1Type))) (= (type h@@35) (MapType3Type (MapType0Type refType MapType1Type) BoxType BoxType BoxType))) (= (type r@@16) (MapType3Type (MapType0Type refType MapType1Type) BoxType BoxType boolType))) (= (type rd@@7) (MapType3Type (MapType0Type refType MapType1Type) BoxType BoxType (MapType0Type BoxType boolType)))) (= (type bx0@@15) BoxType)) (= (type bx1@@1) BoxType)) (= (type bx@@44) BoxType)) (= (U_2_bool (MapType0Select (Reads2 t0@@48 t1@@24 t2@@1 heap@@13 (Handle2 h@@35 r@@16 rd@@7) bx0@@15 bx1@@1) bx@@44)) (U_2_bool (MapType0Select (MapType3Select rd@@7 heap@@13 bx0@@15 bx1@@1) bx@@44))))
 :qid |unknown.0:0|
 :skolemid |811|
 :pattern ( (MapType0Select (Reads2 t0@@48 t1@@24 t2@@1 heap@@13 (Handle2 h@@35 r@@16 rd@@7) bx0@@15 bx1@@1) bx@@44))
)))
(assert (forall ((t0@@49 T@U) (t1@@25 T@U) (t2@@2 T@U) (h0@@12 T@U) (h1@@12 T@U) (f@@29 T@U) (bx0@@16 T@U) (bx1@@2 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (= (type t0@@49) TyType) (= (type t1@@25) TyType)) (= (type t2@@2) TyType)) (= (type h0@@12) (MapType0Type refType MapType1Type))) (= (type h1@@12) (MapType0Type refType MapType1Type))) (= (type f@@29) HandleTypeType)) (= (type bx0@@16) BoxType)) (= (type bx1@@2) BoxType)) (and (and (and ($HeapSucc h0@@12 h1@@12) (and ($IsGoodHeap h0@@12) ($IsGoodHeap h1@@12))) (and (and ($IsBox bx0@@16 t0@@49) ($IsBox bx1@@2 t1@@25)) ($Is f@@29 (Tclass._System.___hFunc2 t0@@49 t1@@25 t2@@2)))) (forall ((o@@56 T@U) (fld@@11 T@U) ) (! (let ((a@@94 (FieldTypeInv0 (type fld@@11))))
 (=> (and (and (= (type o@@56) refType) (= (type fld@@11) (FieldType a@@94))) (and (not (= o@@56 null)) (U_2_bool (MapType0Select (Reads2 t0@@49 t1@@25 t2@@2 h0@@12 f@@29 bx0@@16 bx1@@2) ($Box o@@56))))) (= (MapType1Select (MapType0Select h0@@12 o@@56) fld@@11) (MapType1Select (MapType0Select h1@@12 o@@56) fld@@11))))
 :qid |unknown.0:0|
 :skolemid |812|
 :no-pattern (type o@@56)
 :no-pattern (type fld@@11)
 :no-pattern (U_2_int o@@56)
 :no-pattern (U_2_bool o@@56)
 :no-pattern (U_2_int fld@@11)
 :no-pattern (U_2_bool fld@@11)
)))) (= (Reads2 t0@@49 t1@@25 t2@@2 h0@@12 f@@29 bx0@@16 bx1@@2) (Reads2 t0@@49 t1@@25 t2@@2 h1@@12 f@@29 bx0@@16 bx1@@2)))
 :qid |unknown.0:0|
 :skolemid |813|
 :pattern ( ($HeapSucc h0@@12 h1@@12) (Reads2 t0@@49 t1@@25 t2@@2 h1@@12 f@@29 bx0@@16 bx1@@2))
)))
(assert (forall ((t0@@50 T@U) (t1@@26 T@U) (t2@@3 T@U) (h0@@13 T@U) (h1@@13 T@U) (f@@30 T@U) (bx0@@17 T@U) (bx1@@3 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (= (type t0@@50) TyType) (= (type t1@@26) TyType)) (= (type t2@@3) TyType)) (= (type h0@@13) (MapType0Type refType MapType1Type))) (= (type h1@@13) (MapType0Type refType MapType1Type))) (= (type f@@30) HandleTypeType)) (= (type bx0@@17) BoxType)) (= (type bx1@@3) BoxType)) (and (and (and ($HeapSucc h0@@13 h1@@13) (and ($IsGoodHeap h0@@13) ($IsGoodHeap h1@@13))) (and (and ($IsBox bx0@@17 t0@@50) ($IsBox bx1@@3 t1@@26)) ($Is f@@30 (Tclass._System.___hFunc2 t0@@50 t1@@26 t2@@3)))) (forall ((o@@57 T@U) (fld@@12 T@U) ) (! (let ((a@@95 (FieldTypeInv0 (type fld@@12))))
 (=> (and (and (= (type o@@57) refType) (= (type fld@@12) (FieldType a@@95))) (and (not (= o@@57 null)) (U_2_bool (MapType0Select (Reads2 t0@@50 t1@@26 t2@@3 h1@@13 f@@30 bx0@@17 bx1@@3) ($Box o@@57))))) (= (MapType1Select (MapType0Select h0@@13 o@@57) fld@@12) (MapType1Select (MapType0Select h1@@13 o@@57) fld@@12))))
 :qid |unknown.0:0|
 :skolemid |814|
 :no-pattern (type o@@57)
 :no-pattern (type fld@@12)
 :no-pattern (U_2_int o@@57)
 :no-pattern (U_2_bool o@@57)
 :no-pattern (U_2_int fld@@12)
 :no-pattern (U_2_bool fld@@12)
)))) (= (Reads2 t0@@50 t1@@26 t2@@3 h0@@13 f@@30 bx0@@17 bx1@@3) (Reads2 t0@@50 t1@@26 t2@@3 h1@@13 f@@30 bx0@@17 bx1@@3)))
 :qid |unknown.0:0|
 :skolemid |815|
 :pattern ( ($HeapSucc h0@@13 h1@@13) (Reads2 t0@@50 t1@@26 t2@@3 h1@@13 f@@30 bx0@@17 bx1@@3))
)))
(assert (forall ((t0@@51 T@U) (t1@@27 T@U) (t2@@4 T@U) (h0@@14 T@U) (h1@@14 T@U) (f@@31 T@U) (bx0@@18 T@U) (bx1@@4 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (= (type t0@@51) TyType) (= (type t1@@27) TyType)) (= (type t2@@4) TyType)) (= (type h0@@14) (MapType0Type refType MapType1Type))) (= (type h1@@14) (MapType0Type refType MapType1Type))) (= (type f@@31) HandleTypeType)) (= (type bx0@@18) BoxType)) (= (type bx1@@4) BoxType)) (and (and (and ($HeapSucc h0@@14 h1@@14) (and ($IsGoodHeap h0@@14) ($IsGoodHeap h1@@14))) (and (and ($IsBox bx0@@18 t0@@51) ($IsBox bx1@@4 t1@@27)) ($Is f@@31 (Tclass._System.___hFunc2 t0@@51 t1@@27 t2@@4)))) (forall ((o@@58 T@U) (fld@@13 T@U) ) (! (let ((a@@96 (FieldTypeInv0 (type fld@@13))))
 (=> (and (and (= (type o@@58) refType) (= (type fld@@13) (FieldType a@@96))) (and (not (= o@@58 null)) (U_2_bool (MapType0Select (Reads2 t0@@51 t1@@27 t2@@4 h0@@14 f@@31 bx0@@18 bx1@@4) ($Box o@@58))))) (= (MapType1Select (MapType0Select h0@@14 o@@58) fld@@13) (MapType1Select (MapType0Select h1@@14 o@@58) fld@@13))))
 :qid |unknown.0:0|
 :skolemid |816|
 :no-pattern (type o@@58)
 :no-pattern (type fld@@13)
 :no-pattern (U_2_int o@@58)
 :no-pattern (U_2_bool o@@58)
 :no-pattern (U_2_int fld@@13)
 :no-pattern (U_2_bool fld@@13)
)))) (= (Requires2 t0@@51 t1@@27 t2@@4 h0@@14 f@@31 bx0@@18 bx1@@4) (Requires2 t0@@51 t1@@27 t2@@4 h1@@14 f@@31 bx0@@18 bx1@@4)))
 :qid |unknown.0:0|
 :skolemid |817|
 :pattern ( ($HeapSucc h0@@14 h1@@14) (Requires2 t0@@51 t1@@27 t2@@4 h1@@14 f@@31 bx0@@18 bx1@@4))
)))
(assert (forall ((t0@@52 T@U) (t1@@28 T@U) (t2@@5 T@U) (h0@@15 T@U) (h1@@15 T@U) (f@@32 T@U) (bx0@@19 T@U) (bx1@@5 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (= (type t0@@52) TyType) (= (type t1@@28) TyType)) (= (type t2@@5) TyType)) (= (type h0@@15) (MapType0Type refType MapType1Type))) (= (type h1@@15) (MapType0Type refType MapType1Type))) (= (type f@@32) HandleTypeType)) (= (type bx0@@19) BoxType)) (= (type bx1@@5) BoxType)) (and (and (and ($HeapSucc h0@@15 h1@@15) (and ($IsGoodHeap h0@@15) ($IsGoodHeap h1@@15))) (and (and ($IsBox bx0@@19 t0@@52) ($IsBox bx1@@5 t1@@28)) ($Is f@@32 (Tclass._System.___hFunc2 t0@@52 t1@@28 t2@@5)))) (forall ((o@@59 T@U) (fld@@14 T@U) ) (! (let ((a@@97 (FieldTypeInv0 (type fld@@14))))
 (=> (and (and (= (type o@@59) refType) (= (type fld@@14) (FieldType a@@97))) (and (not (= o@@59 null)) (U_2_bool (MapType0Select (Reads2 t0@@52 t1@@28 t2@@5 h1@@15 f@@32 bx0@@19 bx1@@5) ($Box o@@59))))) (= (MapType1Select (MapType0Select h0@@15 o@@59) fld@@14) (MapType1Select (MapType0Select h1@@15 o@@59) fld@@14))))
 :qid |unknown.0:0|
 :skolemid |818|
 :no-pattern (type o@@59)
 :no-pattern (type fld@@14)
 :no-pattern (U_2_int o@@59)
 :no-pattern (U_2_bool o@@59)
 :no-pattern (U_2_int fld@@14)
 :no-pattern (U_2_bool fld@@14)
)))) (= (Requires2 t0@@52 t1@@28 t2@@5 h0@@15 f@@32 bx0@@19 bx1@@5) (Requires2 t0@@52 t1@@28 t2@@5 h1@@15 f@@32 bx0@@19 bx1@@5)))
 :qid |unknown.0:0|
 :skolemid |819|
 :pattern ( ($HeapSucc h0@@15 h1@@15) (Requires2 t0@@52 t1@@28 t2@@5 h1@@15 f@@32 bx0@@19 bx1@@5))
)))
(assert (forall ((t0@@53 T@U) (t1@@29 T@U) (t2@@6 T@U) (h0@@16 T@U) (h1@@16 T@U) (f@@33 T@U) (bx0@@20 T@U) (bx1@@6 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (= (type t0@@53) TyType) (= (type t1@@29) TyType)) (= (type t2@@6) TyType)) (= (type h0@@16) (MapType0Type refType MapType1Type))) (= (type h1@@16) (MapType0Type refType MapType1Type))) (= (type f@@33) HandleTypeType)) (= (type bx0@@20) BoxType)) (= (type bx1@@6) BoxType)) (and (and (and ($HeapSucc h0@@16 h1@@16) (and ($IsGoodHeap h0@@16) ($IsGoodHeap h1@@16))) (and (and ($IsBox bx0@@20 t0@@53) ($IsBox bx1@@6 t1@@29)) ($Is f@@33 (Tclass._System.___hFunc2 t0@@53 t1@@29 t2@@6)))) (forall ((o@@60 T@U) (fld@@15 T@U) ) (! (let ((a@@98 (FieldTypeInv0 (type fld@@15))))
 (=> (and (and (= (type o@@60) refType) (= (type fld@@15) (FieldType a@@98))) (and (not (= o@@60 null)) (U_2_bool (MapType0Select (Reads2 t0@@53 t1@@29 t2@@6 h0@@16 f@@33 bx0@@20 bx1@@6) ($Box o@@60))))) (= (MapType1Select (MapType0Select h0@@16 o@@60) fld@@15) (MapType1Select (MapType0Select h1@@16 o@@60) fld@@15))))
 :qid |unknown.0:0|
 :skolemid |820|
 :no-pattern (type o@@60)
 :no-pattern (type fld@@15)
 :no-pattern (U_2_int o@@60)
 :no-pattern (U_2_bool o@@60)
 :no-pattern (U_2_int fld@@15)
 :no-pattern (U_2_bool fld@@15)
)))) (= (Apply2 t0@@53 t1@@29 t2@@6 h0@@16 f@@33 bx0@@20 bx1@@6) (Apply2 t0@@53 t1@@29 t2@@6 h1@@16 f@@33 bx0@@20 bx1@@6)))
 :qid |unknown.0:0|
 :skolemid |821|
 :pattern ( ($HeapSucc h0@@16 h1@@16) (Apply2 t0@@53 t1@@29 t2@@6 h1@@16 f@@33 bx0@@20 bx1@@6))
)))
(assert (forall ((t0@@54 T@U) (t1@@30 T@U) (t2@@7 T@U) (h0@@17 T@U) (h1@@17 T@U) (f@@34 T@U) (bx0@@21 T@U) (bx1@@7 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (= (type t0@@54) TyType) (= (type t1@@30) TyType)) (= (type t2@@7) TyType)) (= (type h0@@17) (MapType0Type refType MapType1Type))) (= (type h1@@17) (MapType0Type refType MapType1Type))) (= (type f@@34) HandleTypeType)) (= (type bx0@@21) BoxType)) (= (type bx1@@7) BoxType)) (and (and (and ($HeapSucc h0@@17 h1@@17) (and ($IsGoodHeap h0@@17) ($IsGoodHeap h1@@17))) (and (and ($IsBox bx0@@21 t0@@54) ($IsBox bx1@@7 t1@@30)) ($Is f@@34 (Tclass._System.___hFunc2 t0@@54 t1@@30 t2@@7)))) (forall ((o@@61 T@U) (fld@@16 T@U) ) (! (let ((a@@99 (FieldTypeInv0 (type fld@@16))))
 (=> (and (and (= (type o@@61) refType) (= (type fld@@16) (FieldType a@@99))) (and (not (= o@@61 null)) (U_2_bool (MapType0Select (Reads2 t0@@54 t1@@30 t2@@7 h1@@17 f@@34 bx0@@21 bx1@@7) ($Box o@@61))))) (= (MapType1Select (MapType0Select h0@@17 o@@61) fld@@16) (MapType1Select (MapType0Select h1@@17 o@@61) fld@@16))))
 :qid |unknown.0:0|
 :skolemid |822|
 :no-pattern (type o@@61)
 :no-pattern (type fld@@16)
 :no-pattern (U_2_int o@@61)
 :no-pattern (U_2_bool o@@61)
 :no-pattern (U_2_int fld@@16)
 :no-pattern (U_2_bool fld@@16)
)))) (= (Apply2 t0@@54 t1@@30 t2@@7 h0@@17 f@@34 bx0@@21 bx1@@7) (Apply2 t0@@54 t1@@30 t2@@7 h1@@17 f@@34 bx0@@21 bx1@@7)))
 :qid |unknown.0:0|
 :skolemid |823|
 :pattern ( ($HeapSucc h0@@17 h1@@17) (Apply2 t0@@54 t1@@30 t2@@7 h1@@17 f@@34 bx0@@21 bx1@@7))
)))
(assert (forall ((t0@@55 T@U) (t1@@31 T@U) (t2@@8 T@U) (heap@@14 T@U) (f@@35 T@U) (bx0@@22 T@U) (bx1@@8 T@U) ) (!  (=> (and (and (and (and (and (and (and (= (type t0@@55) TyType) (= (type t1@@31) TyType)) (= (type t2@@8) TyType)) (= (type heap@@14) (MapType0Type refType MapType1Type))) (= (type f@@35) HandleTypeType)) (= (type bx0@@22) BoxType)) (= (type bx1@@8) BoxType)) (and ($IsGoodHeap heap@@14) (and (and ($IsBox bx0@@22 t0@@55) ($IsBox bx1@@8 t1@@31)) ($Is f@@35 (Tclass._System.___hFunc2 t0@@55 t1@@31 t2@@8))))) (= (|Set#Equal| (Reads2 t0@@55 t1@@31 t2@@8 $OneHeap f@@35 bx0@@22 bx1@@8) (|Set#Empty| BoxType)) (|Set#Equal| (Reads2 t0@@55 t1@@31 t2@@8 heap@@14 f@@35 bx0@@22 bx1@@8) (|Set#Empty| BoxType))))
 :qid |unknown.0:0|
 :skolemid |824|
 :pattern ( (Reads2 t0@@55 t1@@31 t2@@8 $OneHeap f@@35 bx0@@22 bx1@@8) ($IsGoodHeap heap@@14))
 :pattern ( (Reads2 t0@@55 t1@@31 t2@@8 heap@@14 f@@35 bx0@@22 bx1@@8))
)))
(assert (forall ((t0@@56 T@U) (t1@@32 T@U) (t2@@9 T@U) (heap@@15 T@U) (f@@36 T@U) (bx0@@23 T@U) (bx1@@9 T@U) ) (!  (=> (and (and (and (and (and (and (and (= (type t0@@56) TyType) (= (type t1@@32) TyType)) (= (type t2@@9) TyType)) (= (type heap@@15) (MapType0Type refType MapType1Type))) (= (type f@@36) HandleTypeType)) (= (type bx0@@23) BoxType)) (= (type bx1@@9) BoxType)) (and (and ($IsGoodHeap heap@@15) (and (and ($IsBox bx0@@23 t0@@56) ($IsBox bx1@@9 t1@@32)) ($Is f@@36 (Tclass._System.___hFunc2 t0@@56 t1@@32 t2@@9)))) (|Set#Equal| (Reads2 t0@@56 t1@@32 t2@@9 $OneHeap f@@36 bx0@@23 bx1@@9) (|Set#Empty| BoxType)))) (= (Requires2 t0@@56 t1@@32 t2@@9 $OneHeap f@@36 bx0@@23 bx1@@9) (Requires2 t0@@56 t1@@32 t2@@9 heap@@15 f@@36 bx0@@23 bx1@@9)))
 :qid |unknown.0:0|
 :skolemid |825|
 :pattern ( (Requires2 t0@@56 t1@@32 t2@@9 $OneHeap f@@36 bx0@@23 bx1@@9) ($IsGoodHeap heap@@15))
 :pattern ( (Requires2 t0@@56 t1@@32 t2@@9 heap@@15 f@@36 bx0@@23 bx1@@9))
)))
(assert (forall ((f@@37 T@U) (t0@@57 T@U) (t1@@33 T@U) (t2@@10 T@U) ) (!  (=> (and (and (and (= (type f@@37) HandleTypeType) (= (type t0@@57) TyType)) (= (type t1@@33) TyType)) (= (type t2@@10) TyType)) (= ($Is f@@37 (Tclass._System.___hFunc2 t0@@57 t1@@33 t2@@10)) (forall ((h@@36 T@U) (bx0@@24 T@U) (bx1@@10 T@U) ) (!  (=> (and (and (and (= (type h@@36) (MapType0Type refType MapType1Type)) (= (type bx0@@24) BoxType)) (= (type bx1@@10) BoxType)) (and (and ($IsGoodHeap h@@36) (and ($IsBox bx0@@24 t0@@57) ($IsBox bx1@@10 t1@@33))) (Requires2 t0@@57 t1@@33 t2@@10 h@@36 f@@37 bx0@@24 bx1@@10))) ($IsBox (Apply2 t0@@57 t1@@33 t2@@10 h@@36 f@@37 bx0@@24 bx1@@10) t2@@10))
 :qid |DafnyPreludebpl.545:12|
 :skolemid |826|
 :pattern ( (Apply2 t0@@57 t1@@33 t2@@10 h@@36 f@@37 bx0@@24 bx1@@10))
))))
 :qid |unknown.0:0|
 :skolemid |827|
 :pattern ( ($Is f@@37 (Tclass._System.___hFunc2 t0@@57 t1@@33 t2@@10)))
)))
(assert (forall ((f@@38 T@U) (t0@@58 T@U) (t1@@34 T@U) (t2@@11 T@U) (u0@@1 T@U) (u1@@0 T@U) (u2 T@U) ) (!  (=> (and (and (and (and (and (and (and (= (type f@@38) HandleTypeType) (= (type t0@@58) TyType)) (= (type t1@@34) TyType)) (= (type t2@@11) TyType)) (= (type u0@@1) TyType)) (= (type u1@@0) TyType)) (= (type u2) TyType)) (and (and (and ($Is f@@38 (Tclass._System.___hFunc2 t0@@58 t1@@34 t2@@11)) (forall ((bx@@45 T@U) ) (!  (=> (and (= (type bx@@45) BoxType) ($IsBox bx@@45 u0@@1)) ($IsBox bx@@45 t0@@58))
 :qid |unknown.0:0|
 :skolemid |828|
 :pattern ( ($IsBox bx@@45 u0@@1))
 :pattern ( ($IsBox bx@@45 t0@@58))
))) (forall ((bx@@46 T@U) ) (!  (=> (and (= (type bx@@46) BoxType) ($IsBox bx@@46 u1@@0)) ($IsBox bx@@46 t1@@34))
 :qid |unknown.0:0|
 :skolemid |829|
 :pattern ( ($IsBox bx@@46 u1@@0))
 :pattern ( ($IsBox bx@@46 t1@@34))
))) (forall ((bx@@47 T@U) ) (!  (=> (and (= (type bx@@47) BoxType) ($IsBox bx@@47 t2@@11)) ($IsBox bx@@47 u2))
 :qid |unknown.0:0|
 :skolemid |830|
 :pattern ( ($IsBox bx@@47 t2@@11))
 :pattern ( ($IsBox bx@@47 u2))
)))) ($Is f@@38 (Tclass._System.___hFunc2 u0@@1 u1@@0 u2)))
 :qid |unknown.0:0|
 :skolemid |831|
 :pattern ( ($Is f@@38 (Tclass._System.___hFunc2 t0@@58 t1@@34 t2@@11)) ($Is f@@38 (Tclass._System.___hFunc2 u0@@1 u1@@0 u2)))
)))
(assert (forall ((f@@39 T@U) (t0@@59 T@U) (t1@@35 T@U) (t2@@12 T@U) (h@@37 T@U) ) (!  (=> (and (and (and (and (and (= (type f@@39) HandleTypeType) (= (type t0@@59) TyType)) (= (type t1@@35) TyType)) (= (type t2@@12) TyType)) (= (type h@@37) (MapType0Type refType MapType1Type))) ($IsGoodHeap h@@37)) (= ($IsAlloc f@@39 (Tclass._System.___hFunc2 t0@@59 t1@@35 t2@@12) h@@37) (forall ((bx0@@25 T@U) (bx1@@11 T@U) ) (!  (=> (and (= (type bx0@@25) BoxType) (= (type bx1@@11) BoxType)) (=> (and (and (and ($IsBox bx0@@25 t0@@59) ($IsAllocBox bx0@@25 t0@@59 h@@37)) (and ($IsBox bx1@@11 t1@@35) ($IsAllocBox bx1@@11 t1@@35 h@@37))) (Requires2 t0@@59 t1@@35 t2@@12 h@@37 f@@39 bx0@@25 bx1@@11)) (forall ((r@@17 T@U) ) (!  (=> (= (type r@@17) refType) (=> (and (not (= r@@17 null)) (U_2_bool (MapType0Select (Reads2 t0@@59 t1@@35 t2@@12 h@@37 f@@39 bx0@@25 bx1@@11) ($Box r@@17)))) (U_2_bool (MapType1Select (MapType0Select h@@37 r@@17) alloc))))
 :qid |unknown.0:0|
 :skolemid |832|
 :pattern ( (MapType0Select (Reads2 t0@@59 t1@@35 t2@@12 h@@37 f@@39 bx0@@25 bx1@@11) ($Box r@@17)))
))))
 :qid |unknown.0:0|
 :skolemid |833|
 :pattern ( (Apply2 t0@@59 t1@@35 t2@@12 h@@37 f@@39 bx0@@25 bx1@@11))
 :pattern ( (Reads2 t0@@59 t1@@35 t2@@12 h@@37 f@@39 bx0@@25 bx1@@11))
))))
 :qid |unknown.0:0|
 :skolemid |834|
 :pattern ( ($IsAlloc f@@39 (Tclass._System.___hFunc2 t0@@59 t1@@35 t2@@12) h@@37))
)))
(assert (forall ((f@@40 T@U) (t0@@60 T@U) (t1@@36 T@U) (t2@@13 T@U) (h@@38 T@U) ) (!  (=> (and (and (and (and (and (= (type f@@40) HandleTypeType) (= (type t0@@60) TyType)) (= (type t1@@36) TyType)) (= (type t2@@13) TyType)) (= (type h@@38) (MapType0Type refType MapType1Type))) (and ($IsGoodHeap h@@38) ($IsAlloc f@@40 (Tclass._System.___hFunc2 t0@@60 t1@@36 t2@@13) h@@38))) (forall ((bx0@@26 T@U) (bx1@@12 T@U) ) (!  (=> (and (= (type bx0@@26) BoxType) (= (type bx1@@12) BoxType)) (=> (and (and ($IsAllocBox bx0@@26 t0@@60 h@@38) ($IsAllocBox bx1@@12 t1@@36 h@@38)) (Requires2 t0@@60 t1@@36 t2@@13 h@@38 f@@40 bx0@@26 bx1@@12)) ($IsAllocBox (Apply2 t0@@60 t1@@36 t2@@13 h@@38 f@@40 bx0@@26 bx1@@12) t2@@13 h@@38)))
 :qid |unknown.0:0|
 :skolemid |835|
 :pattern ( (Apply2 t0@@60 t1@@36 t2@@13 h@@38 f@@40 bx0@@26 bx1@@12))
)))
 :qid |unknown.0:0|
 :skolemid |836|
 :pattern ( ($IsAlloc f@@40 (Tclass._System.___hFunc2 t0@@60 t1@@36 t2@@13) h@@38))
)))
(assert (forall ((arg0@@159 T@U) (arg1@@78 T@U) (arg2@@30 T@U) ) (! (= (type (Tclass._System.___hPartialFunc2 arg0@@159 arg1@@78 arg2@@30)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc2|
 :pattern ( (Tclass._System.___hPartialFunc2 arg0@@159 arg1@@78 arg2@@30))
)))
(assert (forall ((|#$T0@@20| T@U) (|#$T1@@4| T@U) (|#$R@@33| T@U) ) (!  (=> (and (and (= (type |#$T0@@20|) TyType) (= (type |#$T1@@4|) TyType)) (= (type |#$R@@33|) TyType)) (and (= (Tag (Tclass._System.___hPartialFunc2 |#$T0@@20| |#$T1@@4| |#$R@@33|)) Tagclass._System.___hPartialFunc2) (= (TagFamily (Tclass._System.___hPartialFunc2 |#$T0@@20| |#$T1@@4| |#$R@@33|)) |tytagFamily$_#PartialFunc2|)))
 :qid |unknown.0:0|
 :skolemid |837|
 :pattern ( (Tclass._System.___hPartialFunc2 |#$T0@@20| |#$T1@@4| |#$R@@33|))
)))
(assert (forall ((arg0@@160 T@U) ) (! (= (type (Tclass._System.___hPartialFunc2_0 arg0@@160)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc2_0|
 :pattern ( (Tclass._System.___hPartialFunc2_0 arg0@@160))
)))
(assert (forall ((|#$T0@@21| T@U) (|#$T1@@5| T@U) (|#$R@@34| T@U) ) (!  (=> (and (and (= (type |#$T0@@21|) TyType) (= (type |#$T1@@5|) TyType)) (= (type |#$R@@34|) TyType)) (= (Tclass._System.___hPartialFunc2_0 (Tclass._System.___hPartialFunc2 |#$T0@@21| |#$T1@@5| |#$R@@34|)) |#$T0@@21|))
 :qid |unknown.0:0|
 :skolemid |838|
 :pattern ( (Tclass._System.___hPartialFunc2 |#$T0@@21| |#$T1@@5| |#$R@@34|))
)))
(assert (forall ((arg0@@161 T@U) ) (! (= (type (Tclass._System.___hPartialFunc2_1 arg0@@161)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc2_1|
 :pattern ( (Tclass._System.___hPartialFunc2_1 arg0@@161))
)))
(assert (forall ((|#$T0@@22| T@U) (|#$T1@@6| T@U) (|#$R@@35| T@U) ) (!  (=> (and (and (= (type |#$T0@@22|) TyType) (= (type |#$T1@@6|) TyType)) (= (type |#$R@@35|) TyType)) (= (Tclass._System.___hPartialFunc2_1 (Tclass._System.___hPartialFunc2 |#$T0@@22| |#$T1@@6| |#$R@@35|)) |#$T1@@6|))
 :qid |unknown.0:0|
 :skolemid |839|
 :pattern ( (Tclass._System.___hPartialFunc2 |#$T0@@22| |#$T1@@6| |#$R@@35|))
)))
(assert (forall ((arg0@@162 T@U) ) (! (= (type (Tclass._System.___hPartialFunc2_2 arg0@@162)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc2_2|
 :pattern ( (Tclass._System.___hPartialFunc2_2 arg0@@162))
)))
(assert (forall ((|#$T0@@23| T@U) (|#$T1@@7| T@U) (|#$R@@36| T@U) ) (!  (=> (and (and (= (type |#$T0@@23|) TyType) (= (type |#$T1@@7|) TyType)) (= (type |#$R@@36|) TyType)) (= (Tclass._System.___hPartialFunc2_2 (Tclass._System.___hPartialFunc2 |#$T0@@23| |#$T1@@7| |#$R@@36|)) |#$R@@36|))
 :qid |unknown.0:0|
 :skolemid |840|
 :pattern ( (Tclass._System.___hPartialFunc2 |#$T0@@23| |#$T1@@7| |#$R@@36|))
)))
(assert (forall ((|#$T0@@24| T@U) (|#$T1@@8| T@U) (|#$R@@37| T@U) (bx@@48 T@U) ) (!  (=> (and (and (and (and (= (type |#$T0@@24|) TyType) (= (type |#$T1@@8|) TyType)) (= (type |#$R@@37|) TyType)) (= (type bx@@48) BoxType)) ($IsBox bx@@48 (Tclass._System.___hPartialFunc2 |#$T0@@24| |#$T1@@8| |#$R@@37|))) (and (= ($Box ($Unbox HandleTypeType bx@@48)) bx@@48) ($Is ($Unbox HandleTypeType bx@@48) (Tclass._System.___hPartialFunc2 |#$T0@@24| |#$T1@@8| |#$R@@37|))))
 :qid |unknown.0:0|
 :skolemid |841|
 :pattern ( ($IsBox bx@@48 (Tclass._System.___hPartialFunc2 |#$T0@@24| |#$T1@@8| |#$R@@37|)))
)))
(assert (forall ((|#$T0@@25| T@U) (|#$T1@@9| T@U) (|#$R@@38| T@U) (|f#0@@7| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@25|) TyType) (= (type |#$T1@@9|) TyType)) (= (type |#$R@@38|) TyType)) (= (type |f#0@@7|) HandleTypeType)) (= ($Is |f#0@@7| (Tclass._System.___hPartialFunc2 |#$T0@@25| |#$T1@@9| |#$R@@38|))  (and ($Is |f#0@@7| (Tclass._System.___hFunc2 |#$T0@@25| |#$T1@@9| |#$R@@38|)) (forall ((|x0#0@@1| T@U) (|x1#0| T@U) ) (!  (=> (and (and (= (type |x0#0@@1|) BoxType) (= (type |x1#0|) BoxType)) (and ($IsBox |x0#0@@1| |#$T0@@25|) ($IsBox |x1#0| |#$T1@@9|))) (|Set#Equal| (Reads2 |#$T0@@25| |#$T1@@9| |#$R@@38| $OneHeap |f#0@@7| |x0#0@@1| |x1#0|) (|Set#Empty| BoxType)))
 :qid |unknown.0:0|
 :skolemid |842|
 :no-pattern (type |x0#0@@1|)
 :no-pattern (type |x1#0|)
 :no-pattern (U_2_int |x0#0@@1|)
 :no-pattern (U_2_bool |x0#0@@1|)
 :no-pattern (U_2_int |x1#0|)
 :no-pattern (U_2_bool |x1#0|)
)))))
 :qid |unknown.0:0|
 :skolemid |843|
 :pattern ( ($Is |f#0@@7| (Tclass._System.___hPartialFunc2 |#$T0@@25| |#$T1@@9| |#$R@@38|)))
)))
(assert (forall ((|#$T0@@26| T@U) (|#$T1@@10| T@U) (|#$R@@39| T@U) (|f#0@@8| T@U) ($h@@12 T@U) ) (!  (=> (and (and (and (and (= (type |#$T0@@26|) TyType) (= (type |#$T1@@10|) TyType)) (= (type |#$R@@39|) TyType)) (= (type |f#0@@8|) HandleTypeType)) (= (type $h@@12) (MapType0Type refType MapType1Type))) (= ($IsAlloc |f#0@@8| (Tclass._System.___hPartialFunc2 |#$T0@@26| |#$T1@@10| |#$R@@39|) $h@@12) ($IsAlloc |f#0@@8| (Tclass._System.___hFunc2 |#$T0@@26| |#$T1@@10| |#$R@@39|) $h@@12)))
 :qid |unknown.0:0|
 :skolemid |844|
 :pattern ( ($IsAlloc |f#0@@8| (Tclass._System.___hPartialFunc2 |#$T0@@26| |#$T1@@10| |#$R@@39|) $h@@12))
)))
(assert (forall ((arg0@@163 T@U) (arg1@@79 T@U) (arg2@@31 T@U) ) (! (= (type (Tclass._System.___hTotalFunc2 arg0@@163 arg1@@79 arg2@@31)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc2|
 :pattern ( (Tclass._System.___hTotalFunc2 arg0@@163 arg1@@79 arg2@@31))
)))
(assert (forall ((|#$T0@@27| T@U) (|#$T1@@11| T@U) (|#$R@@40| T@U) ) (!  (=> (and (and (= (type |#$T0@@27|) TyType) (= (type |#$T1@@11|) TyType)) (= (type |#$R@@40|) TyType)) (and (= (Tag (Tclass._System.___hTotalFunc2 |#$T0@@27| |#$T1@@11| |#$R@@40|)) Tagclass._System.___hTotalFunc2) (= (TagFamily (Tclass._System.___hTotalFunc2 |#$T0@@27| |#$T1@@11| |#$R@@40|)) |tytagFamily$_#TotalFunc2|)))
 :qid |unknown.0:0|
 :skolemid |845|
 :pattern ( (Tclass._System.___hTotalFunc2 |#$T0@@27| |#$T1@@11| |#$R@@40|))
)))
(assert (forall ((arg0@@164 T@U) ) (! (= (type (Tclass._System.___hTotalFunc2_0 arg0@@164)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc2_0|
 :pattern ( (Tclass._System.___hTotalFunc2_0 arg0@@164))
)))
(assert (forall ((|#$T0@@28| T@U) (|#$T1@@12| T@U) (|#$R@@41| T@U) ) (!  (=> (and (and (= (type |#$T0@@28|) TyType) (= (type |#$T1@@12|) TyType)) (= (type |#$R@@41|) TyType)) (= (Tclass._System.___hTotalFunc2_0 (Tclass._System.___hTotalFunc2 |#$T0@@28| |#$T1@@12| |#$R@@41|)) |#$T0@@28|))
 :qid |unknown.0:0|
 :skolemid |846|
 :pattern ( (Tclass._System.___hTotalFunc2 |#$T0@@28| |#$T1@@12| |#$R@@41|))
)))
(assert (forall ((arg0@@165 T@U) ) (! (= (type (Tclass._System.___hTotalFunc2_1 arg0@@165)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc2_1|
 :pattern ( (Tclass._System.___hTotalFunc2_1 arg0@@165))
)))
(assert (forall ((|#$T0@@29| T@U) (|#$T1@@13| T@U) (|#$R@@42| T@U) ) (!  (=> (and (and (= (type |#$T0@@29|) TyType) (= (type |#$T1@@13|) TyType)) (= (type |#$R@@42|) TyType)) (= (Tclass._System.___hTotalFunc2_1 (Tclass._System.___hTotalFunc2 |#$T0@@29| |#$T1@@13| |#$R@@42|)) |#$T1@@13|))
 :qid |unknown.0:0|
 :skolemid |847|
 :pattern ( (Tclass._System.___hTotalFunc2 |#$T0@@29| |#$T1@@13| |#$R@@42|))
)))
(assert (forall ((arg0@@166 T@U) ) (! (= (type (Tclass._System.___hTotalFunc2_2 arg0@@166)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc2_2|
 :pattern ( (Tclass._System.___hTotalFunc2_2 arg0@@166))
)))
(assert (forall ((|#$T0@@30| T@U) (|#$T1@@14| T@U) (|#$R@@43| T@U) ) (!  (=> (and (and (= (type |#$T0@@30|) TyType) (= (type |#$T1@@14|) TyType)) (= (type |#$R@@43|) TyType)) (= (Tclass._System.___hTotalFunc2_2 (Tclass._System.___hTotalFunc2 |#$T0@@30| |#$T1@@14| |#$R@@43|)) |#$R@@43|))
 :qid |unknown.0:0|
 :skolemid |848|
 :pattern ( (Tclass._System.___hTotalFunc2 |#$T0@@30| |#$T1@@14| |#$R@@43|))
)))
(assert (forall ((|#$T0@@31| T@U) (|#$T1@@15| T@U) (|#$R@@44| T@U) (bx@@49 T@U) ) (!  (=> (and (and (and (and (= (type |#$T0@@31|) TyType) (= (type |#$T1@@15|) TyType)) (= (type |#$R@@44|) TyType)) (= (type bx@@49) BoxType)) ($IsBox bx@@49 (Tclass._System.___hTotalFunc2 |#$T0@@31| |#$T1@@15| |#$R@@44|))) (and (= ($Box ($Unbox HandleTypeType bx@@49)) bx@@49) ($Is ($Unbox HandleTypeType bx@@49) (Tclass._System.___hTotalFunc2 |#$T0@@31| |#$T1@@15| |#$R@@44|))))
 :qid |unknown.0:0|
 :skolemid |849|
 :pattern ( ($IsBox bx@@49 (Tclass._System.___hTotalFunc2 |#$T0@@31| |#$T1@@15| |#$R@@44|)))
)))
(assert (forall ((|#$T0@@32| T@U) (|#$T1@@16| T@U) (|#$R@@45| T@U) (|f#0@@9| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@32|) TyType) (= (type |#$T1@@16|) TyType)) (= (type |#$R@@45|) TyType)) (= (type |f#0@@9|) HandleTypeType)) (= ($Is |f#0@@9| (Tclass._System.___hTotalFunc2 |#$T0@@32| |#$T1@@16| |#$R@@45|))  (and ($Is |f#0@@9| (Tclass._System.___hPartialFunc2 |#$T0@@32| |#$T1@@16| |#$R@@45|)) (forall ((|x0#0@@2| T@U) (|x1#0@@0| T@U) ) (!  (=> (and (and (= (type |x0#0@@2|) BoxType) (= (type |x1#0@@0|) BoxType)) (and ($IsBox |x0#0@@2| |#$T0@@32|) ($IsBox |x1#0@@0| |#$T1@@16|))) (Requires2 |#$T0@@32| |#$T1@@16| |#$R@@45| $OneHeap |f#0@@9| |x0#0@@2| |x1#0@@0|))
 :qid |unknown.0:0|
 :skolemid |850|
 :no-pattern (type |x0#0@@2|)
 :no-pattern (type |x1#0@@0|)
 :no-pattern (U_2_int |x0#0@@2|)
 :no-pattern (U_2_bool |x0#0@@2|)
 :no-pattern (U_2_int |x1#0@@0|)
 :no-pattern (U_2_bool |x1#0@@0|)
)))))
 :qid |unknown.0:0|
 :skolemid |851|
 :pattern ( ($Is |f#0@@9| (Tclass._System.___hTotalFunc2 |#$T0@@32| |#$T1@@16| |#$R@@45|)))
)))
(assert (forall ((|#$T0@@33| T@U) (|#$T1@@17| T@U) (|#$R@@46| T@U) (|f#0@@10| T@U) ($h@@13 T@U) ) (!  (=> (and (and (and (and (= (type |#$T0@@33|) TyType) (= (type |#$T1@@17|) TyType)) (= (type |#$R@@46|) TyType)) (= (type |f#0@@10|) HandleTypeType)) (= (type $h@@13) (MapType0Type refType MapType1Type))) (= ($IsAlloc |f#0@@10| (Tclass._System.___hTotalFunc2 |#$T0@@33| |#$T1@@17| |#$R@@46|) $h@@13) ($IsAlloc |f#0@@10| (Tclass._System.___hPartialFunc2 |#$T0@@33| |#$T1@@17| |#$R@@46|) $h@@13)))
 :qid |unknown.0:0|
 :skolemid |852|
 :pattern ( ($IsAlloc |f#0@@10| (Tclass._System.___hTotalFunc2 |#$T0@@33| |#$T1@@17| |#$R@@46|) $h@@13))
)))
(assert (forall ((arg0@@167 T@U) ) (! (= (type (DatatypeCtorId arg0@@167)) DtCtorIdType)
 :qid |funType:DatatypeCtorId|
 :pattern ( (DatatypeCtorId arg0@@167))
)))
(assert (forall ((|a#0#0#0| T@U) (|a#0#1#0| T@U) ) (!  (=> (and (= (type |a#0#0#0|) BoxType) (= (type |a#0#1#0|) BoxType)) (= (DatatypeCtorId (|#_System._tuple#2._#Make2| |a#0#0#0| |a#0#1#0|)) |##_System._tuple#2._#Make2|))
 :qid |unknown.0:0|
 :skolemid |853|
 :pattern ( (|#_System._tuple#2._#Make2| |a#0#0#0| |a#0#1#0|))
)))
(assert (forall ((d@@0 T@U) ) (!  (=> (= (type d@@0) DatatypeTypeType) (= (_System.Tuple2.___hMake2_q d@@0) (= (DatatypeCtorId d@@0) |##_System._tuple#2._#Make2|)))
 :qid |unknown.0:0|
 :skolemid |854|
 :pattern ( (_System.Tuple2.___hMake2_q d@@0))
)))
(assert (forall ((d@@1 T@U) ) (!  (=> (and (= (type d@@1) DatatypeTypeType) (_System.Tuple2.___hMake2_q d@@1)) (exists ((|a#1#0#0| T@U) (|a#1#1#0| T@U) ) (!  (and (and (= (type |a#1#0#0|) BoxType) (= (type |a#1#1#0|) BoxType)) (= d@@1 (|#_System._tuple#2._#Make2| |a#1#0#0| |a#1#1#0|)))
 :qid |unknown.0:0|
 :skolemid |855|
 :no-pattern (type |a#1#0#0|)
 :no-pattern (type |a#1#1#0|)
 :no-pattern (U_2_int |a#1#0#0|)
 :no-pattern (U_2_bool |a#1#0#0|)
 :no-pattern (U_2_int |a#1#1#0|)
 :no-pattern (U_2_bool |a#1#1#0|)
)))
 :qid |unknown.0:0|
 :skolemid |856|
 :pattern ( (_System.Tuple2.___hMake2_q d@@1))
)))
(assert (forall ((|_System._tuple#2$T0| T@U) (|_System._tuple#2$T1| T@U) ) (!  (=> (and (= (type |_System._tuple#2$T0|) TyType) (= (type |_System._tuple#2$T1|) TyType)) (and (= (Tag (Tclass._System.Tuple2 |_System._tuple#2$T0| |_System._tuple#2$T1|)) Tagclass._System.Tuple2) (= (TagFamily (Tclass._System.Tuple2 |_System._tuple#2$T0| |_System._tuple#2$T1|)) |tytagFamily$_tuple#2|)))
 :qid |unknown.0:0|
 :skolemid |857|
 :pattern ( (Tclass._System.Tuple2 |_System._tuple#2$T0| |_System._tuple#2$T1|))
)))
(assert (forall ((arg0@@168 T@U) ) (! (= (type (Tclass._System.Tuple2_0 arg0@@168)) TyType)
 :qid |funType:Tclass._System.Tuple2_0|
 :pattern ( (Tclass._System.Tuple2_0 arg0@@168))
)))
(assert (forall ((|_System._tuple#2$T0@@0| T@U) (|_System._tuple#2$T1@@0| T@U) ) (!  (=> (and (= (type |_System._tuple#2$T0@@0|) TyType) (= (type |_System._tuple#2$T1@@0|) TyType)) (= (Tclass._System.Tuple2_0 (Tclass._System.Tuple2 |_System._tuple#2$T0@@0| |_System._tuple#2$T1@@0|)) |_System._tuple#2$T0@@0|))
 :qid |unknown.0:0|
 :skolemid |858|
 :pattern ( (Tclass._System.Tuple2 |_System._tuple#2$T0@@0| |_System._tuple#2$T1@@0|))
)))
(assert (forall ((arg0@@169 T@U) ) (! (= (type (Tclass._System.Tuple2_1 arg0@@169)) TyType)
 :qid |funType:Tclass._System.Tuple2_1|
 :pattern ( (Tclass._System.Tuple2_1 arg0@@169))
)))
(assert (forall ((|_System._tuple#2$T0@@1| T@U) (|_System._tuple#2$T1@@1| T@U) ) (!  (=> (and (= (type |_System._tuple#2$T0@@1|) TyType) (= (type |_System._tuple#2$T1@@1|) TyType)) (= (Tclass._System.Tuple2_1 (Tclass._System.Tuple2 |_System._tuple#2$T0@@1| |_System._tuple#2$T1@@1|)) |_System._tuple#2$T1@@1|))
 :qid |unknown.0:0|
 :skolemid |859|
 :pattern ( (Tclass._System.Tuple2 |_System._tuple#2$T0@@1| |_System._tuple#2$T1@@1|))
)))
(assert (forall ((|_System._tuple#2$T0@@2| T@U) (|_System._tuple#2$T1@@2| T@U) (bx@@50 T@U) ) (!  (=> (and (and (and (= (type |_System._tuple#2$T0@@2|) TyType) (= (type |_System._tuple#2$T1@@2|) TyType)) (= (type bx@@50) BoxType)) ($IsBox bx@@50 (Tclass._System.Tuple2 |_System._tuple#2$T0@@2| |_System._tuple#2$T1@@2|))) (and (= ($Box ($Unbox DatatypeTypeType bx@@50)) bx@@50) ($Is ($Unbox DatatypeTypeType bx@@50) (Tclass._System.Tuple2 |_System._tuple#2$T0@@2| |_System._tuple#2$T1@@2|))))
 :qid |unknown.0:0|
 :skolemid |860|
 :pattern ( ($IsBox bx@@50 (Tclass._System.Tuple2 |_System._tuple#2$T0@@2| |_System._tuple#2$T1@@2|)))
)))
(assert (forall ((|_System._tuple#2$T0@@3| T@U) (|_System._tuple#2$T1@@3| T@U) (|a#2#0#0| T@U) (|a#2#1#0| T@U) ) (!  (=> (and (and (and (= (type |_System._tuple#2$T0@@3|) TyType) (= (type |_System._tuple#2$T1@@3|) TyType)) (= (type |a#2#0#0|) BoxType)) (= (type |a#2#1#0|) BoxType)) (= ($Is (|#_System._tuple#2._#Make2| |a#2#0#0| |a#2#1#0|) (Tclass._System.Tuple2 |_System._tuple#2$T0@@3| |_System._tuple#2$T1@@3|))  (and ($IsBox |a#2#0#0| |_System._tuple#2$T0@@3|) ($IsBox |a#2#1#0| |_System._tuple#2$T1@@3|))))
 :qid |unknown.0:0|
 :skolemid |861|
 :pattern ( ($Is (|#_System._tuple#2._#Make2| |a#2#0#0| |a#2#1#0|) (Tclass._System.Tuple2 |_System._tuple#2$T0@@3| |_System._tuple#2$T1@@3|)))
)))
(assert (forall ((|_System._tuple#2$T0@@4| T@U) (|_System._tuple#2$T1@@4| T@U) (|a#3#0#0| T@U) (|a#3#1#0| T@U) ($h@@14 T@U) ) (!  (=> (and (and (and (and (and (= (type |_System._tuple#2$T0@@4|) TyType) (= (type |_System._tuple#2$T1@@4|) TyType)) (= (type |a#3#0#0|) BoxType)) (= (type |a#3#1#0|) BoxType)) (= (type $h@@14) (MapType0Type refType MapType1Type))) ($IsGoodHeap $h@@14)) (= ($IsAlloc (|#_System._tuple#2._#Make2| |a#3#0#0| |a#3#1#0|) (Tclass._System.Tuple2 |_System._tuple#2$T0@@4| |_System._tuple#2$T1@@4|) $h@@14)  (and ($IsAllocBox |a#3#0#0| |_System._tuple#2$T0@@4| $h@@14) ($IsAllocBox |a#3#1#0| |_System._tuple#2$T1@@4| $h@@14))))
 :qid |unknown.0:0|
 :skolemid |862|
 :pattern ( ($IsAlloc (|#_System._tuple#2._#Make2| |a#3#0#0| |a#3#1#0|) (Tclass._System.Tuple2 |_System._tuple#2$T0@@4| |_System._tuple#2$T1@@4|) $h@@14))
)))
(assert (forall ((d@@2 T@U) (|_System._tuple#2$T0@@5| T@U) ($h@@15 T@U) ) (!  (=> (and (and (and (= (type d@@2) DatatypeTypeType) (= (type |_System._tuple#2$T0@@5|) TyType)) (= (type $h@@15) (MapType0Type refType MapType1Type))) (and ($IsGoodHeap $h@@15) (and (_System.Tuple2.___hMake2_q d@@2) (exists ((|_System._tuple#2$T1@@5| T@U) ) (!  (and (= (type |_System._tuple#2$T1@@5|) TyType) ($IsAlloc d@@2 (Tclass._System.Tuple2 |_System._tuple#2$T0@@5| |_System._tuple#2$T1@@5|) $h@@15))
 :qid |unknown.0:0|
 :skolemid |863|
 :pattern ( ($IsAlloc d@@2 (Tclass._System.Tuple2 |_System._tuple#2$T0@@5| |_System._tuple#2$T1@@5|) $h@@15))
))))) ($IsAllocBox (_System.Tuple2._0 d@@2) |_System._tuple#2$T0@@5| $h@@15))
 :qid |unknown.0:0|
 :skolemid |864|
 :pattern ( ($IsAllocBox (_System.Tuple2._0 d@@2) |_System._tuple#2$T0@@5| $h@@15))
)))
(assert (forall ((d@@3 T@U) (|_System._tuple#2$T1@@6| T@U) ($h@@16 T@U) ) (!  (=> (and (and (and (= (type d@@3) DatatypeTypeType) (= (type |_System._tuple#2$T1@@6|) TyType)) (= (type $h@@16) (MapType0Type refType MapType1Type))) (and ($IsGoodHeap $h@@16) (and (_System.Tuple2.___hMake2_q d@@3) (exists ((|_System._tuple#2$T0@@6| T@U) ) (!  (and (= (type |_System._tuple#2$T0@@6|) TyType) ($IsAlloc d@@3 (Tclass._System.Tuple2 |_System._tuple#2$T0@@6| |_System._tuple#2$T1@@6|) $h@@16))
 :qid |unknown.0:0|
 :skolemid |865|
 :pattern ( ($IsAlloc d@@3 (Tclass._System.Tuple2 |_System._tuple#2$T0@@6| |_System._tuple#2$T1@@6|) $h@@16))
))))) ($IsAllocBox (_System.Tuple2._1 d@@3) |_System._tuple#2$T1@@6| $h@@16))
 :qid |unknown.0:0|
 :skolemid |866|
 :pattern ( ($IsAllocBox (_System.Tuple2._1 d@@3) |_System._tuple#2$T1@@6| $h@@16))
)))
(assert (forall ((|a#4#0#0| T@U) (|a#4#1#0| T@U) ) (!  (=> (and (= (type |a#4#0#0|) BoxType) (= (type |a#4#1#0|) BoxType)) (= (|#_System._tuple#2._#Make2| (Lit |a#4#0#0|) (Lit |a#4#1#0|)) (Lit (|#_System._tuple#2._#Make2| |a#4#0#0| |a#4#1#0|))))
 :qid |unknown.0:0|
 :skolemid |867|
 :pattern ( (|#_System._tuple#2._#Make2| (Lit |a#4#0#0|) (Lit |a#4#1#0|)))
)))
(assert (forall ((|a#5#0#0| T@U) (|a#5#1#0| T@U) ) (!  (=> (and (= (type |a#5#0#0|) BoxType) (= (type |a#5#1#0|) BoxType)) (= (_System.Tuple2._0 (|#_System._tuple#2._#Make2| |a#5#0#0| |a#5#1#0|)) |a#5#0#0|))
 :qid |unknown.0:0|
 :skolemid |868|
 :pattern ( (|#_System._tuple#2._#Make2| |a#5#0#0| |a#5#1#0|))
)))
(assert (forall ((|a#6#0#0| T@U) (|a#6#1#0| T@U) ) (!  (=> (and (= (type |a#6#0#0|) BoxType) (= (type |a#6#1#0|) BoxType)) (< (BoxRank |a#6#0#0|) (DtRank (|#_System._tuple#2._#Make2| |a#6#0#0| |a#6#1#0|))))
 :qid |unknown.0:0|
 :skolemid |869|
 :pattern ( (|#_System._tuple#2._#Make2| |a#6#0#0| |a#6#1#0|))
)))
(assert (forall ((|a#7#0#0| T@U) (|a#7#1#0| T@U) ) (!  (=> (and (= (type |a#7#0#0|) BoxType) (= (type |a#7#1#0|) BoxType)) (= (_System.Tuple2._1 (|#_System._tuple#2._#Make2| |a#7#0#0| |a#7#1#0|)) |a#7#1#0|))
 :qid |unknown.0:0|
 :skolemid |870|
 :pattern ( (|#_System._tuple#2._#Make2| |a#7#0#0| |a#7#1#0|))
)))
(assert (forall ((|a#8#0#0| T@U) (|a#8#1#0| T@U) ) (!  (=> (and (= (type |a#8#0#0|) BoxType) (= (type |a#8#1#0|) BoxType)) (< (BoxRank |a#8#1#0|) (DtRank (|#_System._tuple#2._#Make2| |a#8#0#0| |a#8#1#0|))))
 :qid |unknown.0:0|
 :skolemid |871|
 :pattern ( (|#_System._tuple#2._#Make2| |a#8#0#0| |a#8#1#0|))
)))
(assert (forall ((d@@4 T@U) ) (!  (=> (and (= (type d@@4) DatatypeTypeType) (|$IsA#_System.Tuple2| d@@4)) (_System.Tuple2.___hMake2_q d@@4))
 :qid |unknown.0:0|
 :skolemid |872|
 :pattern ( (|$IsA#_System.Tuple2| d@@4))
)))
(assert (forall ((|_System._tuple#2$T0@@7| T@U) (|_System._tuple#2$T1@@7| T@U) (d@@5 T@U) ) (!  (=> (and (and (and (= (type |_System._tuple#2$T0@@7|) TyType) (= (type |_System._tuple#2$T1@@7|) TyType)) (= (type d@@5) DatatypeTypeType)) ($Is d@@5 (Tclass._System.Tuple2 |_System._tuple#2$T0@@7| |_System._tuple#2$T1@@7|))) (_System.Tuple2.___hMake2_q d@@5))
 :qid |unknown.0:0|
 :skolemid |873|
 :pattern ( (_System.Tuple2.___hMake2_q d@@5) ($Is d@@5 (Tclass._System.Tuple2 |_System._tuple#2$T0@@7| |_System._tuple#2$T1@@7|)))
)))
(assert (forall ((a@@100 T@U) (b@@61 T@U) ) (!  (=> (and (and (= (type a@@100) DatatypeTypeType) (= (type b@@61) DatatypeTypeType)) true) (= (|_System.Tuple2#Equal| a@@100 b@@61)  (and (= (_System.Tuple2._0 a@@100) (_System.Tuple2._0 b@@61)) (= (_System.Tuple2._1 a@@100) (_System.Tuple2._1 b@@61)))))
 :qid |unknown.0:0|
 :skolemid |874|
 :pattern ( (|_System.Tuple2#Equal| a@@100 b@@61))
)))
(assert (forall ((a@@101 T@U) (b@@62 T@U) ) (!  (=> (and (= (type a@@101) DatatypeTypeType) (= (type b@@62) DatatypeTypeType)) (= (|_System.Tuple2#Equal| a@@101 b@@62) (= a@@101 b@@62)))
 :qid |unknown.0:0|
 :skolemid |875|
 :pattern ( (|_System.Tuple2#Equal| a@@101 b@@62))
)))
(assert (= (type |#_System._tuple#0._#Make0|) DatatypeTypeType))
(assert (= (DatatypeCtorId |#_System._tuple#0._#Make0|) |##_System._tuple#0._#Make0|))
(assert (forall ((d@@6 T@U) ) (!  (=> (= (type d@@6) DatatypeTypeType) (= (_System.Tuple0.___hMake0_q d@@6) (= (DatatypeCtorId d@@6) |##_System._tuple#0._#Make0|)))
 :qid |unknown.0:0|
 :skolemid |876|
 :pattern ( (_System.Tuple0.___hMake0_q d@@6))
)))
(assert (forall ((d@@7 T@U) ) (!  (=> (and (= (type d@@7) DatatypeTypeType) (_System.Tuple0.___hMake0_q d@@7)) (= d@@7 |#_System._tuple#0._#Make0|))
 :qid |unknown.0:0|
 :skolemid |877|
 :pattern ( (_System.Tuple0.___hMake0_q d@@7))
)))
(assert (= (type Tclass._System.Tuple0) TyType))
(assert (= (Tag Tclass._System.Tuple0) Tagclass._System.Tuple0))
(assert (= (TagFamily Tclass._System.Tuple0) |tytagFamily$_tuple#0|))
(assert (forall ((bx@@51 T@U) ) (!  (=> (and (= (type bx@@51) BoxType) ($IsBox bx@@51 Tclass._System.Tuple0)) (and (= ($Box ($Unbox DatatypeTypeType bx@@51)) bx@@51) ($Is ($Unbox DatatypeTypeType bx@@51) Tclass._System.Tuple0)))
 :qid |unknown.0:0|
 :skolemid |878|
 :pattern ( ($IsBox bx@@51 Tclass._System.Tuple0))
)))
(assert ($Is |#_System._tuple#0._#Make0| Tclass._System.Tuple0))
(assert (forall (($h@@17 T@U) ) (!  (=> (and (= (type $h@@17) (MapType0Type refType MapType1Type)) ($IsGoodHeap $h@@17)) ($IsAlloc |#_System._tuple#0._#Make0| Tclass._System.Tuple0 $h@@17))
 :qid |DafnyPreludebpl.545:12|
 :skolemid |879|
 :pattern ( ($IsAlloc |#_System._tuple#0._#Make0| Tclass._System.Tuple0 $h@@17))
)))
(assert (= |#_System._tuple#0._#Make0| (Lit |#_System._tuple#0._#Make0|)))
(assert (forall ((d@@8 T@U) ) (!  (=> (and (= (type d@@8) DatatypeTypeType) (|$IsA#_System.Tuple0| d@@8)) (_System.Tuple0.___hMake0_q d@@8))
 :qid |unknown.0:0|
 :skolemid |880|
 :pattern ( (|$IsA#_System.Tuple0| d@@8))
)))
(assert (forall ((d@@9 T@U) ) (!  (=> (and (= (type d@@9) DatatypeTypeType) ($Is d@@9 Tclass._System.Tuple0)) (_System.Tuple0.___hMake0_q d@@9))
 :qid |unknown.0:0|
 :skolemid |881|
 :pattern ( (_System.Tuple0.___hMake0_q d@@9) ($Is d@@9 Tclass._System.Tuple0))
)))
(assert (forall ((a@@102 T@U) (b@@63 T@U) ) (!  (=> (and (and (= (type a@@102) DatatypeTypeType) (= (type b@@63) DatatypeTypeType)) true) (= (|_System.Tuple0#Equal| a@@102 b@@63) true))
 :qid |unknown.0:0|
 :skolemid |882|
 :pattern ( (|_System.Tuple0#Equal| a@@102 b@@63))
)))
(assert (forall ((a@@103 T@U) (b@@64 T@U) ) (!  (=> (and (= (type a@@103) DatatypeTypeType) (= (type b@@64) DatatypeTypeType)) (= (|_System.Tuple0#Equal| a@@103 b@@64) (= a@@103 b@@64)))
 :qid |unknown.0:0|
 :skolemid |883|
 :pattern ( (|_System.Tuple0#Equal| a@@103 b@@64))
)))
(assert (forall ((arg0@@170 T@U) ) (! (= (type (|#Test.ChildMap.ChildMap| arg0@@170)) DatatypeTypeType)
 :qid |funType:#Test.ChildMap.ChildMap|
 :pattern ( (|#Test.ChildMap.ChildMap| arg0@@170))
)))
(assert (forall ((|a#14#0#0| T@U) ) (!  (=> (= (type |a#14#0#0|) (IMapType BoxType BoxType)) (= (DatatypeCtorId (|#Test.ChildMap.ChildMap| |a#14#0#0|)) |##Test.ChildMap.ChildMap|))
 :qid |Testidfy.6:30|
 :skolemid |884|
 :pattern ( (|#Test.ChildMap.ChildMap| |a#14#0#0|))
)))
(assert (forall ((d@@10 T@U) ) (!  (=> (= (type d@@10) DatatypeTypeType) (= (Test.ChildMap.ChildMap_q d@@10) (= (DatatypeCtorId d@@10) |##Test.ChildMap.ChildMap|)))
 :qid |unknown.0:0|
 :skolemid |885|
 :pattern ( (Test.ChildMap.ChildMap_q d@@10))
)))
(assert (forall ((d@@11 T@U) ) (!  (=> (and (= (type d@@11) DatatypeTypeType) (Test.ChildMap.ChildMap_q d@@11)) (exists ((|a#15#0#0| T@U) ) (!  (and (= (type |a#15#0#0|) (IMapType BoxType BoxType)) (= d@@11 (|#Test.ChildMap.ChildMap| |a#15#0#0|)))
 :qid |Testidfy.6:30|
 :skolemid |886|
 :no-pattern (type |a#15#0#0|)
 :no-pattern (U_2_int |a#15#0#0|)
 :no-pattern (U_2_bool |a#15#0#0|)
)))
 :qid |unknown.0:0|
 :skolemid |887|
 :pattern ( (Test.ChildMap.ChildMap_q d@@11))
)))
(assert (= (type Tclass.Common.Key) TyType))
(assert (= (Tag Tclass.Common.Key) Tagclass.Common.Key))
(assert (= (TagFamily Tclass.Common.Key) tytagFamily$Key))
(assert (forall ((bx@@52 T@U) ) (!  (=> (and (= (type bx@@52) BoxType) ($IsBox bx@@52 Tclass.Common.Key)) (and (= ($Box ($Unbox (SeqType BoxType) bx@@52)) bx@@52) ($Is ($Unbox (SeqType BoxType) bx@@52) Tclass.Common.Key)))
 :qid |unknown.0:0|
 :skolemid |888|
 :pattern ( ($IsBox bx@@52 Tclass.Common.Key))
)))
(assert (= (type Tclass.Test.BetreeNode) TyType))
(assert (= (Tag Tclass.Test.BetreeNode) Tagclass.Test.BetreeNode))
(assert (= (TagFamily Tclass.Test.BetreeNode) tytagFamily$BetreeNode))
(assert (forall ((bx@@53 T@U) ) (!  (=> (and (= (type bx@@53) BoxType) ($IsBox bx@@53 Tclass.Test.BetreeNode)) (and (= ($Box ($Unbox DatatypeTypeType bx@@53)) bx@@53) ($Is ($Unbox DatatypeTypeType bx@@53) Tclass.Test.BetreeNode)))
 :qid |unknown.0:0|
 :skolemid |889|
 :pattern ( ($IsBox bx@@53 Tclass.Test.BetreeNode))
)))
(assert (= (type Tclass.Test.ChildMap) TyType))
(assert (= (Tag Tclass.Test.ChildMap) Tagclass.Test.ChildMap))
(assert (= (TagFamily Tclass.Test.ChildMap) tytagFamily$ChildMap))
(assert (forall ((bx@@54 T@U) ) (!  (=> (and (= (type bx@@54) BoxType) ($IsBox bx@@54 Tclass.Test.ChildMap)) (and (= ($Box ($Unbox DatatypeTypeType bx@@54)) bx@@54) ($Is ($Unbox DatatypeTypeType bx@@54) Tclass.Test.ChildMap)))
 :qid |unknown.0:0|
 :skolemid |890|
 :pattern ( ($IsBox bx@@54 Tclass.Test.ChildMap))
)))
(assert (forall ((|a#16#0#0| T@U) ) (!  (=> (= (type |a#16#0#0|) (IMapType BoxType BoxType)) (= ($Is (|#Test.ChildMap.ChildMap| |a#16#0#0|) Tclass.Test.ChildMap) ($Is |a#16#0#0| (TIMap Tclass.Common.Key Tclass.Test.BetreeNode))))
 :qid |Testidfy.6:30|
 :skolemid |891|
 :pattern ( ($Is (|#Test.ChildMap.ChildMap| |a#16#0#0|) Tclass.Test.ChildMap))
)))
(assert (forall ((|a#17#0#0| T@U) ($h@@18 T@U) ) (!  (=> (and (and (= (type |a#17#0#0|) (IMapType BoxType BoxType)) (= (type $h@@18) (MapType0Type refType MapType1Type))) ($IsGoodHeap $h@@18)) (= ($IsAlloc (|#Test.ChildMap.ChildMap| |a#17#0#0|) Tclass.Test.ChildMap $h@@18) ($IsAlloc |a#17#0#0| (TIMap Tclass.Common.Key Tclass.Test.BetreeNode) $h@@18)))
 :qid |Testidfy.6:30|
 :skolemid |892|
 :pattern ( ($IsAlloc (|#Test.ChildMap.ChildMap| |a#17#0#0|) Tclass.Test.ChildMap $h@@18))
)))
(assert (forall ((arg0@@171 T@U) ) (! (= (type (Test.ChildMap.mapp arg0@@171)) (IMapType BoxType BoxType))
 :qid |funType:Test.ChildMap.mapp|
 :pattern ( (Test.ChildMap.mapp arg0@@171))
)))
(assert (forall ((d@@12 T@U) ($h@@19 T@U) ) (!  (=> (and (and (= (type d@@12) DatatypeTypeType) (= (type $h@@19) (MapType0Type refType MapType1Type))) (and ($IsGoodHeap $h@@19) (and (Test.ChildMap.ChildMap_q d@@12) ($IsAlloc d@@12 Tclass.Test.ChildMap $h@@19)))) ($IsAlloc (Test.ChildMap.mapp d@@12) (TIMap Tclass.Common.Key Tclass.Test.BetreeNode) $h@@19))
 :qid |unknown.0:0|
 :skolemid |893|
 :pattern ( ($IsAlloc (Test.ChildMap.mapp d@@12) (TIMap Tclass.Common.Key Tclass.Test.BetreeNode) $h@@19))
)))
(assert (forall ((|a#18#0#0| T@U) ) (!  (=> (= (type |a#18#0#0|) (IMapType BoxType BoxType)) (= (|#Test.ChildMap.ChildMap| (Lit |a#18#0#0|)) (Lit (|#Test.ChildMap.ChildMap| |a#18#0#0|))))
 :qid |Testidfy.6:30|
 :skolemid |894|
 :pattern ( (|#Test.ChildMap.ChildMap| (Lit |a#18#0#0|)))
)))
(assert (forall ((|a#19#0#0| T@U) ) (!  (=> (= (type |a#19#0#0|) (IMapType BoxType BoxType)) (= (Test.ChildMap.mapp (|#Test.ChildMap.ChildMap| |a#19#0#0|)) |a#19#0#0|))
 :qid |Testidfy.6:30|
 :skolemid |895|
 :pattern ( (|#Test.ChildMap.ChildMap| |a#19#0#0|))
)))
(assert (forall ((|a#20#0#0| T@U) (d@@13 T@U) ) (!  (=> (and (and (= (type |a#20#0#0|) (IMapType BoxType BoxType)) (= (type d@@13) DatatypeTypeType)) (U_2_bool (MapType0Select (|IMap#Domain| |a#20#0#0|) ($Box d@@13)))) (< (DtRank d@@13) (DtRank (|#Test.ChildMap.ChildMap| |a#20#0#0|))))
 :qid |Testidfy.6:30|
 :skolemid |896|
 :pattern ( (MapType0Select (|IMap#Domain| |a#20#0#0|) ($Box d@@13)) (|#Test.ChildMap.ChildMap| |a#20#0#0|))
)))
(assert (forall ((|a#21#0#0| T@U) (bx@@55 T@U) ) (!  (=> (and (and (= (type |a#21#0#0|) (IMapType BoxType BoxType)) (= (type bx@@55) BoxType)) (U_2_bool (MapType0Select (|IMap#Domain| |a#21#0#0|) bx@@55))) (< (DtRank ($Unbox DatatypeTypeType (MapType0Select (|IMap#Elements| |a#21#0#0|) bx@@55))) (DtRank (|#Test.ChildMap.ChildMap| |a#21#0#0|))))
 :qid |Testidfy.6:30|
 :skolemid |897|
 :pattern ( (MapType0Select (|IMap#Domain| |a#21#0#0|) bx@@55) (|#Test.ChildMap.ChildMap| |a#21#0#0|))
)))
(assert (forall ((d@@14 T@U) ) (!  (=> (and (= (type d@@14) DatatypeTypeType) (|$IsA#Test.ChildMap| d@@14)) (Test.ChildMap.ChildMap_q d@@14))
 :qid |unknown.0:0|
 :skolemid |898|
 :pattern ( (|$IsA#Test.ChildMap| d@@14))
)))
(assert (forall ((d@@15 T@U) ) (!  (=> (and (= (type d@@15) DatatypeTypeType) ($Is d@@15 Tclass.Test.ChildMap)) (Test.ChildMap.ChildMap_q d@@15))
 :qid |unknown.0:0|
 :skolemid |899|
 :pattern ( (Test.ChildMap.ChildMap_q d@@15) ($Is d@@15 Tclass.Test.ChildMap))
)))
(assert (forall ((a@@104 T@U) (b@@65 T@U) ) (!  (=> (and (and (= (type a@@104) DatatypeTypeType) (= (type b@@65) DatatypeTypeType)) true) (= (|Test.ChildMap#Equal| a@@104 b@@65) (|IMap#Equal| (Test.ChildMap.mapp a@@104) (Test.ChildMap.mapp b@@65))))
 :qid |unknown.0:0|
 :skolemid |900|
 :pattern ( (|Test.ChildMap#Equal| a@@104 b@@65))
)))
(assert (forall ((a@@105 T@U) (b@@66 T@U) ) (!  (=> (and (= (type a@@105) DatatypeTypeType) (= (type b@@66) DatatypeTypeType)) (= (|Test.ChildMap#Equal| a@@105 b@@66) (= a@@105 b@@66)))
 :qid |unknown.0:0|
 :skolemid |901|
 :pattern ( (|Test.ChildMap#Equal| a@@105 b@@66))
)))
(assert (forall (($ly T@U) (this T@U) ) (!  (=> (and (= (type $ly) LayerTypeType) (= (type this) DatatypeTypeType)) (= (Test.ChildMap.WF ($LS $ly) this) (Test.ChildMap.WF $ly this)))
 :qid |Testidfy.7:15|
 :skolemid |902|
 :pattern ( (Test.ChildMap.WF ($LS $ly) this))
)))
(assert  (and (forall ((arg0@@172 T@U) ) (! (= (type (AsFuelBottom arg0@@172)) LayerTypeType)
 :qid |funType:AsFuelBottom|
 :pattern ( (AsFuelBottom arg0@@172))
)) (= (type $LZ) LayerTypeType)))
(assert (forall (($ly@@0 T@U) (this@@0 T@U) ) (!  (=> (and (= (type $ly@@0) LayerTypeType) (= (type this@@0) DatatypeTypeType)) (= (Test.ChildMap.WF $ly@@0 this@@0) (Test.ChildMap.WF $LZ this@@0)))
 :qid |Testidfy.7:15|
 :skolemid |903|
 :pattern ( (Test.ChildMap.WF (AsFuelBottom $ly@@0) this@@0))
)))
(assert  (=> (<= 5 $FunctionContextHeight) (forall (($ly@@1 T@U) (this@@1 T@U) ) (!  (=> (and (and (= (type $ly@@1) LayerTypeType) (= (type this@@1) DatatypeTypeType)) (or (|Test.ChildMap.WF#canCall| this@@1) (and (not (= 5 $FunctionContextHeight)) ($Is this@@1 Tclass.Test.ChildMap)))) true)
 :qid |Testidfy.7:15|
 :skolemid |904|
 :pattern ( (Test.ChildMap.WF $ly@@1 this@@1))
))))
(assert (forall (($ly@@2 T@U) (this@@2 T@U) ) (!  (=> (and (and (= (type $ly@@2) LayerTypeType) (= (type this@@2) DatatypeTypeType)) ($Is this@@2 Tclass.Test.ChildMap)) (= (|Test.ChildMap.WF#requires| $ly@@2 this@@2) true))
 :qid |Testidfy.7:15|
 :skolemid |905|
 :pattern ( (|Test.ChildMap.WF#requires| $ly@@2 this@@2))
)))
(assert  (=> (<= 5 $FunctionContextHeight) (forall (($ly@@3 T@U) (this@@3 T@U) ) (!  (=> (and (and (= (type $ly@@3) LayerTypeType) (= (type this@@3) DatatypeTypeType)) (or (|Test.ChildMap.WF#canCall| this@@3) (and (not (= 5 $FunctionContextHeight)) ($Is this@@3 Tclass.Test.ChildMap)))) (and (and (and (Test.ChildMap.ChildMap_q this@@3) (|Common.__default.TotalSet#canCall| (|IMap#Domain| (Test.ChildMap.mapp this@@3)))) (=> (Common.__default.TotalSet (|IMap#Domain| (Test.ChildMap.mapp this@@3))) (forall ((|k#0| T@U) ) (!  (=> (and (= (type |k#0|) (SeqType BoxType)) ($Is |k#0| Tclass.Common.Key)) (and (|Common.__default.AnyKey#canCall| |k#0|) (=> (Common.__default.AnyKey |k#0|) (and (Test.ChildMap.ChildMap_q this@@3) (|Test.BetreeNode.WF#canCall| ($Unbox DatatypeTypeType (MapType0Select (|IMap#Elements| (Test.ChildMap.mapp this@@3)) ($Box |k#0|))))))))
 :qid |Testidfy.9:20|
 :skolemid |907|
 :pattern ( ($Unbox DatatypeTypeType (MapType0Select (|IMap#Elements| (Test.ChildMap.mapp this@@3)) ($Box |k#0|))))
 :pattern ( (Common.__default.AnyKey |k#0|))
)))) (= (Test.ChildMap.WF ($LS $ly@@3) this@@3)  (and (Common.__default.TotalSet (|IMap#Domain| (Test.ChildMap.mapp this@@3))) (forall ((|k#0@@0| T@U) ) (!  (=> (= (type |k#0@@0|) (SeqType BoxType)) (=> (and ($Is |k#0@@0| Tclass.Common.Key) (Common.__default.AnyKey |k#0@@0|)) (Test.BetreeNode.WF $ly@@3 ($Unbox DatatypeTypeType (MapType0Select (|IMap#Elements| (Test.ChildMap.mapp this@@3)) ($Box |k#0@@0|))))))
 :qid |Testidfy.9:20|
 :skolemid |906|
 :pattern ( ($Unbox DatatypeTypeType (MapType0Select (|IMap#Elements| (Test.ChildMap.mapp this@@3)) ($Box |k#0@@0|))))
 :pattern ( (Common.__default.AnyKey |k#0@@0|))
))))))
 :qid |Testidfy.7:15|
 :skolemid |908|
 :pattern ( (Test.ChildMap.WF ($LS $ly@@3) this@@3))
))))
(assert  (=> (<= 5 $FunctionContextHeight) (forall (($ly@@4 T@U) (this@@4 T@U) ) (!  (=> (and (and (= (type $ly@@4) LayerTypeType) (= (type this@@4) DatatypeTypeType)) (or (|Test.ChildMap.WF#canCall| (Lit this@@4)) (and (not (= 5 $FunctionContextHeight)) ($Is this@@4 Tclass.Test.ChildMap)))) (and (and (and (Test.ChildMap.ChildMap_q (Lit this@@4)) (|Common.__default.TotalSet#canCall| (Lit (|IMap#Domain| (Lit (Test.ChildMap.mapp (Lit this@@4))))))) (=> (U_2_bool (Lit (bool_2_U (Common.__default.TotalSet (Lit (|IMap#Domain| (Lit (Test.ChildMap.mapp (Lit this@@4))))))))) (forall ((|k#1| T@U) ) (!  (=> (and (= (type |k#1|) (SeqType BoxType)) ($Is |k#1| Tclass.Common.Key)) (and (|Common.__default.AnyKey#canCall| |k#1|) (=> (Common.__default.AnyKey |k#1|) (and (Test.ChildMap.ChildMap_q (Lit this@@4)) (|Test.BetreeNode.WF#canCall| ($Unbox DatatypeTypeType (MapType0Select (|IMap#Elements| (Lit (Test.ChildMap.mapp (Lit this@@4)))) ($Box |k#1|))))))))
 :qid |Testidfy.9:20|
 :skolemid |910|
 :pattern ( ($Unbox DatatypeTypeType (MapType0Select (|IMap#Elements| (Test.ChildMap.mapp this@@4)) ($Box |k#1|))))
 :pattern ( (Common.__default.AnyKey |k#1|))
)))) (= (Test.ChildMap.WF ($LS $ly@@4) (Lit this@@4))  (and (Common.__default.TotalSet (Lit (|IMap#Domain| (Lit (Test.ChildMap.mapp (Lit this@@4)))))) (forall ((|k#1@@0| T@U) ) (!  (=> (= (type |k#1@@0|) (SeqType BoxType)) (=> (and ($Is |k#1@@0| Tclass.Common.Key) (Common.__default.AnyKey |k#1@@0|)) (Test.BetreeNode.WF ($LS $ly@@4) ($Unbox DatatypeTypeType (MapType0Select (|IMap#Elements| (Lit (Test.ChildMap.mapp (Lit this@@4)))) ($Box |k#1@@0|))))))
 :qid |Testidfy.9:20|
 :skolemid |909|
 :pattern ( ($Unbox DatatypeTypeType (MapType0Select (|IMap#Elements| (Test.ChildMap.mapp this@@4)) ($Box |k#1@@0|))))
 :pattern ( (Common.__default.AnyKey |k#1@@0|))
))))))
 :qid |Testidfy.7:15|
 :weight 3
 :skolemid |911|
 :pattern ( (Test.ChildMap.WF ($LS $ly@@4) (Lit this@@4)))
))))
(assert (= (type |#Test.BetreeNode.Nil|) DatatypeTypeType))
(assert (= (DatatypeCtorId |#Test.BetreeNode.Nil|) |##Test.BetreeNode.Nil|))
(assert (forall ((d@@16 T@U) ) (!  (=> (= (type d@@16) DatatypeTypeType) (= (Test.BetreeNode.Nil_q d@@16) (= (DatatypeCtorId d@@16) |##Test.BetreeNode.Nil|)))
 :qid |unknown.0:0|
 :skolemid |917|
 :pattern ( (Test.BetreeNode.Nil_q d@@16))
)))
(assert (forall ((d@@17 T@U) ) (!  (=> (and (= (type d@@17) DatatypeTypeType) (Test.BetreeNode.Nil_q d@@17)) (= d@@17 |#Test.BetreeNode.Nil|))
 :qid |unknown.0:0|
 :skolemid |918|
 :pattern ( (Test.BetreeNode.Nil_q d@@17))
)))
(assert ($Is |#Test.BetreeNode.Nil| Tclass.Test.BetreeNode))
(assert (forall (($h@@20 T@U) ) (!  (=> (and (= (type $h@@20) (MapType0Type refType MapType1Type)) ($IsGoodHeap $h@@20)) ($IsAlloc |#Test.BetreeNode.Nil| Tclass.Test.BetreeNode $h@@20))
 :qid |DafnyPreludebpl.545:12|
 :skolemid |919|
 :pattern ( ($IsAlloc |#Test.BetreeNode.Nil| Tclass.Test.BetreeNode $h@@20))
)))
(assert (= |#Test.BetreeNode.Nil| (Lit |#Test.BetreeNode.Nil|)))
(assert (forall ((arg0@@173 T@U) ) (! (= (type (|#Test.BetreeNode.BetreeNode| arg0@@173)) DatatypeTypeType)
 :qid |funType:#Test.BetreeNode.BetreeNode|
 :pattern ( (|#Test.BetreeNode.BetreeNode| arg0@@173))
)))
(assert (forall ((|a#5#0#0@@0| T@U) ) (!  (=> (= (type |a#5#0#0@@0|) DatatypeTypeType) (= (DatatypeCtorId (|#Test.BetreeNode.BetreeNode| |a#5#0#0@@0|)) |##Test.BetreeNode.BetreeNode|))
 :qid |Testidfy.13:40|
 :skolemid |920|
 :pattern ( (|#Test.BetreeNode.BetreeNode| |a#5#0#0@@0|))
)))
(assert (forall ((d@@18 T@U) ) (!  (=> (= (type d@@18) DatatypeTypeType) (= (Test.BetreeNode.BetreeNode_q d@@18) (= (DatatypeCtorId d@@18) |##Test.BetreeNode.BetreeNode|)))
 :qid |unknown.0:0|
 :skolemid |921|
 :pattern ( (Test.BetreeNode.BetreeNode_q d@@18))
)))
(assert (forall ((d@@19 T@U) ) (!  (=> (and (= (type d@@19) DatatypeTypeType) (Test.BetreeNode.BetreeNode_q d@@19)) (exists ((|a#6#0#0@@0| T@U) ) (!  (and (= (type |a#6#0#0@@0|) DatatypeTypeType) (= d@@19 (|#Test.BetreeNode.BetreeNode| |a#6#0#0@@0|)))
 :qid |Testidfy.13:40|
 :skolemid |922|
 :no-pattern (type |a#6#0#0@@0|)
 :no-pattern (U_2_int |a#6#0#0@@0|)
 :no-pattern (U_2_bool |a#6#0#0@@0|)
)))
 :qid |unknown.0:0|
 :skolemid |923|
 :pattern ( (Test.BetreeNode.BetreeNode_q d@@19))
)))
(assert (forall ((|a#7#0#0@@0| T@U) ) (!  (=> (= (type |a#7#0#0@@0|) DatatypeTypeType) (= ($Is (|#Test.BetreeNode.BetreeNode| |a#7#0#0@@0|) Tclass.Test.BetreeNode) ($Is |a#7#0#0@@0| Tclass.Test.ChildMap)))
 :qid |Testidfy.13:40|
 :skolemid |924|
 :pattern ( ($Is (|#Test.BetreeNode.BetreeNode| |a#7#0#0@@0|) Tclass.Test.BetreeNode))
)))
(assert (forall ((|a#8#0#0@@0| T@U) ($h@@21 T@U) ) (!  (=> (and (and (= (type |a#8#0#0@@0|) DatatypeTypeType) (= (type $h@@21) (MapType0Type refType MapType1Type))) ($IsGoodHeap $h@@21)) (= ($IsAlloc (|#Test.BetreeNode.BetreeNode| |a#8#0#0@@0|) Tclass.Test.BetreeNode $h@@21) ($IsAlloc |a#8#0#0@@0| Tclass.Test.ChildMap $h@@21)))
 :qid |Testidfy.13:40|
 :skolemid |925|
 :pattern ( ($IsAlloc (|#Test.BetreeNode.BetreeNode| |a#8#0#0@@0|) Tclass.Test.BetreeNode $h@@21))
)))
(assert (forall ((arg0@@174 T@U) ) (! (= (type (Test.BetreeNode.children arg0@@174)) DatatypeTypeType)
 :qid |funType:Test.BetreeNode.children|
 :pattern ( (Test.BetreeNode.children arg0@@174))
)))
(assert (forall ((d@@20 T@U) ($h@@22 T@U) ) (!  (=> (and (and (= (type d@@20) DatatypeTypeType) (= (type $h@@22) (MapType0Type refType MapType1Type))) (and ($IsGoodHeap $h@@22) (and (Test.BetreeNode.BetreeNode_q d@@20) ($IsAlloc d@@20 Tclass.Test.BetreeNode $h@@22)))) ($IsAlloc (Test.BetreeNode.children d@@20) Tclass.Test.ChildMap $h@@22))
 :qid |unknown.0:0|
 :skolemid |926|
 :pattern ( ($IsAlloc (Test.BetreeNode.children d@@20) Tclass.Test.ChildMap $h@@22))
)))
(assert (forall ((|a#9#0#0| T@U) ) (!  (=> (= (type |a#9#0#0|) DatatypeTypeType) (= (|#Test.BetreeNode.BetreeNode| (Lit |a#9#0#0|)) (Lit (|#Test.BetreeNode.BetreeNode| |a#9#0#0|))))
 :qid |Testidfy.13:40|
 :skolemid |927|
 :pattern ( (|#Test.BetreeNode.BetreeNode| (Lit |a#9#0#0|)))
)))
(assert (forall ((|a#10#0#0| T@U) ) (!  (=> (= (type |a#10#0#0|) DatatypeTypeType) (= (Test.BetreeNode.children (|#Test.BetreeNode.BetreeNode| |a#10#0#0|)) |a#10#0#0|))
 :qid |Testidfy.13:40|
 :skolemid |928|
 :pattern ( (|#Test.BetreeNode.BetreeNode| |a#10#0#0|))
)))
(assert (forall ((|a#11#0#0| T@U) ) (!  (=> (= (type |a#11#0#0|) DatatypeTypeType) (< (DtRank |a#11#0#0|) (DtRank (|#Test.BetreeNode.BetreeNode| |a#11#0#0|))))
 :qid |Testidfy.13:40|
 :skolemid |929|
 :pattern ( (|#Test.BetreeNode.BetreeNode| |a#11#0#0|))
)))
(assert (forall ((d@@21 T@U) ) (!  (=> (and (= (type d@@21) DatatypeTypeType) (|$IsA#Test.BetreeNode| d@@21)) (or (Test.BetreeNode.Nil_q d@@21) (Test.BetreeNode.BetreeNode_q d@@21)))
 :qid |unknown.0:0|
 :skolemid |930|
 :pattern ( (|$IsA#Test.BetreeNode| d@@21))
)))
(assert (forall ((d@@22 T@U) ) (!  (=> (and (= (type d@@22) DatatypeTypeType) ($Is d@@22 Tclass.Test.BetreeNode)) (or (Test.BetreeNode.Nil_q d@@22) (Test.BetreeNode.BetreeNode_q d@@22)))
 :qid |unknown.0:0|
 :skolemid |931|
 :pattern ( (Test.BetreeNode.BetreeNode_q d@@22) ($Is d@@22 Tclass.Test.BetreeNode))
 :pattern ( (Test.BetreeNode.Nil_q d@@22) ($Is d@@22 Tclass.Test.BetreeNode))
)))
(assert (forall ((a@@106 T@U) (b@@67 T@U) ) (!  (=> (and (and (= (type a@@106) DatatypeTypeType) (= (type b@@67) DatatypeTypeType)) (and (Test.BetreeNode.Nil_q a@@106) (Test.BetreeNode.Nil_q b@@67))) (= (|Test.BetreeNode#Equal| a@@106 b@@67) true))
 :qid |unknown.0:0|
 :skolemid |932|
 :pattern ( (|Test.BetreeNode#Equal| a@@106 b@@67) (Test.BetreeNode.Nil_q a@@106))
 :pattern ( (|Test.BetreeNode#Equal| a@@106 b@@67) (Test.BetreeNode.Nil_q b@@67))
)))
(assert (forall ((a@@107 T@U) (b@@68 T@U) ) (!  (=> (and (and (= (type a@@107) DatatypeTypeType) (= (type b@@68) DatatypeTypeType)) (and (Test.BetreeNode.BetreeNode_q a@@107) (Test.BetreeNode.BetreeNode_q b@@68))) (= (|Test.BetreeNode#Equal| a@@107 b@@68) (|Test.ChildMap#Equal| (Test.BetreeNode.children a@@107) (Test.BetreeNode.children b@@68))))
 :qid |unknown.0:0|
 :skolemid |933|
 :pattern ( (|Test.BetreeNode#Equal| a@@107 b@@68) (Test.BetreeNode.BetreeNode_q a@@107))
 :pattern ( (|Test.BetreeNode#Equal| a@@107 b@@68) (Test.BetreeNode.BetreeNode_q b@@68))
)))
(assert (forall ((a@@108 T@U) (b@@69 T@U) ) (!  (=> (and (= (type a@@108) DatatypeTypeType) (= (type b@@69) DatatypeTypeType)) (= (|Test.BetreeNode#Equal| a@@108 b@@69) (= a@@108 b@@69)))
 :qid |unknown.0:0|
 :skolemid |934|
 :pattern ( (|Test.BetreeNode#Equal| a@@108 b@@69))
)))
(assert (forall (($ly@@5 T@U) (this@@5 T@U) ) (!  (=> (and (= (type $ly@@5) LayerTypeType) (= (type this@@5) DatatypeTypeType)) (= (Test.BetreeNode.WF ($LS $ly@@5) this@@5) (Test.BetreeNode.WF $ly@@5 this@@5)))
 :qid |Testidfy.14:15|
 :skolemid |935|
 :pattern ( (Test.BetreeNode.WF ($LS $ly@@5) this@@5))
)))
(assert (forall (($ly@@6 T@U) (this@@6 T@U) ) (!  (=> (and (= (type $ly@@6) LayerTypeType) (= (type this@@6) DatatypeTypeType)) (= (Test.BetreeNode.WF $ly@@6 this@@6) (Test.BetreeNode.WF $LZ this@@6)))
 :qid |Testidfy.14:15|
 :skolemid |936|
 :pattern ( (Test.BetreeNode.WF (AsFuelBottom $ly@@6) this@@6))
)))
(assert  (=> (<= 5 $FunctionContextHeight) (forall (($ly@@7 T@U) (this@@7 T@U) ) (!  (=> (and (and (= (type $ly@@7) LayerTypeType) (= (type this@@7) DatatypeTypeType)) (or (|Test.BetreeNode.WF#canCall| this@@7) (and (not (= 5 $FunctionContextHeight)) ($Is this@@7 Tclass.Test.BetreeNode)))) true)
 :qid |Testidfy.14:15|
 :skolemid |937|
 :pattern ( (Test.BetreeNode.WF $ly@@7 this@@7))
))))
(assert (forall (($ly@@8 T@U) (this@@8 T@U) ) (!  (=> (and (and (= (type $ly@@8) LayerTypeType) (= (type this@@8) DatatypeTypeType)) ($Is this@@8 Tclass.Test.BetreeNode)) (= (|Test.BetreeNode.WF#requires| $ly@@8 this@@8) true))
 :qid |Testidfy.14:15|
 :skolemid |938|
 :pattern ( (|Test.BetreeNode.WF#requires| $ly@@8 this@@8))
)))
(assert  (=> (<= 5 $FunctionContextHeight) (forall (($ly@@9 T@U) (this@@9 T@U) ) (!  (=> (and (and (= (type $ly@@9) LayerTypeType) (= (type this@@9) DatatypeTypeType)) (or (|Test.BetreeNode.WF#canCall| this@@9) (and (not (= 5 $FunctionContextHeight)) ($Is this@@9 Tclass.Test.BetreeNode)))) (and (=> (U_2_bool (Lit (bool_2_U true))) (=> (Test.BetreeNode.BetreeNode_q this@@9) (|Test.ChildMap.WF#canCall| (Test.BetreeNode.children this@@9)))) (= (Test.BetreeNode.WF ($LS $ly@@9) this@@9)  (and true (=> (Test.BetreeNode.BetreeNode_q this@@9) (Test.ChildMap.WF $ly@@9 (Test.BetreeNode.children this@@9)))))))
 :qid |Testidfy.14:15|
 :skolemid |939|
 :pattern ( (Test.BetreeNode.WF ($LS $ly@@9) this@@9))
))))
(assert  (=> (<= 5 $FunctionContextHeight) (forall (($ly@@10 T@U) (this@@10 T@U) ) (!  (=> (and (and (= (type $ly@@10) LayerTypeType) (= (type this@@10) DatatypeTypeType)) (or (|Test.BetreeNode.WF#canCall| (Lit this@@10)) (and (not (= 5 $FunctionContextHeight)) ($Is this@@10 Tclass.Test.BetreeNode)))) (and (=> (U_2_bool (Lit (bool_2_U true))) (=> (U_2_bool (Lit (bool_2_U (Test.BetreeNode.BetreeNode_q (Lit this@@10))))) (|Test.ChildMap.WF#canCall| (Lit (Test.BetreeNode.children (Lit this@@10)))))) (= (Test.BetreeNode.WF ($LS $ly@@10) (Lit this@@10)) (U_2_bool (Lit (bool_2_U  (and true (=> (Test.BetreeNode.BetreeNode_q (Lit this@@10)) (Test.ChildMap.WF ($LS $ly@@10) (Lit (Test.BetreeNode.children (Lit this@@10))))))))))))
 :qid |Testidfy.14:15|
 :weight 3
 :skolemid |940|
 :pattern ( (Test.BetreeNode.WF ($LS $ly@@10) (Lit this@@10)))
))))
(assert (forall ((arg0@@175 T@U) ) (! (= (type (|#Test.QueryReceiptLine.QueryReceiptLine| arg0@@175)) DatatypeTypeType)
 :qid |funType:#Test.QueryReceiptLine.QueryReceiptLine|
 :pattern ( (|#Test.QueryReceiptLine.QueryReceiptLine| arg0@@175))
)))
(assert (forall ((|a#0#0#0@@0| T@U) ) (!  (=> (= (type |a#0#0#0@@0|) DatatypeTypeType) (= (DatatypeCtorId (|#Test.QueryReceiptLine.QueryReceiptLine| |a#0#0#0@@0|)) |##Test.QueryReceiptLine.QueryReceiptLine|))
 :qid |Testidfy.19:46|
 :skolemid |942|
 :pattern ( (|#Test.QueryReceiptLine.QueryReceiptLine| |a#0#0#0@@0|))
)))
(assert (forall ((d@@23 T@U) ) (!  (=> (= (type d@@23) DatatypeTypeType) (= (Test.QueryReceiptLine.QueryReceiptLine_q d@@23) (= (DatatypeCtorId d@@23) |##Test.QueryReceiptLine.QueryReceiptLine|)))
 :qid |unknown.0:0|
 :skolemid |943|
 :pattern ( (Test.QueryReceiptLine.QueryReceiptLine_q d@@23))
)))
(assert (forall ((d@@24 T@U) ) (!  (=> (and (= (type d@@24) DatatypeTypeType) (Test.QueryReceiptLine.QueryReceiptLine_q d@@24)) (exists ((|a#1#0#0@@0| T@U) ) (!  (and (= (type |a#1#0#0@@0|) DatatypeTypeType) (= d@@24 (|#Test.QueryReceiptLine.QueryReceiptLine| |a#1#0#0@@0|)))
 :qid |Testidfy.19:46|
 :skolemid |944|
 :no-pattern (type |a#1#0#0@@0|)
 :no-pattern (U_2_int |a#1#0#0@@0|)
 :no-pattern (U_2_bool |a#1#0#0@@0|)
)))
 :qid |unknown.0:0|
 :skolemid |945|
 :pattern ( (Test.QueryReceiptLine.QueryReceiptLine_q d@@24))
)))
(assert (= (type Tclass.Test.QueryReceiptLine) TyType))
(assert (= (Tag Tclass.Test.QueryReceiptLine) Tagclass.Test.QueryReceiptLine))
(assert (= (TagFamily Tclass.Test.QueryReceiptLine) tytagFamily$QueryReceiptLine))
(assert (forall ((bx@@56 T@U) ) (!  (=> (and (= (type bx@@56) BoxType) ($IsBox bx@@56 Tclass.Test.QueryReceiptLine)) (and (= ($Box ($Unbox DatatypeTypeType bx@@56)) bx@@56) ($Is ($Unbox DatatypeTypeType bx@@56) Tclass.Test.QueryReceiptLine)))
 :qid |unknown.0:0|
 :skolemid |946|
 :pattern ( ($IsBox bx@@56 Tclass.Test.QueryReceiptLine))
)))
(assert (forall ((|a#2#0#0@@0| T@U) ) (!  (=> (= (type |a#2#0#0@@0|) DatatypeTypeType) (= ($Is (|#Test.QueryReceiptLine.QueryReceiptLine| |a#2#0#0@@0|) Tclass.Test.QueryReceiptLine) ($Is |a#2#0#0@@0| Tclass.Test.BetreeNode)))
 :qid |Testidfy.19:46|
 :skolemid |947|
 :pattern ( ($Is (|#Test.QueryReceiptLine.QueryReceiptLine| |a#2#0#0@@0|) Tclass.Test.QueryReceiptLine))
)))
(assert (forall ((|a#3#0#0@@0| T@U) ($h@@23 T@U) ) (!  (=> (and (and (= (type |a#3#0#0@@0|) DatatypeTypeType) (= (type $h@@23) (MapType0Type refType MapType1Type))) ($IsGoodHeap $h@@23)) (= ($IsAlloc (|#Test.QueryReceiptLine.QueryReceiptLine| |a#3#0#0@@0|) Tclass.Test.QueryReceiptLine $h@@23) ($IsAlloc |a#3#0#0@@0| Tclass.Test.BetreeNode $h@@23)))
 :qid |Testidfy.19:46|
 :skolemid |948|
 :pattern ( ($IsAlloc (|#Test.QueryReceiptLine.QueryReceiptLine| |a#3#0#0@@0|) Tclass.Test.QueryReceiptLine $h@@23))
)))
(assert (forall ((arg0@@176 T@U) ) (! (= (type (Test.QueryReceiptLine.node arg0@@176)) DatatypeTypeType)
 :qid |funType:Test.QueryReceiptLine.node|
 :pattern ( (Test.QueryReceiptLine.node arg0@@176))
)))
(assert (forall ((d@@25 T@U) ($h@@24 T@U) ) (!  (=> (and (and (= (type d@@25) DatatypeTypeType) (= (type $h@@24) (MapType0Type refType MapType1Type))) (and ($IsGoodHeap $h@@24) (and (Test.QueryReceiptLine.QueryReceiptLine_q d@@25) ($IsAlloc d@@25 Tclass.Test.QueryReceiptLine $h@@24)))) ($IsAlloc (Test.QueryReceiptLine.node d@@25) Tclass.Test.BetreeNode $h@@24))
 :qid |unknown.0:0|
 :skolemid |949|
 :pattern ( ($IsAlloc (Test.QueryReceiptLine.node d@@25) Tclass.Test.BetreeNode $h@@24))
)))
(assert (forall ((|a#4#0#0@@0| T@U) ) (!  (=> (= (type |a#4#0#0@@0|) DatatypeTypeType) (= (|#Test.QueryReceiptLine.QueryReceiptLine| (Lit |a#4#0#0@@0|)) (Lit (|#Test.QueryReceiptLine.QueryReceiptLine| |a#4#0#0@@0|))))
 :qid |Testidfy.19:46|
 :skolemid |950|
 :pattern ( (|#Test.QueryReceiptLine.QueryReceiptLine| (Lit |a#4#0#0@@0|)))
)))
(assert (forall ((|a#5#0#0@@1| T@U) ) (!  (=> (= (type |a#5#0#0@@1|) DatatypeTypeType) (= (Test.QueryReceiptLine.node (|#Test.QueryReceiptLine.QueryReceiptLine| |a#5#0#0@@1|)) |a#5#0#0@@1|))
 :qid |Testidfy.19:46|
 :skolemid |951|
 :pattern ( (|#Test.QueryReceiptLine.QueryReceiptLine| |a#5#0#0@@1|))
)))
(assert (forall ((|a#6#0#0@@1| T@U) ) (!  (=> (= (type |a#6#0#0@@1|) DatatypeTypeType) (< (DtRank |a#6#0#0@@1|) (DtRank (|#Test.QueryReceiptLine.QueryReceiptLine| |a#6#0#0@@1|))))
 :qid |Testidfy.19:46|
 :skolemid |952|
 :pattern ( (|#Test.QueryReceiptLine.QueryReceiptLine| |a#6#0#0@@1|))
)))
(assert (forall ((d@@26 T@U) ) (!  (=> (and (= (type d@@26) DatatypeTypeType) (|$IsA#Test.QueryReceiptLine| d@@26)) (Test.QueryReceiptLine.QueryReceiptLine_q d@@26))
 :qid |unknown.0:0|
 :skolemid |953|
 :pattern ( (|$IsA#Test.QueryReceiptLine| d@@26))
)))
(assert (forall ((d@@27 T@U) ) (!  (=> (and (= (type d@@27) DatatypeTypeType) ($Is d@@27 Tclass.Test.QueryReceiptLine)) (Test.QueryReceiptLine.QueryReceiptLine_q d@@27))
 :qid |unknown.0:0|
 :skolemid |954|
 :pattern ( (Test.QueryReceiptLine.QueryReceiptLine_q d@@27) ($Is d@@27 Tclass.Test.QueryReceiptLine))
)))
(assert (forall ((a@@109 T@U) (b@@70 T@U) ) (!  (=> (and (and (= (type a@@109) DatatypeTypeType) (= (type b@@70) DatatypeTypeType)) true) (= (|Test.QueryReceiptLine#Equal| a@@109 b@@70) (|Test.BetreeNode#Equal| (Test.QueryReceiptLine.node a@@109) (Test.QueryReceiptLine.node b@@70))))
 :qid |unknown.0:0|
 :skolemid |955|
 :pattern ( (|Test.QueryReceiptLine#Equal| a@@109 b@@70))
)))
(assert (forall ((a@@110 T@U) (b@@71 T@U) ) (!  (=> (and (= (type a@@110) DatatypeTypeType) (= (type b@@71) DatatypeTypeType)) (= (|Test.QueryReceiptLine#Equal| a@@110 b@@71) (= a@@110 b@@71)))
 :qid |unknown.0:0|
 :skolemid |956|
 :pattern ( (|Test.QueryReceiptLine#Equal| a@@110 b@@71))
)))
(assert  (=> (<= 6 $FunctionContextHeight) (forall ((this@@11 T@U) ) (!  (=> (and (= (type this@@11) DatatypeTypeType) (or (|Test.QueryReceiptLine.WF#canCall| this@@11) (and (not (= 6 $FunctionContextHeight)) ($Is this@@11 Tclass.Test.QueryReceiptLine)))) true)
 :qid |Testidfy.20:15|
 :skolemid |957|
 :pattern ( (Test.QueryReceiptLine.WF this@@11))
))))
(assert (forall ((this@@12 T@U) ) (!  (=> (and (= (type this@@12) DatatypeTypeType) ($Is this@@12 Tclass.Test.QueryReceiptLine)) (= (|Test.QueryReceiptLine.WF#requires| this@@12) true))
 :qid |Testidfy.20:15|
 :skolemid |958|
 :pattern ( (|Test.QueryReceiptLine.WF#requires| this@@12))
)))
(assert  (=> (<= 6 $FunctionContextHeight) (forall ((this@@13 T@U) ) (!  (=> (and (= (type this@@13) DatatypeTypeType) (or (|Test.QueryReceiptLine.WF#canCall| this@@13) (and (not (= 6 $FunctionContextHeight)) ($Is this@@13 Tclass.Test.QueryReceiptLine)))) (and (=> (U_2_bool (Lit (bool_2_U true))) (and (Test.QueryReceiptLine.QueryReceiptLine_q this@@13) (|Test.BetreeNode.WF#canCall| (Test.QueryReceiptLine.node this@@13)))) (= (Test.QueryReceiptLine.WF this@@13)  (and true (Test.BetreeNode.WF ($LS $LZ) (Test.QueryReceiptLine.node this@@13))))))
 :qid |Testidfy.20:15|
 :skolemid |959|
 :pattern ( (Test.QueryReceiptLine.WF this@@13))
))))
(assert  (=> (<= 6 $FunctionContextHeight) (forall ((this@@14 T@U) ) (!  (=> (and (= (type this@@14) DatatypeTypeType) (or (|Test.QueryReceiptLine.WF#canCall| (Lit this@@14)) (and (not (= 6 $FunctionContextHeight)) ($Is this@@14 Tclass.Test.QueryReceiptLine)))) (and (=> (U_2_bool (Lit (bool_2_U true))) (and (Test.QueryReceiptLine.QueryReceiptLine_q (Lit this@@14)) (|Test.BetreeNode.WF#canCall| (Lit (Test.QueryReceiptLine.node (Lit this@@14)))))) (= (Test.QueryReceiptLine.WF (Lit this@@14)) (U_2_bool (Lit (bool_2_U  (and true (Test.BetreeNode.WF ($LS $LZ) (Lit (Test.QueryReceiptLine.node (Lit this@@14)))))))))))
 :qid |Testidfy.20:15|
 :weight 3
 :skolemid |960|
 :pattern ( (Test.QueryReceiptLine.WF (Lit this@@14)))
))))
(assert (forall ((arg0@@177 T@U) (arg1@@80 T@U) (arg2@@32 T@U) ) (! (= (type (|#Test.QueryReceipt.QueryReceipt| arg0@@177 arg1@@80 arg2@@32)) DatatypeTypeType)
 :qid |funType:#Test.QueryReceipt.QueryReceipt|
 :pattern ( (|#Test.QueryReceipt.QueryReceipt| arg0@@177 arg1@@80 arg2@@32))
)))
(assert (forall ((|a#0#0#0@@1| T@U) (|a#0#1#0@@0| T@U) (|a#0#2#0| T@U) ) (!  (=> (and (and (= (type |a#0#0#0@@1|) (SeqType BoxType)) (= (type |a#0#1#0@@0|) DatatypeTypeType)) (= (type |a#0#2#0|) (SeqType BoxType))) (= (DatatypeCtorId (|#Test.QueryReceipt.QueryReceipt| |a#0#0#0@@1| |a#0#1#0@@0| |a#0#2#0|)) |##Test.QueryReceipt.QueryReceipt|))
 :qid |Testidfy.26:5|
 :skolemid |962|
 :pattern ( (|#Test.QueryReceipt.QueryReceipt| |a#0#0#0@@1| |a#0#1#0@@0| |a#0#2#0|))
)))
(assert (forall ((d@@28 T@U) ) (!  (=> (= (type d@@28) DatatypeTypeType) (= (Test.QueryReceipt.QueryReceipt_q d@@28) (= (DatatypeCtorId d@@28) |##Test.QueryReceipt.QueryReceipt|)))
 :qid |unknown.0:0|
 :skolemid |963|
 :pattern ( (Test.QueryReceipt.QueryReceipt_q d@@28))
)))
(assert (forall ((d@@29 T@U) ) (!  (=> (and (= (type d@@29) DatatypeTypeType) (Test.QueryReceipt.QueryReceipt_q d@@29)) (exists ((|a#1#0#0@@1| T@U) (|a#1#1#0@@0| T@U) (|a#1#2#0| T@U) ) (!  (and (and (and (= (type |a#1#0#0@@1|) (SeqType BoxType)) (= (type |a#1#1#0@@0|) DatatypeTypeType)) (= (type |a#1#2#0|) (SeqType BoxType))) (= d@@29 (|#Test.QueryReceipt.QueryReceipt| |a#1#0#0@@1| |a#1#1#0@@0| |a#1#2#0|)))
 :qid |Testidfy.26:5|
 :skolemid |964|
 :no-pattern (type |a#1#0#0@@1|)
 :no-pattern (type |a#1#1#0@@0|)
 :no-pattern (type |a#1#2#0|)
 :no-pattern (U_2_int |a#1#0#0@@1|)
 :no-pattern (U_2_bool |a#1#0#0@@1|)
 :no-pattern (U_2_int |a#1#1#0@@0|)
 :no-pattern (U_2_bool |a#1#1#0@@0|)
 :no-pattern (U_2_int |a#1#2#0|)
 :no-pattern (U_2_bool |a#1#2#0|)
)))
 :qid |unknown.0:0|
 :skolemid |965|
 :pattern ( (Test.QueryReceipt.QueryReceipt_q d@@29))
)))
(assert (= (type Tclass.Test.QueryReceipt) TyType))
(assert (= (Tag Tclass.Test.QueryReceipt) Tagclass.Test.QueryReceipt))
(assert (= (TagFamily Tclass.Test.QueryReceipt) tytagFamily$QueryReceipt))
(assert (forall ((bx@@57 T@U) ) (!  (=> (and (= (type bx@@57) BoxType) ($IsBox bx@@57 Tclass.Test.QueryReceipt)) (and (= ($Box ($Unbox DatatypeTypeType bx@@57)) bx@@57) ($Is ($Unbox DatatypeTypeType bx@@57) Tclass.Test.QueryReceipt)))
 :qid |unknown.0:0|
 :skolemid |966|
 :pattern ( ($IsBox bx@@57 Tclass.Test.QueryReceipt))
)))
(assert (forall ((|a#2#0#0@@1| T@U) (|a#2#1#0@@0| T@U) (|a#2#2#0| T@U) ) (!  (=> (and (and (= (type |a#2#0#0@@1|) (SeqType BoxType)) (= (type |a#2#1#0@@0|) DatatypeTypeType)) (= (type |a#2#2#0|) (SeqType BoxType))) (= ($Is (|#Test.QueryReceipt.QueryReceipt| |a#2#0#0@@1| |a#2#1#0@@0| |a#2#2#0|) Tclass.Test.QueryReceipt)  (and (and ($Is |a#2#0#0@@1| Tclass.Common.Key) ($Is |a#2#1#0@@0| Tclass.Test.BetreeNode)) ($Is |a#2#2#0| (TSeq Tclass.Test.QueryReceiptLine)))))
 :qid |Testidfy.26:5|
 :skolemid |967|
 :pattern ( ($Is (|#Test.QueryReceipt.QueryReceipt| |a#2#0#0@@1| |a#2#1#0@@0| |a#2#2#0|) Tclass.Test.QueryReceipt))
)))
(assert (forall ((|a#3#0#0@@1| T@U) (|a#3#1#0@@0| T@U) (|a#3#2#0| T@U) ($h@@25 T@U) ) (!  (=> (and (and (and (and (= (type |a#3#0#0@@1|) (SeqType BoxType)) (= (type |a#3#1#0@@0|) DatatypeTypeType)) (= (type |a#3#2#0|) (SeqType BoxType))) (= (type $h@@25) (MapType0Type refType MapType1Type))) ($IsGoodHeap $h@@25)) (= ($IsAlloc (|#Test.QueryReceipt.QueryReceipt| |a#3#0#0@@1| |a#3#1#0@@0| |a#3#2#0|) Tclass.Test.QueryReceipt $h@@25)  (and (and ($IsAlloc |a#3#0#0@@1| Tclass.Common.Key $h@@25) ($IsAlloc |a#3#1#0@@0| Tclass.Test.BetreeNode $h@@25)) ($IsAlloc |a#3#2#0| (TSeq Tclass.Test.QueryReceiptLine) $h@@25))))
 :qid |Testidfy.26:5|
 :skolemid |968|
 :pattern ( ($IsAlloc (|#Test.QueryReceipt.QueryReceipt| |a#3#0#0@@1| |a#3#1#0@@0| |a#3#2#0|) Tclass.Test.QueryReceipt $h@@25))
)))
(assert (forall ((arg0@@178 T@U) ) (! (= (type (Test.QueryReceipt.key arg0@@178)) (SeqType BoxType))
 :qid |funType:Test.QueryReceipt.key|
 :pattern ( (Test.QueryReceipt.key arg0@@178))
)))
(assert (forall ((d@@30 T@U) ($h@@26 T@U) ) (!  (=> (and (and (= (type d@@30) DatatypeTypeType) (= (type $h@@26) (MapType0Type refType MapType1Type))) (and ($IsGoodHeap $h@@26) (and (Test.QueryReceipt.QueryReceipt_q d@@30) ($IsAlloc d@@30 Tclass.Test.QueryReceipt $h@@26)))) ($IsAlloc (Test.QueryReceipt.key d@@30) Tclass.Common.Key $h@@26))
 :qid |unknown.0:0|
 :skolemid |969|
 :pattern ( ($IsAlloc (Test.QueryReceipt.key d@@30) Tclass.Common.Key $h@@26))
)))
(assert (forall ((arg0@@179 T@U) ) (! (= (type (Test.QueryReceipt.root arg0@@179)) DatatypeTypeType)
 :qid |funType:Test.QueryReceipt.root|
 :pattern ( (Test.QueryReceipt.root arg0@@179))
)))
(assert (forall ((d@@31 T@U) ($h@@27 T@U) ) (!  (=> (and (and (= (type d@@31) DatatypeTypeType) (= (type $h@@27) (MapType0Type refType MapType1Type))) (and ($IsGoodHeap $h@@27) (and (Test.QueryReceipt.QueryReceipt_q d@@31) ($IsAlloc d@@31 Tclass.Test.QueryReceipt $h@@27)))) ($IsAlloc (Test.QueryReceipt.root d@@31) Tclass.Test.BetreeNode $h@@27))
 :qid |unknown.0:0|
 :skolemid |970|
 :pattern ( ($IsAlloc (Test.QueryReceipt.root d@@31) Tclass.Test.BetreeNode $h@@27))
)))
(assert (forall ((arg0@@180 T@U) ) (! (= (type (Test.QueryReceipt.lines arg0@@180)) (SeqType BoxType))
 :qid |funType:Test.QueryReceipt.lines|
 :pattern ( (Test.QueryReceipt.lines arg0@@180))
)))
(assert (forall ((d@@32 T@U) ($h@@28 T@U) ) (!  (=> (and (and (= (type d@@32) DatatypeTypeType) (= (type $h@@28) (MapType0Type refType MapType1Type))) (and ($IsGoodHeap $h@@28) (and (Test.QueryReceipt.QueryReceipt_q d@@32) ($IsAlloc d@@32 Tclass.Test.QueryReceipt $h@@28)))) ($IsAlloc (Test.QueryReceipt.lines d@@32) (TSeq Tclass.Test.QueryReceiptLine) $h@@28))
 :qid |unknown.0:0|
 :skolemid |971|
 :pattern ( ($IsAlloc (Test.QueryReceipt.lines d@@32) (TSeq Tclass.Test.QueryReceiptLine) $h@@28))
)))
(assert (forall ((|a#4#0#0@@1| T@U) (|a#4#1#0@@0| T@U) (|a#4#2#0| T@U) ) (!  (=> (and (and (= (type |a#4#0#0@@1|) (SeqType BoxType)) (= (type |a#4#1#0@@0|) DatatypeTypeType)) (= (type |a#4#2#0|) (SeqType BoxType))) (= (|#Test.QueryReceipt.QueryReceipt| (Lit |a#4#0#0@@1|) (Lit |a#4#1#0@@0|) (Lit |a#4#2#0|)) (Lit (|#Test.QueryReceipt.QueryReceipt| |a#4#0#0@@1| |a#4#1#0@@0| |a#4#2#0|))))
 :qid |Testidfy.26:5|
 :skolemid |972|
 :pattern ( (|#Test.QueryReceipt.QueryReceipt| (Lit |a#4#0#0@@1|) (Lit |a#4#1#0@@0|) (Lit |a#4#2#0|)))
)))
(assert (forall ((|a#5#0#0@@2| T@U) (|a#5#1#0@@0| T@U) (|a#5#2#0| T@U) ) (!  (=> (and (and (= (type |a#5#0#0@@2|) (SeqType BoxType)) (= (type |a#5#1#0@@0|) DatatypeTypeType)) (= (type |a#5#2#0|) (SeqType BoxType))) (= (Test.QueryReceipt.key (|#Test.QueryReceipt.QueryReceipt| |a#5#0#0@@2| |a#5#1#0@@0| |a#5#2#0|)) |a#5#0#0@@2|))
 :qid |Testidfy.26:5|
 :skolemid |973|
 :pattern ( (|#Test.QueryReceipt.QueryReceipt| |a#5#0#0@@2| |a#5#1#0@@0| |a#5#2#0|))
)))
(assert (forall ((|a#6#0#0@@2| T@U) (|a#6#1#0@@0| T@U) (|a#6#2#0| T@U) ) (!  (=> (and (and (= (type |a#6#0#0@@2|) (SeqType BoxType)) (= (type |a#6#1#0@@0|) DatatypeTypeType)) (= (type |a#6#2#0|) (SeqType BoxType))) (= (Test.QueryReceipt.root (|#Test.QueryReceipt.QueryReceipt| |a#6#0#0@@2| |a#6#1#0@@0| |a#6#2#0|)) |a#6#1#0@@0|))
 :qid |Testidfy.26:5|
 :skolemid |974|
 :pattern ( (|#Test.QueryReceipt.QueryReceipt| |a#6#0#0@@2| |a#6#1#0@@0| |a#6#2#0|))
)))
(assert (forall ((|a#7#0#0@@1| T@U) (|a#7#1#0@@0| T@U) (|a#7#2#0| T@U) ) (!  (=> (and (and (= (type |a#7#0#0@@1|) (SeqType BoxType)) (= (type |a#7#1#0@@0|) DatatypeTypeType)) (= (type |a#7#2#0|) (SeqType BoxType))) (< (DtRank |a#7#1#0@@0|) (DtRank (|#Test.QueryReceipt.QueryReceipt| |a#7#0#0@@1| |a#7#1#0@@0| |a#7#2#0|))))
 :qid |Testidfy.26:5|
 :skolemid |975|
 :pattern ( (|#Test.QueryReceipt.QueryReceipt| |a#7#0#0@@1| |a#7#1#0@@0| |a#7#2#0|))
)))
(assert (forall ((|a#8#0#0@@1| T@U) (|a#8#1#0@@0| T@U) (|a#8#2#0| T@U) ) (!  (=> (and (and (= (type |a#8#0#0@@1|) (SeqType BoxType)) (= (type |a#8#1#0@@0|) DatatypeTypeType)) (= (type |a#8#2#0|) (SeqType BoxType))) (= (Test.QueryReceipt.lines (|#Test.QueryReceipt.QueryReceipt| |a#8#0#0@@1| |a#8#1#0@@0| |a#8#2#0|)) |a#8#2#0|))
 :qid |Testidfy.26:5|
 :skolemid |976|
 :pattern ( (|#Test.QueryReceipt.QueryReceipt| |a#8#0#0@@1| |a#8#1#0@@0| |a#8#2#0|))
)))
(assert (forall ((|a#9#0#0@@0| T@U) (|a#9#1#0| T@U) (|a#9#2#0| T@U) (i@@25 Int) ) (!  (=> (and (and (and (= (type |a#9#0#0@@0|) (SeqType BoxType)) (= (type |a#9#1#0|) DatatypeTypeType)) (= (type |a#9#2#0|) (SeqType BoxType))) (and (<= 0 i@@25) (< i@@25 (|Seq#Length| |a#9#2#0|)))) (< (DtRank ($Unbox DatatypeTypeType (|Seq#Index| |a#9#2#0| i@@25))) (DtRank (|#Test.QueryReceipt.QueryReceipt| |a#9#0#0@@0| |a#9#1#0| |a#9#2#0|))))
 :qid |Testidfy.26:5|
 :skolemid |977|
 :pattern ( (|Seq#Index| |a#9#2#0| i@@25) (|#Test.QueryReceipt.QueryReceipt| |a#9#0#0@@0| |a#9#1#0| |a#9#2#0|))
)))
(assert (forall ((|a#10#0#0@@0| T@U) (|a#10#1#0| T@U) (|a#10#2#0| T@U) ) (!  (=> (and (and (= (type |a#10#0#0@@0|) (SeqType BoxType)) (= (type |a#10#1#0|) DatatypeTypeType)) (= (type |a#10#2#0|) (SeqType BoxType))) (< (|Seq#Rank| |a#10#2#0|) (DtRank (|#Test.QueryReceipt.QueryReceipt| |a#10#0#0@@0| |a#10#1#0| |a#10#2#0|))))
 :qid |Testidfy.26:5|
 :skolemid |978|
 :pattern ( (|#Test.QueryReceipt.QueryReceipt| |a#10#0#0@@0| |a#10#1#0| |a#10#2#0|))
)))
(assert (forall ((d@@33 T@U) ) (!  (=> (and (= (type d@@33) DatatypeTypeType) (|$IsA#Test.QueryReceipt| d@@33)) (Test.QueryReceipt.QueryReceipt_q d@@33))
 :qid |unknown.0:0|
 :skolemid |979|
 :pattern ( (|$IsA#Test.QueryReceipt| d@@33))
)))
(assert (forall ((d@@34 T@U) ) (!  (=> (and (= (type d@@34) DatatypeTypeType) ($Is d@@34 Tclass.Test.QueryReceipt)) (Test.QueryReceipt.QueryReceipt_q d@@34))
 :qid |unknown.0:0|
 :skolemid |980|
 :pattern ( (Test.QueryReceipt.QueryReceipt_q d@@34) ($Is d@@34 Tclass.Test.QueryReceipt))
)))
(assert (forall ((a@@111 T@U) (b@@72 T@U) ) (!  (=> (and (and (= (type a@@111) DatatypeTypeType) (= (type b@@72) DatatypeTypeType)) true) (= (|Test.QueryReceipt#Equal| a@@111 b@@72)  (and (and (|Seq#Equal| (Test.QueryReceipt.key a@@111) (Test.QueryReceipt.key b@@72)) (|Test.BetreeNode#Equal| (Test.QueryReceipt.root a@@111) (Test.QueryReceipt.root b@@72))) (|Seq#Equal| (Test.QueryReceipt.lines a@@111) (Test.QueryReceipt.lines b@@72)))))
 :qid |unknown.0:0|
 :skolemid |981|
 :pattern ( (|Test.QueryReceipt#Equal| a@@111 b@@72))
)))
(assert (forall ((a@@112 T@U) (b@@73 T@U) ) (!  (=> (and (= (type a@@112) DatatypeTypeType) (= (type b@@73) DatatypeTypeType)) (= (|Test.QueryReceipt#Equal| a@@112 b@@73) (= a@@112 b@@73)))
 :qid |unknown.0:0|
 :skolemid |982|
 :pattern ( (|Test.QueryReceipt#Equal| a@@112 b@@73))
)))
(assert  (=> (<= 8 $FunctionContextHeight) (forall ((this@@15 T@U) ) (!  (=> (and (= (type this@@15) DatatypeTypeType) (or (|Test.QueryReceipt.Structure#canCall| this@@15) (and (not (= 8 $FunctionContextHeight)) ($Is this@@15 Tclass.Test.QueryReceipt)))) true)
 :qid |Testidfy.30:15|
 :skolemid |983|
 :pattern ( (Test.QueryReceipt.Structure this@@15))
))))
(assert (forall ((this@@16 T@U) ) (!  (=> (and (= (type this@@16) DatatypeTypeType) ($Is this@@16 Tclass.Test.QueryReceipt)) (= (|Test.QueryReceipt.Structure#requires| this@@16) true))
 :qid |Testidfy.30:15|
 :skolemid |984|
 :pattern ( (|Test.QueryReceipt.Structure#requires| this@@16))
)))
(assert  (=> (<= 8 $FunctionContextHeight) (forall ((this@@17 T@U) ) (!  (=> (and (= (type this@@17) DatatypeTypeType) (or (|Test.QueryReceipt.Structure#canCall| this@@17) (and (not (= 8 $FunctionContextHeight)) ($Is this@@17 Tclass.Test.QueryReceipt)))) (and (and (Test.QueryReceipt.QueryReceipt_q this@@17) (=> (INTERNAL_lt_boogie 0 (|Seq#Length| (Test.QueryReceipt.lines this@@17))) (and (and (and (|$IsA#Test.BetreeNode| (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@17) (LitInt 0))))) (|$IsA#Test.BetreeNode| (Test.QueryReceipt.root this@@17))) (and (and (Test.QueryReceipt.QueryReceipt_q this@@17) (Test.QueryReceiptLine.QueryReceiptLine_q ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@17) (LitInt 0))))) (Test.QueryReceipt.QueryReceipt_q this@@17))) (=> (|Test.BetreeNode#Equal| (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@17) (LitInt 0)))) (Test.QueryReceipt.root this@@17)) (forall ((|i#0| Int) ) (!  (=> (INTERNAL_le_boogie 0 |i#0|) (and (Test.QueryReceipt.QueryReceipt_q this@@17) (=> (INTERNAL_lt_boogie |i#0| (|Seq#Length| (Test.QueryReceipt.lines this@@17))) (and (and (Test.QueryReceipt.QueryReceipt_q this@@17) (Test.QueryReceiptLine.QueryReceiptLine_q ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@17) |i#0|)))) (Test.QueryReceipt.QueryReceipt_q this@@17)))))
 :qid |Testidfy.33:20|
 :skolemid |986|
 :pattern ( ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@17) |i#0|)))
)))))) (= (Test.QueryReceipt.Structure this@@17)  (and (and (INTERNAL_lt_boogie 0 (|Seq#Length| (Test.QueryReceipt.lines this@@17))) (|Test.BetreeNode#Equal| (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@17) (LitInt 0)))) (Test.QueryReceipt.root this@@17))) (forall ((|i#0@@0| Int) ) (!  (=> (and (INTERNAL_le_boogie 0 |i#0@@0|) (INTERNAL_lt_boogie |i#0@@0| (|Seq#Length| (Test.QueryReceipt.lines this@@17)))) (= (Test.BetreeNode.BetreeNode_q (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@17) |i#0@@0|)))) (INTERNAL_lt_boogie |i#0@@0| (INTERNAL_sub_boogie (|Seq#Length| (Test.QueryReceipt.lines this@@17)) 1))))
 :qid |Testidfy.33:20|
 :skolemid |985|
 :pattern ( ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@17) |i#0@@0|)))
))))))
 :qid |Testidfy.30:15|
 :skolemid |987|
 :pattern ( (Test.QueryReceipt.Structure this@@17))
))))
(assert  (=> (<= 8 $FunctionContextHeight) (forall ((this@@18 T@U) ) (!  (=> (and (= (type this@@18) DatatypeTypeType) (or (|Test.QueryReceipt.Structure#canCall| (Lit this@@18)) (and (not (= 8 $FunctionContextHeight)) ($Is this@@18 Tclass.Test.QueryReceipt)))) (and (and (Test.QueryReceipt.QueryReceipt_q (Lit this@@18)) (=> (INTERNAL_lt_boogie 0 (|Seq#Length| (Lit (Test.QueryReceipt.lines (Lit this@@18))))) (and (and (and (|$IsA#Test.BetreeNode| (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Lit (Test.QueryReceipt.lines (Lit this@@18))) (LitInt 0))))) (|$IsA#Test.BetreeNode| (Lit (Test.QueryReceipt.root (Lit this@@18))))) (and (and (Test.QueryReceipt.QueryReceipt_q (Lit this@@18)) (Test.QueryReceiptLine.QueryReceiptLine_q ($Unbox DatatypeTypeType (|Seq#Index| (Lit (Test.QueryReceipt.lines (Lit this@@18))) (LitInt 0))))) (Test.QueryReceipt.QueryReceipt_q (Lit this@@18)))) (=> (|Test.BetreeNode#Equal| (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Lit (Test.QueryReceipt.lines (Lit this@@18))) (LitInt 0)))) (Test.QueryReceipt.root (Lit this@@18))) (forall ((|i#1| Int) ) (!  (=> (INTERNAL_le_boogie 0 |i#1|) (and (Test.QueryReceipt.QueryReceipt_q (Lit this@@18)) (=> (INTERNAL_lt_boogie |i#1| (|Seq#Length| (Lit (Test.QueryReceipt.lines (Lit this@@18))))) (and (and (Test.QueryReceipt.QueryReceipt_q (Lit this@@18)) (Test.QueryReceiptLine.QueryReceiptLine_q ($Unbox DatatypeTypeType (|Seq#Index| (Lit (Test.QueryReceipt.lines (Lit this@@18))) |i#1|)))) (Test.QueryReceipt.QueryReceipt_q (Lit this@@18))))))
 :qid |Testidfy.33:20|
 :skolemid |989|
 :pattern ( ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@18) |i#1|)))
)))))) (= (Test.QueryReceipt.Structure (Lit this@@18))  (and (and (INTERNAL_lt_boogie 0 (|Seq#Length| (Lit (Test.QueryReceipt.lines (Lit this@@18))))) (|Test.BetreeNode#Equal| (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Lit (Test.QueryReceipt.lines (Lit this@@18))) (LitInt 0)))) (Test.QueryReceipt.root (Lit this@@18)))) (forall ((|i#1@@0| Int) ) (!  (=> (and (INTERNAL_le_boogie 0 |i#1@@0|) (INTERNAL_lt_boogie |i#1@@0| (|Seq#Length| (Lit (Test.QueryReceipt.lines (Lit this@@18)))))) (= (Test.BetreeNode.BetreeNode_q (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Lit (Test.QueryReceipt.lines (Lit this@@18))) |i#1@@0|)))) (INTERNAL_lt_boogie |i#1@@0| (INTERNAL_sub_boogie (|Seq#Length| (Lit (Test.QueryReceipt.lines (Lit this@@18)))) 1))))
 :qid |Testidfy.33:20|
 :skolemid |988|
 :pattern ( ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@18) |i#1@@0|)))
))))))
 :qid |Testidfy.30:15|
 :weight 3
 :skolemid |990|
 :pattern ( (Test.QueryReceipt.Structure (Lit this@@18)))
))))
(assert  (=> (<= 7 $FunctionContextHeight) (forall ((this@@19 T@U) ) (!  (=> (and (= (type this@@19) DatatypeTypeType) (or (|Test.QueryReceipt.AllLinesWF#canCall| this@@19) (and (not (= 7 $FunctionContextHeight)) ($Is this@@19 Tclass.Test.QueryReceipt)))) true)
 :qid |Testidfy.36:15|
 :skolemid |993|
 :pattern ( (Test.QueryReceipt.AllLinesWF this@@19))
))))
(assert (forall ((this@@20 T@U) ) (!  (=> (and (= (type this@@20) DatatypeTypeType) ($Is this@@20 Tclass.Test.QueryReceipt)) (= (|Test.QueryReceipt.AllLinesWF#requires| this@@20) true))
 :qid |Testidfy.36:15|
 :skolemid |994|
 :pattern ( (|Test.QueryReceipt.AllLinesWF#requires| this@@20))
)))
(assert  (=> (<= 7 $FunctionContextHeight) (forall ((this@@21 T@U) ) (!  (=> (and (= (type this@@21) DatatypeTypeType) (or (|Test.QueryReceipt.AllLinesWF#canCall| this@@21) (and (not (= 7 $FunctionContextHeight)) ($Is this@@21 Tclass.Test.QueryReceipt)))) (and (=> (U_2_bool (Lit (bool_2_U true))) (forall ((|i#0@@1| Int) ) (!  (=> (INTERNAL_le_boogie 0 |i#0@@1|) (and (Test.QueryReceipt.QueryReceipt_q this@@21) (=> (INTERNAL_lt_boogie |i#0@@1| (|Seq#Length| (Test.QueryReceipt.lines this@@21))) (and (Test.QueryReceipt.QueryReceipt_q this@@21) (|Test.QueryReceiptLine.WF#canCall| ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@21) |i#0@@1|)))))))
 :qid |Testidfy.37:20|
 :skolemid |996|
 :pattern ( ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@21) |i#0@@1|)))
))) (= (Test.QueryReceipt.AllLinesWF this@@21)  (and true (forall ((|i#0@@2| Int) ) (!  (=> (and (INTERNAL_le_boogie 0 |i#0@@2|) (INTERNAL_lt_boogie |i#0@@2| (|Seq#Length| (Test.QueryReceipt.lines this@@21)))) (Test.QueryReceiptLine.WF ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@21) |i#0@@2|))))
 :qid |Testidfy.37:20|
 :skolemid |995|
 :pattern ( ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@21) |i#0@@2|)))
))))))
 :qid |Testidfy.36:15|
 :skolemid |997|
 :pattern ( (Test.QueryReceipt.AllLinesWF this@@21))
))))
(assert  (=> (<= 7 $FunctionContextHeight) (forall ((this@@22 T@U) ) (!  (=> (and (= (type this@@22) DatatypeTypeType) (or (|Test.QueryReceipt.AllLinesWF#canCall| (Lit this@@22)) (and (not (= 7 $FunctionContextHeight)) ($Is this@@22 Tclass.Test.QueryReceipt)))) (and (=> (U_2_bool (Lit (bool_2_U true))) (forall ((|i#1@@1| Int) ) (!  (=> (INTERNAL_le_boogie 0 |i#1@@1|) (and (Test.QueryReceipt.QueryReceipt_q (Lit this@@22)) (=> (INTERNAL_lt_boogie |i#1@@1| (|Seq#Length| (Lit (Test.QueryReceipt.lines (Lit this@@22))))) (and (Test.QueryReceipt.QueryReceipt_q (Lit this@@22)) (|Test.QueryReceiptLine.WF#canCall| ($Unbox DatatypeTypeType (|Seq#Index| (Lit (Test.QueryReceipt.lines (Lit this@@22))) |i#1@@1|)))))))
 :qid |Testidfy.37:20|
 :skolemid |999|
 :pattern ( ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@22) |i#1@@1|)))
))) (= (Test.QueryReceipt.AllLinesWF (Lit this@@22))  (and true (forall ((|i#1@@2| Int) ) (!  (=> (and (INTERNAL_le_boogie 0 |i#1@@2|) (INTERNAL_lt_boogie |i#1@@2| (|Seq#Length| (Lit (Test.QueryReceipt.lines (Lit this@@22)))))) (Test.QueryReceiptLine.WF ($Unbox DatatypeTypeType (|Seq#Index| (Lit (Test.QueryReceipt.lines (Lit this@@22))) |i#1@@2|))))
 :qid |Testidfy.37:20|
 :skolemid |998|
 :pattern ( ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@22) |i#1@@2|)))
))))))
 :qid |Testidfy.36:15|
 :weight 3
 :skolemid |1000|
 :pattern ( (Test.QueryReceipt.AllLinesWF (Lit this@@22)))
))))
(assert (forall ((arg0@@181 T@U) (arg1@@81 Int) ) (! (= (type (Test.QueryReceipt.ChildAt arg0@@181 arg1@@81)) DatatypeTypeType)
 :qid |funType:Test.QueryReceipt.ChildAt|
 :pattern ( (Test.QueryReceipt.ChildAt arg0@@181 arg1@@81))
)))
(assert  (=> (<= 9 $FunctionContextHeight) (forall ((this@@23 T@U) (|i#0@@3| Int) ) (!  (=> (and (= (type this@@23) DatatypeTypeType) (or (|Test.QueryReceipt.ChildAt#canCall| this@@23 |i#0@@3|) (and (not (= 9 $FunctionContextHeight)) (and (and ($Is this@@23 Tclass.Test.QueryReceipt) (INTERNAL_le_boogie 0 |i#0@@3|)) (and (and (Test.QueryReceipt.AllLinesWF this@@23) (Test.QueryReceipt.Structure this@@23)) (INTERNAL_lt_boogie |i#0@@3| (INTERNAL_sub_boogie (|Seq#Length| (Test.QueryReceipt.lines this@@23)) 1))))))) ($Is (Test.QueryReceipt.ChildAt this@@23 |i#0@@3|) Tclass.Test.BetreeNode))
 :qid |Testidfy.40:14|
 :skolemid |1004|
 :pattern ( (Test.QueryReceipt.ChildAt this@@23 |i#0@@3|))
))))
(assert (forall ((this@@24 T@U) (|i#0@@4| Int) ) (!  (=> (= (type this@@24) DatatypeTypeType) (=> (and ($Is this@@24 Tclass.Test.QueryReceipt) (INTERNAL_le_boogie 0 |i#0@@4|)) (= (|Test.QueryReceipt.ChildAt#requires| this@@24 |i#0@@4|)  (and (and (Test.QueryReceipt.AllLinesWF this@@24) (Test.QueryReceipt.Structure this@@24)) (INTERNAL_lt_boogie |i#0@@4| (INTERNAL_sub_boogie (|Seq#Length| (Test.QueryReceipt.lines this@@24)) 1))))))
 :qid |Testidfy.40:14|
 :skolemid |1005|
 :pattern ( (|Test.QueryReceipt.ChildAt#requires| this@@24 |i#0@@4|))
)))
(assert  (=> (<= 9 $FunctionContextHeight) (forall ((this@@25 T@U) (|i#0@@5| Int) ) (!  (=> (and (= (type this@@25) DatatypeTypeType) (or (|Test.QueryReceipt.ChildAt#canCall| this@@25 |i#0@@5|) (and (not (= 9 $FunctionContextHeight)) (and (and ($Is this@@25 Tclass.Test.QueryReceipt) (INTERNAL_le_boogie 0 |i#0@@5|)) (and (and (Test.QueryReceipt.AllLinesWF this@@25) (Test.QueryReceipt.Structure this@@25)) (INTERNAL_lt_boogie |i#0@@5| (INTERNAL_sub_boogie (|Seq#Length| (Test.QueryReceipt.lines this@@25)) 1))))))) (and (and (and (and (Test.QueryReceipt.QueryReceipt_q this@@25) (Test.QueryReceiptLine.QueryReceiptLine_q ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@25) |i#0@@5|)))) (Test.ChildMap.ChildMap_q (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@25) |i#0@@5|)))))) (Test.QueryReceipt.QueryReceipt_q this@@25)) (= (Test.QueryReceipt.ChildAt this@@25 |i#0@@5|) ($Unbox DatatypeTypeType (MapType0Select (|IMap#Elements| (Test.ChildMap.mapp (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@25) |i#0@@5|)))))) ($Box (Test.QueryReceipt.key this@@25)))))))
 :qid |Testidfy.40:14|
 :skolemid |1006|
 :pattern ( (Test.QueryReceipt.ChildAt this@@25 |i#0@@5|))
))))
(assert  (=> (<= 9 $FunctionContextHeight) (forall ((this@@26 T@U) (|i#0@@6| Int) ) (!  (=> (and (= (type this@@26) DatatypeTypeType) (or (|Test.QueryReceipt.ChildAt#canCall| (Lit this@@26) (LitInt |i#0@@6|)) (and (not (= 9 $FunctionContextHeight)) (and (and ($Is this@@26 Tclass.Test.QueryReceipt) (INTERNAL_le_boogie 0 |i#0@@6|)) (and (and (U_2_bool (Lit (bool_2_U (Test.QueryReceipt.AllLinesWF (Lit this@@26))))) (U_2_bool (Lit (bool_2_U (Test.QueryReceipt.Structure (Lit this@@26)))))) (INTERNAL_lt_boogie |i#0@@6| (INTERNAL_sub_boogie (|Seq#Length| (Lit (Test.QueryReceipt.lines (Lit this@@26)))) 1))))))) (and (and (and (and (Test.QueryReceipt.QueryReceipt_q (Lit this@@26)) (Test.QueryReceiptLine.QueryReceiptLine_q ($Unbox DatatypeTypeType (|Seq#Index| (Lit (Test.QueryReceipt.lines (Lit this@@26))) (LitInt |i#0@@6|))))) (Test.ChildMap.ChildMap_q (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Lit (Test.QueryReceipt.lines (Lit this@@26))) (LitInt |i#0@@6|))))))) (Test.QueryReceipt.QueryReceipt_q (Lit this@@26))) (= (Test.QueryReceipt.ChildAt (Lit this@@26) (LitInt |i#0@@6|)) ($Unbox DatatypeTypeType (MapType0Select (|IMap#Elements| (Test.ChildMap.mapp (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Lit (Test.QueryReceipt.lines (Lit this@@26))) (LitInt |i#0@@6|))))))) ($Box (Lit (Test.QueryReceipt.key (Lit this@@26)))))))))
 :qid |Testidfy.40:14|
 :weight 3
 :skolemid |1007|
 :pattern ( (Test.QueryReceipt.ChildAt (Lit this@@26) (LitInt |i#0@@6|)))
))))
(assert (= (type Tclass.Test.__default) TyType))
(assert (= (Tag Tclass.Test.__default) Tagclass.Test.__default))
(assert (= (TagFamily Tclass.Test.__default) tytagFamily$_default))
(assert (forall ((bx@@58 T@U) ) (!  (=> (and (= (type bx@@58) BoxType) ($IsBox bx@@58 Tclass.Test.__default)) (and (= ($Box ($Unbox refType bx@@58)) bx@@58) ($Is ($Unbox refType bx@@58) Tclass.Test.__default)))
 :qid |unknown.0:0|
 :skolemid |1010|
 :pattern ( ($IsBox bx@@58 Tclass.Test.__default))
)))
(assert (forall (($o@@9 T@U) ) (!  (=> (= (type $o@@9) refType) (= ($Is $o@@9 Tclass.Test.__default)  (or (= $o@@9 null) (= (dtype $o@@9) Tclass.Test.__default))))
 :qid |unknown.0:0|
 :skolemid |1011|
 :pattern ( ($Is $o@@9 Tclass.Test.__default))
)))
(assert (forall (($o@@10 T@U) ($h@@29 T@U) ) (!  (=> (and (= (type $o@@10) refType) (= (type $h@@29) (MapType0Type refType MapType1Type))) (= ($IsAlloc $o@@10 Tclass.Test.__default $h@@29)  (or (= $o@@10 null) (U_2_bool (MapType1Select (MapType0Select $h@@29 $o@@10) alloc)))))
 :qid |unknown.0:0|
 :skolemid |1012|
 :pattern ( ($IsAlloc $o@@10 Tclass.Test.__default $h@@29))
)))
(assert (= (type Tclass.Common.byte) TyType))
(assert (= (Tag Tclass.Common.byte) Tagclass.Common.byte))
(assert (= (TagFamily Tclass.Common.byte) tytagFamily$byte))
(assert (forall ((bx@@59 T@U) ) (!  (=> (and (= (type bx@@59) BoxType) ($IsBox bx@@59 Tclass.Common.byte)) (and (= ($Box ($Unbox intType bx@@59)) bx@@59) ($Is ($Unbox intType bx@@59) Tclass.Common.byte)))
 :qid |unknown.0:0|
 :skolemid |1013|
 :pattern ( ($IsBox bx@@59 Tclass.Common.byte))
)))
(assert (forall ((|i#0@@7| T@U) ) (!  (=> (= (type |i#0@@7|) intType) (= ($Is |i#0@@7| Tclass.Common.byte)  (and (INTERNAL_le_boogie 0 (U_2_int |i#0@@7|)) (INTERNAL_lt_boogie (U_2_int |i#0@@7|) 256))))
 :qid |unknown.0:0|
 :skolemid |1014|
 :pattern ( ($Is |i#0@@7| Tclass.Common.byte))
)))
(assert (forall ((|i#0@@8| T@U) ($h@@30 T@U) ) (!  (=> (and (= (type |i#0@@8|) intType) (= (type $h@@30) (MapType0Type refType MapType1Type))) ($IsAlloc |i#0@@8| Tclass.Common.byte $h@@30))
 :qid |unknown.0:0|
 :skolemid |1015|
 :pattern ( ($IsAlloc |i#0@@8| Tclass.Common.byte $h@@30))
)))
(assert (forall ((|s#0| T@U) ) (!  (=> (= (type |s#0|) (SeqType BoxType)) (= ($Is |s#0| Tclass.Common.Key)  (and ($Is |s#0| (TSeq Tclass.Common.byte)) (INTERNAL_le_boogie (|Seq#Length| |s#0|) 1024))))
 :qid |unknown.0:0|
 :skolemid |1016|
 :pattern ( ($Is |s#0| Tclass.Common.Key))
)))
(assert (forall ((|s#0@@0| T@U) ($h@@31 T@U) ) (!  (=> (and (= (type |s#0@@0|) (SeqType BoxType)) (= (type $h@@31) (MapType0Type refType MapType1Type))) (= ($IsAlloc |s#0@@0| Tclass.Common.Key $h@@31) ($IsAlloc |s#0@@0| (TSeq Tclass.Common.byte) $h@@31)))
 :qid |unknown.0:0|
 :skolemid |1017|
 :pattern ( ($IsAlloc |s#0@@0| Tclass.Common.Key $h@@31))
)))
(assert (= (type Tclass.Common.__default) TyType))
(assert (= (Tag Tclass.Common.__default) Tagclass.Common.__default))
(assert (= (TagFamily Tclass.Common.__default) tytagFamily$_default))
(assert (forall ((bx@@60 T@U) ) (!  (=> (and (= (type bx@@60) BoxType) ($IsBox bx@@60 Tclass.Common.__default)) (and (= ($Box ($Unbox refType bx@@60)) bx@@60) ($Is ($Unbox refType bx@@60) Tclass.Common.__default)))
 :qid |unknown.0:0|
 :skolemid |1018|
 :pattern ( ($IsBox bx@@60 Tclass.Common.__default))
)))
(assert (forall (($o@@11 T@U) ) (!  (=> (= (type $o@@11) refType) (= ($Is $o@@11 Tclass.Common.__default)  (or (= $o@@11 null) (= (dtype $o@@11) Tclass.Common.__default))))
 :qid |unknown.0:0|
 :skolemid |1019|
 :pattern ( ($Is $o@@11 Tclass.Common.__default))
)))
(assert (forall (($o@@12 T@U) ($h@@32 T@U) ) (!  (=> (and (= (type $o@@12) refType) (= (type $h@@32) (MapType0Type refType MapType1Type))) (= ($IsAlloc $o@@12 Tclass.Common.__default $h@@32)  (or (= $o@@12 null) (U_2_bool (MapType1Select (MapType0Select $h@@32 $o@@12) alloc)))))
 :qid |unknown.0:0|
 :skolemid |1020|
 :pattern ( ($IsAlloc $o@@12 Tclass.Common.__default $h@@32))
)))
(assert  (=> true (forall ((|key#0| T@U) ) (!  (=> (and (= (type |key#0|) (SeqType BoxType)) (or (|Common.__default.AnyKey#canCall| |key#0|) ($Is |key#0| Tclass.Common.Key))) true)
 :qid |Commonidfy.6:18|
 :skolemid |1021|
 :pattern ( (Common.__default.AnyKey |key#0|))
))))
(assert (forall ((|key#0@@0| T@U) ) (!  (=> (and (= (type |key#0@@0|) (SeqType BoxType)) ($Is |key#0@@0| Tclass.Common.Key)) (= (|Common.__default.AnyKey#requires| |key#0@@0|) true))
 :qid |Commonidfy.6:18|
 :skolemid |1022|
 :pattern ( (|Common.__default.AnyKey#requires| |key#0@@0|))
)))
(assert  (=> true (forall ((|key#0@@1| T@U) ) (!  (=> (and (= (type |key#0@@1|) (SeqType BoxType)) (or (|Common.__default.AnyKey#canCall| |key#0@@1|) ($Is |key#0@@1| Tclass.Common.Key))) (= (Common.__default.AnyKey |key#0@@1|) (U_2_bool (Lit (bool_2_U true)))))
 :qid |Commonidfy.6:18|
 :skolemid |1023|
 :pattern ( (Common.__default.AnyKey |key#0@@1|))
))))
(assert  (=> true (forall ((|key#0@@2| T@U) ) (!  (=> (and (= (type |key#0@@2|) (SeqType BoxType)) (or (|Common.__default.AnyKey#canCall| (Lit |key#0@@2|)) ($Is |key#0@@2| Tclass.Common.Key))) (= (Common.__default.AnyKey (Lit |key#0@@2|)) (U_2_bool (Lit (bool_2_U true)))))
 :qid |Commonidfy.6:18|
 :weight 3
 :skolemid |1024|
 :pattern ( (Common.__default.AnyKey (Lit |key#0@@2|)))
))))
(assert  (=> true (forall ((|keys#0| T@U) ) (!  (=> (and (= (type |keys#0|) (MapType0Type BoxType boolType)) (or (|Common.__default.TotalSet#canCall| |keys#0|) ($Is |keys#0| (TISet Tclass.Common.Key)))) true)
 :qid |Commonidfy.10:20|
 :skolemid |1025|
 :pattern ( (Common.__default.TotalSet |keys#0|))
))))
(assert (forall ((|keys#0@@0| T@U) ) (!  (=> (and (= (type |keys#0@@0|) (MapType0Type BoxType boolType)) ($Is |keys#0@@0| (TISet Tclass.Common.Key))) (= (|Common.__default.TotalSet#requires| |keys#0@@0|) true))
 :qid |Commonidfy.10:20|
 :skolemid |1026|
 :pattern ( (|Common.__default.TotalSet#requires| |keys#0@@0|))
)))
(assert  (=> true (forall ((|keys#0@@1| T@U) ) (!  (=> (and (= (type |keys#0@@1|) (MapType0Type BoxType boolType)) (or (|Common.__default.TotalSet#canCall| |keys#0@@1|) ($Is |keys#0@@1| (TISet Tclass.Common.Key)))) (and (forall ((|k#0@@1| T@U) ) (!  (=> (and (= (type |k#0@@1|) (SeqType BoxType)) ($Is |k#0@@1| Tclass.Common.Key)) (|Common.__default.AnyKey#canCall| |k#0@@1|))
 :qid |Commonidfy.11:12|
 :skolemid |1028|
 :pattern ( (MapType0Select |keys#0@@1| ($Box |k#0@@1|)))
 :pattern ( (Common.__default.AnyKey |k#0@@1|))
)) (= (Common.__default.TotalSet |keys#0@@1|) (forall ((|k#0@@2| T@U) ) (!  (=> (= (type |k#0@@2|) (SeqType BoxType)) (=> (and ($Is |k#0@@2| Tclass.Common.Key) (Common.__default.AnyKey |k#0@@2|)) (U_2_bool (MapType0Select |keys#0@@1| ($Box |k#0@@2|)))))
 :qid |Commonidfy.11:12|
 :skolemid |1027|
 :pattern ( (MapType0Select |keys#0@@1| ($Box |k#0@@2|)))
 :pattern ( (Common.__default.AnyKey |k#0@@2|))
)))))
 :qid |Commonidfy.10:20|
 :skolemid |1029|
 :pattern ( (Common.__default.TotalSet |keys#0@@1|))
))))
(assert  (=> true (forall ((|keys#0@@2| T@U) ) (!  (=> (and (= (type |keys#0@@2|) (MapType0Type BoxType boolType)) (or (|Common.__default.TotalSet#canCall| (Lit |keys#0@@2|)) ($Is |keys#0@@2| (TISet Tclass.Common.Key)))) (and (forall ((|k#1@@1| T@U) ) (!  (=> (and (= (type |k#1@@1|) (SeqType BoxType)) ($Is |k#1@@1| Tclass.Common.Key)) (|Common.__default.AnyKey#canCall| |k#1@@1|))
 :qid |Commonidfy.11:12|
 :skolemid |1031|
 :pattern ( (MapType0Select |keys#0@@2| ($Box |k#1@@1|)))
 :pattern ( (Common.__default.AnyKey |k#1@@1|))
)) (= (Common.__default.TotalSet (Lit |keys#0@@2|)) (forall ((|k#1@@2| T@U) ) (!  (=> (= (type |k#1@@2|) (SeqType BoxType)) (=> (and ($Is |k#1@@2| Tclass.Common.Key) (Common.__default.AnyKey |k#1@@2|)) (U_2_bool (MapType0Select (Lit |keys#0@@2|) ($Box |k#1@@2|)))))
 :qid |Commonidfy.11:12|
 :skolemid |1030|
 :pattern ( (MapType0Select |keys#0@@2| ($Box |k#1@@2|)))
 :pattern ( (Common.__default.AnyKey |k#1@@2|))
)))))
 :qid |Commonidfy.10:20|
 :weight 3
 :skolemid |1032|
 :pattern ( (Common.__default.TotalSet (Lit |keys#0@@2|)))
))))
(assert  (and (and (and (and (and (and (and (forall ((arg0@@182 T@T) (arg1@@82 T@T) ) (! (= (Ctor (MapType4Type arg0@@182 arg1@@82)) 26)
 :qid |ctor:MapType4Type|
)) (forall ((arg0@@183 T@T) (arg1@@83 T@T) ) (! (= (MapType4TypeInv0 (MapType4Type arg0@@183 arg1@@83)) arg0@@183)
 :qid |typeInv:MapType4TypeInv0|
 :pattern ( (MapType4Type arg0@@183 arg1@@83))
))) (forall ((arg0@@184 T@T) (arg1@@84 T@T) ) (! (= (MapType4TypeInv1 (MapType4Type arg0@@184 arg1@@84)) arg1@@84)
 :qid |typeInv:MapType4TypeInv1|
 :pattern ( (MapType4Type arg0@@184 arg1@@84))
))) (forall ((arg0@@185 T@U) (arg1@@85 T@U) (arg2@@33 T@U) ) (! (let ((aVar1@@4 (MapType4TypeInv1 (type arg0@@185))))
(= (type (MapType4Select arg0@@185 arg1@@85 arg2@@33)) aVar1@@4))
 :qid |funType:MapType4Select|
 :pattern ( (MapType4Select arg0@@185 arg1@@85 arg2@@33))
))) (forall ((arg0@@186 T@U) (arg1@@86 T@U) (arg2@@34 T@U) (arg3@@12 T@U) ) (! (let ((aVar1@@5 (type arg3@@12)))
(let ((aVar0@@2 (type arg1@@86)))
(= (type (MapType4Store arg0@@186 arg1@@86 arg2@@34 arg3@@12)) (MapType4Type aVar0@@2 aVar1@@5))))
 :qid |funType:MapType4Store|
 :pattern ( (MapType4Store arg0@@186 arg1@@86 arg2@@34 arg3@@12))
))) (forall ((m@@54 T@U) (x0@@14 T@U) (x1@@8 T@U) (val@@15 T@U) ) (! (let ((aVar1@@6 (MapType4TypeInv1 (type m@@54))))
 (=> (= (type val@@15) aVar1@@6) (= (MapType4Select (MapType4Store m@@54 x0@@14 x1@@8 val@@15) x0@@14 x1@@8) val@@15)))
 :qid |mapAx0:MapType4Select|
 :weight 0
))) (and (and (forall ((val@@16 T@U) (m@@55 T@U) (x0@@15 T@U) (x1@@9 T@U) (y0@@10 T@U) (y1@@6 T@U) ) (!  (or (= x0@@15 y0@@10) (= (MapType4Select (MapType4Store m@@55 x0@@15 x1@@9 val@@16) y0@@10 y1@@6) (MapType4Select m@@55 y0@@10 y1@@6)))
 :qid |mapAx1:MapType4Select:0|
 :weight 0
)) (forall ((val@@17 T@U) (m@@56 T@U) (x0@@16 T@U) (x1@@10 T@U) (y0@@11 T@U) (y1@@7 T@U) ) (!  (or (= x1@@10 y1@@7) (= (MapType4Select (MapType4Store m@@56 x0@@16 x1@@10 val@@17) y0@@11 y1@@7) (MapType4Select m@@56 y0@@11 y1@@7)))
 :qid |mapAx1:MapType4Select:1|
 :weight 0
))) (forall ((val@@18 T@U) (m@@57 T@U) (x0@@17 T@U) (x1@@11 T@U) (y0@@12 T@U) (y1@@8 T@U) ) (!  (or true (= (MapType4Select (MapType4Store m@@57 x0@@17 x1@@11 val@@18) y0@@12 y1@@8) (MapType4Select m@@57 y0@@12 y1@@8)))
 :qid |mapAx2:MapType4Select|
 :weight 0
)))) (forall ((arg0@@187 T@U) (arg1@@87 T@U) (arg2@@35 T@U) (arg3@@13 Bool) ) (! (= (type (|lambda#0| arg0@@187 arg1@@87 arg2@@35 arg3@@13)) (MapType4Type refType boolType))
 :qid |funType:lambda#0|
 :pattern ( (|lambda#0| arg0@@187 arg1@@87 arg2@@35 arg3@@13))
))))
(assert (forall ((|l#0| T@U) (|l#1| T@U) (|l#2| T@U) (|l#3| Bool) ($o@@13 T@U) ($f T@U) ) (! (let ((alpha@@6 (FieldTypeInv0 (type $f))))
 (=> (and (and (and (and (= (type |l#0|) refType) (= (type |l#1|) (MapType0Type refType MapType1Type))) (= (type |l#2|) (FieldType boolType))) (= (type $o@@13) refType)) (= (type $f) (FieldType alpha@@6))) (= (U_2_bool (MapType4Select (|lambda#0| |l#0| |l#1| |l#2| |l#3|) $o@@13 $f))  (=> (and (not (= $o@@13 |l#0|)) (U_2_bool (MapType1Select (MapType0Select |l#1| $o@@13) |l#2|))) |l#3|))))
 :qid |DafnyPreludebpl.129:1|
 :skolemid |1033|
 :pattern ( (MapType4Select (|lambda#0| |l#0| |l#1| |l#2| |l#3|) $o@@13 $f))
)))
(assert (forall ((arg0@@188 T@U) (arg1@@88 T@U) (arg2@@36 T@U) (arg3@@14 Bool) ) (! (= (type (|lambda#1| arg0@@188 arg1@@88 arg2@@36 arg3@@14)) (MapType4Type refType boolType))
 :qid |funType:lambda#1|
 :pattern ( (|lambda#1| arg0@@188 arg1@@88 arg2@@36 arg3@@14))
)))
(assert (forall ((|l#0@@0| T@U) (|l#1@@0| T@U) (|l#2@@0| T@U) (|l#3@@0| Bool) ($o@@14 T@U) ($f@@0 T@U) ) (! (let ((alpha@@7 (FieldTypeInv0 (type $f@@0))))
 (=> (and (and (and (and (= (type |l#0@@0|) refType) (= (type |l#1@@0|) (MapType0Type refType MapType1Type))) (= (type |l#2@@0|) (FieldType boolType))) (= (type $o@@14) refType)) (= (type $f@@0) (FieldType alpha@@7))) (= (U_2_bool (MapType4Select (|lambda#1| |l#0@@0| |l#1@@0| |l#2@@0| |l#3@@0|) $o@@14 $f@@0))  (=> (and (not (= $o@@14 |l#0@@0|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@0| $o@@14) |l#2@@0|))) |l#3@@0|))))
 :qid |DafnyPreludebpl.129:1|
 :skolemid |1034|
 :pattern ( (MapType4Select (|lambda#1| |l#0@@0| |l#1@@0| |l#2@@0| |l#3@@0|) $o@@14 $f@@0))
)))
(assert (forall ((arg0@@189 T@U) (arg1@@89 T@U) (arg2@@37 T@U) (arg3@@15 Bool) ) (! (= (type (|lambda#2| arg0@@189 arg1@@89 arg2@@37 arg3@@15)) (MapType4Type refType boolType))
 :qid |funType:lambda#2|
 :pattern ( (|lambda#2| arg0@@189 arg1@@89 arg2@@37 arg3@@15))
)))
(assert (forall ((|l#0@@1| T@U) (|l#1@@1| T@U) (|l#2@@1| T@U) (|l#3@@1| Bool) ($o@@15 T@U) ($f@@1 T@U) ) (! (let ((alpha@@8 (FieldTypeInv0 (type $f@@1))))
 (=> (and (and (and (and (= (type |l#0@@1|) refType) (= (type |l#1@@1|) (MapType0Type refType MapType1Type))) (= (type |l#2@@1|) (FieldType boolType))) (= (type $o@@15) refType)) (= (type $f@@1) (FieldType alpha@@8))) (= (U_2_bool (MapType4Select (|lambda#2| |l#0@@1| |l#1@@1| |l#2@@1| |l#3@@1|) $o@@15 $f@@1))  (=> (and (not (= $o@@15 |l#0@@1|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@1| $o@@15) |l#2@@1|))) |l#3@@1|))))
 :qid |DafnyPreludebpl.129:1|
 :skolemid |1035|
 :pattern ( (MapType4Select (|lambda#2| |l#0@@1| |l#1@@1| |l#2@@1| |l#3@@1|) $o@@15 $f@@1))
)))
(assert (forall ((arg0@@190 T@U) (arg1@@90 T@U) (arg2@@38 T@U) (arg3@@16 Bool) ) (! (= (type (|lambda#3| arg0@@190 arg1@@90 arg2@@38 arg3@@16)) (MapType4Type refType boolType))
 :qid |funType:lambda#3|
 :pattern ( (|lambda#3| arg0@@190 arg1@@90 arg2@@38 arg3@@16))
)))
(assert (forall ((|l#0@@2| T@U) (|l#1@@2| T@U) (|l#2@@2| T@U) (|l#3@@2| Bool) ($o@@16 T@U) ($f@@2 T@U) ) (! (let ((alpha@@9 (FieldTypeInv0 (type $f@@2))))
 (=> (and (and (and (and (= (type |l#0@@2|) refType) (= (type |l#1@@2|) (MapType0Type refType MapType1Type))) (= (type |l#2@@2|) (FieldType boolType))) (= (type $o@@16) refType)) (= (type $f@@2) (FieldType alpha@@9))) (= (U_2_bool (MapType4Select (|lambda#3| |l#0@@2| |l#1@@2| |l#2@@2| |l#3@@2|) $o@@16 $f@@2))  (=> (and (not (= $o@@16 |l#0@@2|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@2| $o@@16) |l#2@@2|))) |l#3@@2|))))
 :qid |DafnyPreludebpl.129:1|
 :skolemid |1036|
 :pattern ( (MapType4Select (|lambda#3| |l#0@@2| |l#1@@2| |l#2@@2| |l#3@@2|) $o@@16 $f@@2))
)))
(assert (forall ((arg0@@191 T@U) (arg1@@91 T@U) (arg2@@39 T@U) (arg3@@17 Bool) ) (! (= (type (|lambda#4| arg0@@191 arg1@@91 arg2@@39 arg3@@17)) (MapType4Type refType boolType))
 :qid |funType:lambda#4|
 :pattern ( (|lambda#4| arg0@@191 arg1@@91 arg2@@39 arg3@@17))
)))
(assert (forall ((|l#0@@3| T@U) (|l#1@@3| T@U) (|l#2@@3| T@U) (|l#3@@3| Bool) ($o@@17 T@U) ($f@@3 T@U) ) (! (let ((alpha@@10 (FieldTypeInv0 (type $f@@3))))
 (=> (and (and (and (and (= (type |l#0@@3|) refType) (= (type |l#1@@3|) (MapType0Type refType MapType1Type))) (= (type |l#2@@3|) (FieldType boolType))) (= (type $o@@17) refType)) (= (type $f@@3) (FieldType alpha@@10))) (= (U_2_bool (MapType4Select (|lambda#4| |l#0@@3| |l#1@@3| |l#2@@3| |l#3@@3|) $o@@17 $f@@3))  (=> (and (not (= $o@@17 |l#0@@3|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@3| $o@@17) |l#2@@3|))) |l#3@@3|))))
 :qid |DafnyPreludebpl.129:1|
 :skolemid |1037|
 :pattern ( (MapType4Select (|lambda#4| |l#0@@3| |l#1@@3| |l#2@@3| |l#3@@3|) $o@@17 $f@@3))
)))
(assert (forall ((arg0@@192 T@U) (arg1@@92 T@U) (arg2@@40 T@U) (arg3@@18 Bool) ) (! (= (type (|lambda#5| arg0@@192 arg1@@92 arg2@@40 arg3@@18)) (MapType4Type refType boolType))
 :qid |funType:lambda#5|
 :pattern ( (|lambda#5| arg0@@192 arg1@@92 arg2@@40 arg3@@18))
)))
(assert (forall ((|l#0@@4| T@U) (|l#1@@4| T@U) (|l#2@@4| T@U) (|l#3@@4| Bool) ($o@@18 T@U) ($f@@4 T@U) ) (! (let ((alpha@@11 (FieldTypeInv0 (type $f@@4))))
 (=> (and (and (and (and (= (type |l#0@@4|) refType) (= (type |l#1@@4|) (MapType0Type refType MapType1Type))) (= (type |l#2@@4|) (FieldType boolType))) (= (type $o@@18) refType)) (= (type $f@@4) (FieldType alpha@@11))) (= (U_2_bool (MapType4Select (|lambda#5| |l#0@@4| |l#1@@4| |l#2@@4| |l#3@@4|) $o@@18 $f@@4))  (=> (and (not (= $o@@18 |l#0@@4|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@4| $o@@18) |l#2@@4|))) |l#3@@4|))))
 :qid |DafnyPreludebpl.129:1|
 :skolemid |1038|
 :pattern ( (MapType4Select (|lambda#5| |l#0@@4| |l#1@@4| |l#2@@4| |l#3@@4|) $o@@18 $f@@4))
)))
(assert (forall ((arg0@@193 T@U) (arg1@@93 T@U) (arg2@@41 T@U) (arg3@@19 Bool) ) (! (= (type (|lambda#6| arg0@@193 arg1@@93 arg2@@41 arg3@@19)) (MapType4Type refType boolType))
 :qid |funType:lambda#6|
 :pattern ( (|lambda#6| arg0@@193 arg1@@93 arg2@@41 arg3@@19))
)))
(assert (forall ((|l#0@@5| T@U) (|l#1@@5| T@U) (|l#2@@5| T@U) (|l#3@@5| Bool) ($o@@19 T@U) ($f@@5 T@U) ) (! (let ((alpha@@12 (FieldTypeInv0 (type $f@@5))))
 (=> (and (and (and (and (= (type |l#0@@5|) refType) (= (type |l#1@@5|) (MapType0Type refType MapType1Type))) (= (type |l#2@@5|) (FieldType boolType))) (= (type $o@@19) refType)) (= (type $f@@5) (FieldType alpha@@12))) (= (U_2_bool (MapType4Select (|lambda#6| |l#0@@5| |l#1@@5| |l#2@@5| |l#3@@5|) $o@@19 $f@@5))  (=> (and (not (= $o@@19 |l#0@@5|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@5| $o@@19) |l#2@@5|))) |l#3@@5|))))
 :qid |DafnyPreludebpl.129:1|
 :skolemid |1039|
 :pattern ( (MapType4Select (|lambda#6| |l#0@@5| |l#1@@5| |l#2@@5| |l#3@@5|) $o@@19 $f@@5))
)))
(assert (forall ((arg0@@194 T@U) (arg1@@94 T@U) (arg2@@42 T@U) (arg3@@20 Bool) ) (! (= (type (|lambda#7| arg0@@194 arg1@@94 arg2@@42 arg3@@20)) (MapType4Type refType boolType))
 :qid |funType:lambda#7|
 :pattern ( (|lambda#7| arg0@@194 arg1@@94 arg2@@42 arg3@@20))
)))
(assert (forall ((|l#0@@6| T@U) (|l#1@@6| T@U) (|l#2@@6| T@U) (|l#3@@6| Bool) ($o@@20 T@U) ($f@@6 T@U) ) (! (let ((alpha@@13 (FieldTypeInv0 (type $f@@6))))
 (=> (and (and (and (and (= (type |l#0@@6|) refType) (= (type |l#1@@6|) (MapType0Type refType MapType1Type))) (= (type |l#2@@6|) (FieldType boolType))) (= (type $o@@20) refType)) (= (type $f@@6) (FieldType alpha@@13))) (= (U_2_bool (MapType4Select (|lambda#7| |l#0@@6| |l#1@@6| |l#2@@6| |l#3@@6|) $o@@20 $f@@6))  (=> (and (not (= $o@@20 |l#0@@6|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@6| $o@@20) |l#2@@6|))) |l#3@@6|))))
 :qid |DafnyPreludebpl.129:1|
 :skolemid |1040|
 :pattern ( (MapType4Select (|lambda#7| |l#0@@6| |l#1@@6| |l#2@@6| |l#3@@6|) $o@@20 $f@@6))
)))
(assert (forall ((arg0@@195 T@U) (arg1@@95 T@U) (arg2@@43 T@U) (arg3@@21 Bool) ) (! (= (type (|lambda#8| arg0@@195 arg1@@95 arg2@@43 arg3@@21)) (MapType4Type refType boolType))
 :qid |funType:lambda#8|
 :pattern ( (|lambda#8| arg0@@195 arg1@@95 arg2@@43 arg3@@21))
)))
(assert (forall ((|l#0@@7| T@U) (|l#1@@7| T@U) (|l#2@@7| T@U) (|l#3@@7| Bool) ($o@@21 T@U) ($f@@7 T@U) ) (! (let ((alpha@@14 (FieldTypeInv0 (type $f@@7))))
 (=> (and (and (and (and (= (type |l#0@@7|) refType) (= (type |l#1@@7|) (MapType0Type refType MapType1Type))) (= (type |l#2@@7|) (FieldType boolType))) (= (type $o@@21) refType)) (= (type $f@@7) (FieldType alpha@@14))) (= (U_2_bool (MapType4Select (|lambda#8| |l#0@@7| |l#1@@7| |l#2@@7| |l#3@@7|) $o@@21 $f@@7))  (=> (and (not (= $o@@21 |l#0@@7|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@7| $o@@21) |l#2@@7|))) |l#3@@7|))))
 :qid |DafnyPreludebpl.129:1|
 :skolemid |1041|
 :pattern ( (MapType4Select (|lambda#8| |l#0@@7| |l#1@@7| |l#2@@7| |l#3@@7|) $o@@21 $f@@7))
)))
(assert (forall ((arg0@@196 T@U) (arg1@@96 T@U) (arg2@@44 T@U) (arg3@@22 Bool) ) (! (= (type (|lambda#9| arg0@@196 arg1@@96 arg2@@44 arg3@@22)) (MapType4Type refType boolType))
 :qid |funType:lambda#9|
 :pattern ( (|lambda#9| arg0@@196 arg1@@96 arg2@@44 arg3@@22))
)))
(assert (forall ((|l#0@@8| T@U) (|l#1@@8| T@U) (|l#2@@8| T@U) (|l#3@@8| Bool) ($o@@22 T@U) ($f@@8 T@U) ) (! (let ((alpha@@15 (FieldTypeInv0 (type $f@@8))))
 (=> (and (and (and (and (= (type |l#0@@8|) refType) (= (type |l#1@@8|) (MapType0Type refType MapType1Type))) (= (type |l#2@@8|) (FieldType boolType))) (= (type $o@@22) refType)) (= (type $f@@8) (FieldType alpha@@15))) (= (U_2_bool (MapType4Select (|lambda#9| |l#0@@8| |l#1@@8| |l#2@@8| |l#3@@8|) $o@@22 $f@@8))  (=> (and (not (= $o@@22 |l#0@@8|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@8| $o@@22) |l#2@@8|))) |l#3@@8|))))
 :qid |DafnyPreludebpl.129:1|
 :skolemid |1042|
 :pattern ( (MapType4Select (|lambda#9| |l#0@@8| |l#1@@8| |l#2@@8| |l#3@@8|) $o@@22 $f@@8))
)))
(assert (forall ((arg0@@197 T@U) (arg1@@97 T@U) (arg2@@45 T@U) (arg3@@23 Bool) ) (! (= (type (|lambda#10| arg0@@197 arg1@@97 arg2@@45 arg3@@23)) (MapType4Type refType boolType))
 :qid |funType:lambda#10|
 :pattern ( (|lambda#10| arg0@@197 arg1@@97 arg2@@45 arg3@@23))
)))
(assert (forall ((|l#0@@9| T@U) (|l#1@@9| T@U) (|l#2@@9| T@U) (|l#3@@9| Bool) ($o@@23 T@U) ($f@@9 T@U) ) (! (let ((alpha@@16 (FieldTypeInv0 (type $f@@9))))
 (=> (and (and (and (and (= (type |l#0@@9|) refType) (= (type |l#1@@9|) (MapType0Type refType MapType1Type))) (= (type |l#2@@9|) (FieldType boolType))) (= (type $o@@23) refType)) (= (type $f@@9) (FieldType alpha@@16))) (= (U_2_bool (MapType4Select (|lambda#10| |l#0@@9| |l#1@@9| |l#2@@9| |l#3@@9|) $o@@23 $f@@9))  (=> (and (not (= $o@@23 |l#0@@9|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@9| $o@@23) |l#2@@9|))) |l#3@@9|))))
 :qid |DafnyPreludebpl.129:1|
 :skolemid |1043|
 :pattern ( (MapType4Select (|lambda#10| |l#0@@9| |l#1@@9| |l#2@@9| |l#3@@9|) $o@@23 $f@@9))
)))
(assert (forall ((arg0@@198 T@U) (arg1@@98 T@U) (arg2@@46 T@U) (arg3@@24 Bool) ) (! (= (type (|lambda#11| arg0@@198 arg1@@98 arg2@@46 arg3@@24)) (MapType4Type refType boolType))
 :qid |funType:lambda#11|
 :pattern ( (|lambda#11| arg0@@198 arg1@@98 arg2@@46 arg3@@24))
)))
(assert (forall ((|l#0@@10| T@U) (|l#1@@10| T@U) (|l#2@@10| T@U) (|l#3@@10| Bool) ($o@@24 T@U) ($f@@10 T@U) ) (! (let ((alpha@@17 (FieldTypeInv0 (type $f@@10))))
 (=> (and (and (and (and (= (type |l#0@@10|) refType) (= (type |l#1@@10|) (MapType0Type refType MapType1Type))) (= (type |l#2@@10|) (FieldType boolType))) (= (type $o@@24) refType)) (= (type $f@@10) (FieldType alpha@@17))) (= (U_2_bool (MapType4Select (|lambda#11| |l#0@@10| |l#1@@10| |l#2@@10| |l#3@@10|) $o@@24 $f@@10))  (=> (and (not (= $o@@24 |l#0@@10|)) (U_2_bool (MapType1Select (MapType0Select |l#1@@10| $o@@24) |l#2@@10|))) |l#3@@10|))))
 :qid |DafnyPreludebpl.129:1|
 :skolemid |1044|
 :pattern ( (MapType4Select (|lambda#11| |l#0@@10| |l#1@@10| |l#2@@10| |l#3@@10|) $o@@24 $f@@10))
)))
(declare-fun ControlFlow (Int Int) Int)
(declare-fun $_Frame@0 () T@U)
(declare-fun $Heap () T@U)
(declare-fun this@@27 () T@U)
(declare-fun |i#0@@9| () Int)
(declare-fun $_Frame@0@@0 () T@U)
(declare-fun |b$reqreads#0@0| () Bool)
(declare-fun |b$reqreads#1@0| () Bool)
(declare-fun $IsHeapAnchor (T@U) Bool)
(assert  (and (and (and (= (type $_Frame@0) (MapType4Type refType boolType)) (= (type $Heap) (MapType0Type refType MapType1Type))) (= (type this@@27) DatatypeTypeType)) (= (type $_Frame@0@@0) (MapType4Type refType boolType))))
(set-info :boogie-vc-id CheckWellformed$$Test.QueryReceipt.ChildAt)
(set-option :timeout 0)
(set-option :rlimit 16350000)
(assert (not
 (=> (= (ControlFlow 0 0) 55423) (let ((anon4_Else_correct  (=> (and (= $_Frame@0 (|lambda#11| null $Heap alloc false)) (Test.QueryReceipt.QueryReceipt_q this@@27)) (and (=> (= (ControlFlow 0 38390) (- 0 55628)) (and (<= 0 |i#0@@9|) (< |i#0@@9| (|Seq#Length| (Test.QueryReceipt.lines this@@27))))) (=> (and (<= 0 |i#0@@9|) (< |i#0@@9| (|Seq#Length| (Test.QueryReceipt.lines this@@27)))) (=> (Test.QueryReceiptLine.QueryReceiptLine_q ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))) (and (=> (= (ControlFlow 0 38390) (- 0 55660)) (Test.BetreeNode.BetreeNode_q (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))))) (=> (Test.BetreeNode.BetreeNode_q (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))) (=> (Test.ChildMap.ChildMap_q (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))))) (=> (and (Test.QueryReceipt.QueryReceipt_q this@@27) (= (ControlFlow 0 38390) (- 0 55698))) (U_2_bool (MapType0Select (|IMap#Domain| (Test.ChildMap.mapp (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))))) ($Box (Test.QueryReceipt.key this@@27))))))))))))))
(let ((anon4_Then_correct true))
(let ((anon0_correct  (=> (= $_Frame@0@@0 (|lambda#10| null $Heap alloc false)) (=> (and ($IsAlloc this@@27 Tclass.Test.QueryReceipt $Heap) (= |b$reqreads#0@0| (forall (($o@@25 T@U) ($f@@11 T@U) ) (! (let ((alpha@@18 (FieldTypeInv0 (type $f@@11))))
 (=> (and (and (= (type $o@@25) refType) (= (type $f@@11) (FieldType alpha@@18))) false) (U_2_bool (MapType4Select $_Frame@0@@0 $o@@25 $f@@11))))
 :qid |Testidfy.41:16|
 :skolemid |1008|
 :no-pattern (type $o@@25)
 :no-pattern (type $f@@11)
 :no-pattern (U_2_int $o@@25)
 :no-pattern (U_2_bool $o@@25)
 :no-pattern (U_2_int $f@@11)
 :no-pattern (U_2_bool $f@@11)
)))) (=> (and (and (and (|Test.QueryReceipt.AllLinesWF#canCall| this@@27) (Test.QueryReceipt.AllLinesWF this@@27)) (and ($IsAlloc this@@27 Tclass.Test.QueryReceipt $Heap) (= |b$reqreads#1@0| (forall (($o@@26 T@U) ($f@@12 T@U) ) (! (let ((alpha@@19 (FieldTypeInv0 (type $f@@12))))
 (=> (and (and (= (type $o@@26) refType) (= (type $f@@12) (FieldType alpha@@19))) false) (U_2_bool (MapType4Select $_Frame@0@@0 $o@@26 $f@@12))))
 :qid |Testidfy.42:16|
 :skolemid |1009|
 :no-pattern (type $o@@26)
 :no-pattern (type $f@@12)
 :no-pattern (U_2_int $o@@26)
 :no-pattern (U_2_bool $o@@26)
 :no-pattern (U_2_int $f@@12)
 :no-pattern (U_2_bool $f@@12)
))))) (and (and (|Test.QueryReceipt.Structure#canCall| this@@27) (Test.QueryReceipt.Structure this@@27)) (and (Test.QueryReceipt.QueryReceipt_q this@@27) (INTERNAL_lt_boogie |i#0@@9| (INTERNAL_sub_boogie (|Seq#Length| (Test.QueryReceipt.lines this@@27)) 1))))) (and (=> (= (ControlFlow 0 38384) (- 0 55594)) |b$reqreads#0@0|) (=> |b$reqreads#0@0| (and (=> (= (ControlFlow 0 38384) (- 0 55595)) |b$reqreads#1@0|) (=> |b$reqreads#1@0| (and (=> (= (ControlFlow 0 38384) 38388) anon4_Then_correct) (=> (= (ControlFlow 0 38384) 38390) anon4_Else_correct)))))))))))
(let ((PreconditionGeneratedEntry_correct  (=> (and ($IsGoodHeap $Heap) ($IsHeapAnchor $Heap)) (=> (and (and (and ($Is this@@27 Tclass.Test.QueryReceipt) ($IsAlloc this@@27 Tclass.Test.QueryReceipt $Heap)) (INTERNAL_le_boogie 0 |i#0@@9|)) (and (= 9 $FunctionContextHeight) (= (ControlFlow 0 55423) 38384))) anon0_correct))))
PreconditionGeneratedEntry_correct)))))
))
(check-sat)