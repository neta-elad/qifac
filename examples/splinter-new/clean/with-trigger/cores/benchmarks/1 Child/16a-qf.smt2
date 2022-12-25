(declare-fun |b1[typeInv:U_2_int]| () Bool)
(declare-fun |b34[Buffersidfy.15:20!1659]| () Bool)
(declare-fun |b30[PagedBetreeidfy.49:15!1085]| () Bool)
(declare-fun |b36[PagedBetreeidfy.77:16]| () Bool)
(declare-fun |b17[cast:U_2_regex]| () Bool)
(declare-fun |b6[funType:real_2_U]| () Bool)
(declare-fun |b7[typeInv:U_2_bool]| () Bool)
(declare-fun |b2[cast:U_2_int]| () Bool)
(declare-fun |b23[typeInv:IMapTypeInv1]| () Bool)
(declare-fun |b8[cast:U_2_bool]| () Bool)
(declare-fun |b24[funType:IMap#Elements]| () Bool)
(declare-fun |b21[ctor:IMapType]| () Bool)
(declare-fun |b18[funType:regex_2_U]| () Bool)
(declare-fun |b25[funType:IMap#Domain]| () Bool)
(declare-fun |b4[typeInv:U_2_real]| () Bool)
(declare-fun |b3[funType:int_2_U]| () Bool)
(declare-fun |b29[funType:AsFuelBottom]| () Bool)
(declare-fun |b32[PagedBetreeidfy.69:5!1156]| () Bool)
(declare-fun |b26[funType:$LS]| () Bool)
(declare-fun |b22[typeInv:IMapTypeInv0]| () Bool)
(declare-fun |b37[Buffersidfy.17:12]| () Bool)
(declare-fun |b12[funType:rmode_2_U]| () Bool)
(declare-fun |b35[Buffersidfy.16:19!1676]| () Bool)
(declare-fun |b9[funType:bool_2_U]| () Bool)
(declare-fun |b28[PagedBetreeidfy.49:15]| () Bool)
(declare-fun |b39[]| () Bool)
(declare-fun |b20[DafnyPreludebpl.89:29]| () Bool)
(declare-fun |b33[PagedBetreeidfy.72:15!1188]| () Bool)
(declare-fun |b13[typeInv:U_2_string]| () Bool)
(declare-fun |b38[]| () Bool)
(declare-fun |b40[]| () Bool)
(declare-fun |b41[]| () Bool)
(declare-fun |b27[funType:PagedBetree.ChildMap.mapp]| () Bool)
(declare-fun |b31[unknown.0:0!1121]| () Bool)
(declare-fun |b15[funType:string_2_U]| () Bool)
(declare-fun |b14[cast:U_2_string]| () Bool)
(declare-fun |b11[cast:U_2_rmode]| () Bool)
(declare-fun |b10[typeInv:U_2_rmode]| () Bool)
(declare-fun |b5[cast:U_2_real]| () Bool)
(declare-fun |b16[typeInv:U_2_regex]| () Bool)
(declare-fun |b19[funType:Lit]| () Bool)
(set-info :smt-lib-version |2.6|)
(set-info :category |"industrial"|)
(set-info :boogie-vc-id CheckWellformed$$PagedBetree.BetreeNode.Child)
(set-option :print-success false)
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
(declare-sort T@T 0)
(declare-sort T@U 0)
(declare-fun Ctor (T@T) Int)
(declare-fun intType () T@T)
(declare-fun realType () T@T)
(declare-fun boolType () T@T)
(declare-fun rmodeType () T@T)
(declare-fun stringType () T@T)
(declare-fun regexType () T@T)
(declare-fun int_2_U (Int) T@U)
(declare-fun U_2_int (T@U) Int)
(declare-fun type (T@U) T@T)
(declare-fun real_2_U (Real) T@U)
(declare-fun U_2_real (T@U) Real)
(declare-fun bool_2_U (Bool) T@U)
(declare-fun U_2_bool (T@U) Bool)
(declare-fun rmode_2_U (RoundingMode) T@U)
(declare-fun U_2_rmode (T@U) RoundingMode)
(declare-fun string_2_U (String) T@U)
(declare-fun U_2_string (T@U) String)
(declare-fun regex_2_U ((RegEx String)) T@U)
(declare-fun U_2_regex (T@U) (RegEx String))
(declare-fun Lit (T@U) T@U)
(declare-fun IMapType (T@T T@T) T@T)
(declare-fun IMapTypeInv0 (T@T) T@T)
(declare-fun IMapTypeInv1 (T@T) T@T)
(declare-fun |IMap#Elements| (T@U) T@U)
(declare-fun MapType0Type (T@T T@T) T@T)
(declare-fun |IMap#Domain| (T@U) T@U)
(declare-fun $LS (T@U) T@U)
(declare-fun LayerTypeType () T@T)
(declare-fun PagedBetree.ChildMap.mapp (T@U) T@U)
(declare-fun BoxType () T@T)
(declare-fun PagedBetree.ChildMap.WF (T@U T@U) Bool)
(declare-fun DatatypeTypeType () T@T)
(declare-fun AsFuelBottom (T@U) T@U)
(declare-fun $LZ () T@U)
(declare-fun PagedBetree.BetreeNode.WF (T@U T@U) Bool)
(declare-fun $Unbox (T@T T@U) T@U)
(declare-fun MapType0Select (T@U T@U) T@U)
(declare-fun $Box (T@U) T@U)
(declare-fun |k#0@@0!1333!0| (T@U T@U) T@U)
(declare-fun Buffers.__default.AnyKey (T@U) Bool)
(declare-fun $Is (T@U T@U) Bool)
(declare-fun Tclass.KeyType.Key () T@U)
(declare-fun SeqType (T@T) T@T)
(declare-fun Buffers.__default.Total (T@U) Bool)
(declare-fun |PagedBetree.BetreeNode.WF#canCall| (T@U) Bool)
(declare-fun PagedBetree.ChildMap.ChildMap_q (T@U) Bool)
(declare-fun |Buffers.__default.AnyKey#canCall| (T@U) Bool)
(declare-fun |Buffers.__default.Total#canCall| (T@U) Bool)
(declare-fun Tclass.PagedBetree.ChildMap () T@U)
(declare-fun $FunctionContextHeight () Int)
(declare-fun |PagedBetree.ChildMap.WF#canCall| (T@U) Bool)
(declare-fun PagedBetree.BetreeNode.BetreeNode_q (T@U) Bool)
(declare-fun |#PagedBetree.BetreeNode.BetreeNode| (T@U T@U) T@U)
(declare-fun |a#6#1#0@@0!1349!1| (T@U) T@U)
(declare-fun |a#6#0#0@@0!1349!2| (T@U) T@U)
(declare-fun PagedBetree.BetreeNode.children (T@U) T@U)
(declare-fun Tclass.PagedBetree.BetreeNode () T@U)
(declare-fun Tclass.ValueMessage.Message () T@U)
(declare-fun TotalKMMapMod.__default.DefaultV () T@U)
(declare-fun TotalKMMapMod.__default.TerminalValue (T@U) Bool)
(declare-fun |k#0@@82!3099!3| (T@U) T@U)
(declare-fun TISet (T@U) T@U)
(declare-fun MapType6Type (T@T T@T) T@T)
(declare-fun refType () T@T)
(declare-fun $_Frame@0 () T@U)
(declare-fun MapType1Type () T@T)
(declare-fun $Heap@@50 () T@U)
(declare-fun this@@248 () T@U)
(declare-fun |key#0@@61| () T@U)
(declare-fun $_Frame@0@@0 () T@U)
(declare-fun StartFuel_Sequences._default.Range () T@U)
(declare-fun StartFuelAssert_Sequences._default.Range () T@U)
(declare-fun StartFuel_Sequences._default.ApplyOpaque () T@U)
(declare-fun StartFuelAssert_Sequences._default.ApplyOpaque () T@U)
(declare-fun StartFuel_Sequences._default.remove () T@U)
(declare-fun StartFuelAssert_Sequences._default.remove () T@U)
(declare-fun StartFuel_Sequences._default.RemoveOneValue () T@U)
(declare-fun StartFuelAssert_Sequences._default.RemoveOneValue () T@U)
(declare-fun StartFuel_Sequences._default.insert () T@U)
(declare-fun StartFuelAssert_Sequences._default.insert () T@U)
(declare-fun StartFuel_Sequences._default.replace1with2 () T@U)
(declare-fun StartFuelAssert_Sequences._default.replace1with2 () T@U)
(declare-fun StartFuel_Sequences._default.replace2with1 () T@U)
(declare-fun StartFuelAssert_Sequences._default.replace2with1 () T@U)
(declare-fun StartFuel_Sequences._default.concat () T@U)
(declare-fun StartFuelAssert_Sequences._default.concat () T@U)
(declare-fun StartFuel_Sequences._default.concat3 () T@U)
(declare-fun StartFuelAssert_Sequences._default.concat3 () T@U)
(declare-fun StartFuel_Sequences._default.concatSeq () T@U)
(declare-fun StartFuelAssert_Sequences._default.concatSeq () T@U)
(declare-fun StartFuel_Sequences._default.IsPrefix () T@U)
(declare-fun StartFuelAssert_Sequences._default.IsPrefix () T@U)
(declare-fun StartFuel_Sequences._default.IsSuffix () T@U)
(declare-fun StartFuelAssert_Sequences._default.IsSuffix () T@U)
(declare-fun StartFuelAssert_Sequences._default.SeqIndexIterate () T@U)
(declare-fun StartFuel_Sequences._default.SeqIndex () T@U)
(declare-fun StartFuelAssert_Sequences._default.SeqIndex () T@U)
(declare-fun StartFuel_Sequences._default.SeqOfLength () T@U)
(declare-fun StartFuelAssert_Sequences._default.SeqOfLength () T@U)
(declare-fun StartFuel_Sequences._default.SeqIndexUpdate () T@U)
(declare-fun StartFuelAssert_Sequences._default.SeqIndexUpdate () T@U)
(declare-fun StartFuel_Sequences._default.Zip () T@U)
(declare-fun StartFuelAssert_Sequences._default.Zip () T@U)
(declare-fun StartFuel_Sequences._default.Unzip () T@U)
(declare-fun StartFuelAssert_Sequences._default.Unzip () T@U)
(declare-fun StartFuel_Sequences._default.Flatten () T@U)
(declare-fun StartFuelAssert_Sequences._default.Flatten () T@U)
(declare-fun StartFuel_Sequences._default.seqMax () T@U)
(declare-fun StartFuelAssert_Sequences._default.seqMax () T@U)
(declare-fun StartFuel_Sequences._default.fill () T@U)
(declare-fun StartFuelAssert_Sequences._default.fill () T@U)
(declare-fun StartFuel_Maps._default.MapRemoveStrong () T@U)
(declare-fun StartFuelAssert_Maps._default.MapRemoveStrong () T@U)
(declare-fun StartFuel_Maps._default.MapRemove1Strong () T@U)
(declare-fun StartFuelAssert_Maps._default.MapRemove1Strong () T@U)
(declare-fun StartFuel_Maps._default.IMapInvert () T@U)
(declare-fun StartFuelAssert_Maps._default.IMapInvert () T@U)
(declare-fun StartFuel_Maps._default.IMapRemove () T@U)
(declare-fun StartFuelAssert_Maps._default.IMapRemove () T@U)
(declare-fun StartFuel_Maps._default.IMapRemove1 () T@U)
(declare-fun StartFuelAssert_Maps._default.IMapRemove1 () T@U)
(declare-fun StartFuelAssert_Maps._default.MapDisjointUnion () T@U)
(declare-fun StartFuelAssert_Maps._default.MapUnionPreferA () T@U)
(declare-fun StartFuel_Maps._default.MapUnionPreferB () T@U)
(declare-fun StartFuelAssert_Maps._default.MapUnionPreferB () T@U)
(declare-fun StartFuel_Maps._default.MapUnion () T@U)
(declare-fun StartFuelAssert_Maps._default.MapUnion () T@U)
(declare-fun StartFuelAssert_Maps._default.IMapUnionPreferA () T@U)
(declare-fun StartFuel_Maps._default.IMapUnionPreferB () T@U)
(declare-fun StartFuelAssert_Maps._default.IMapUnionPreferB () T@U)
(declare-fun StartFuel_Maps._default.IMapUnion () T@U)
(declare-fun StartFuelAssert_Maps._default.IMapUnion () T@U)
(declare-fun StartFuel_Maps._default.MapDisjointUnion3 () T@U)
(declare-fun StartFuelAssert_Maps._default.MapDisjointUnion3 () T@U)
(declare-fun StartFuelAssert_MsgHistoryMod.MsgHistory.LSNSet () T@U)
(declare-fun StartFuel_PagedBetree.Path.ReplacedChildren () T@U)
(declare-fun StartFuelAssert_PagedBetree.Path.ReplacedChildren () T@U)
(declare-fun ControlFlow (Int Int) Int)
(declare-fun $IsGoodHeap (T@U) Bool)
(declare-fun $IsHeapAnchor (T@U) Bool)
(declare-fun $IsAlloc (T@U T@U T@U) Bool)
(declare-fun |lambda#4| (T@U T@U T@U Bool) T@U)
(declare-fun alloc () T@U)
(declare-fun null () T@U)
(declare-fun StartFuel_Sequences._default.NoDupes () T@U)
(declare-fun StartFuelAssert_Sequences._default.NoDupes () T@U)
(declare-fun StartFuel_Sequences._default.SeqIndexIterate () T@U)
(declare-fun StartFuel_Sequences._default.FlattenShape () T@U)
(declare-fun StartFuelAssert_Sequences._default.FlattenShape () T@U)
(declare-fun StartFuel_Sequences._default.FlattenLength () T@U)
(declare-fun StartFuelAssert_Sequences._default.FlattenLength () T@U)
(declare-fun StartFuel_MapRemove_s._default.MapRemove1 () T@U)
(declare-fun StartFuelAssert_MapRemove_s._default.MapRemove1 () T@U)
(declare-fun StartFuel_Maps._default.MapRemove () T@U)
(declare-fun StartFuelAssert_Maps._default.MapRemove () T@U)
(declare-fun StartFuel_Maps._default.MapDisjointUnion () T@U)
(declare-fun StartFuel_Maps._default.MapUnionPreferA () T@U)
(declare-fun StartFuel_Maps._default.IMapUnionPreferA () T@U)
(declare-fun StartFuel_MsgHistoryMod.MsgHistory.LSNSet () T@U)
(declare-fun MapType6Select (T@U T@U T@U) T@U)
(declare-fun FieldType (T@T) T@T)
(declare-fun FieldTypeInv0 (T@T) T@T)
(declare-fun |b$reqreads#0@0| () Bool)
(declare-fun $f@@91!1377!4 () T@U)
(declare-fun $o@@141!1377!5 () T@U)
(declare-fun |k#0@@84!1378!6| () T@U)
(declare-fun |lambda#5| (T@U T@U T@U Bool) T@U)
(assert (= (Ctor intType) 0)) ;; !QUANTIFIER-FREE!
(assert (= (Ctor realType) 1)) ;; !QUANTIFIER-FREE!
(assert (= (Ctor boolType) 2)) ;; !QUANTIFIER-FREE!
(assert (= (Ctor rmodeType) 3)) ;; !QUANTIFIER-FREE!
(assert (= (Ctor stringType) 4)) ;; !QUANTIFIER-FREE!
(assert (= (Ctor regexType) 5)) ;; !QUANTIFIER-FREE!
(assert (= (type $LZ) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (=> true (=> true (and (U_2_bool (Lit (bool_2_U (TotalKMMapMod.__default.TerminalValue (Lit TotalKMMapMod.__default.DefaultV))))) ($Is TotalKMMapMod.__default.DefaultV Tclass.ValueMessage.Message))))) ;; !QUANTIFIER-FREE!
(assert (= (type $_Frame@0) (MapType6Type refType boolType))) ;; !QUANTIFIER-FREE!
(assert (= (type $Heap@@50) (MapType0Type refType MapType1Type))) ;; !QUANTIFIER-FREE!
(assert (= (type this@@248) DatatypeTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type |key#0@@61|) (SeqType BoxType))) ;; !QUANTIFIER-FREE!
(assert (= (type $_Frame@0@@0) (MapType6Type refType boolType))) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuel_Sequences._default.Range) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuelAssert_Sequences._default.Range) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuel_Sequences._default.ApplyOpaque) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuelAssert_Sequences._default.ApplyOpaque) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuel_Sequences._default.remove) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuelAssert_Sequences._default.remove) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuel_Sequences._default.RemoveOneValue) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuelAssert_Sequences._default.RemoveOneValue) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuel_Sequences._default.insert) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuelAssert_Sequences._default.insert) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuel_Sequences._default.replace1with2) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuelAssert_Sequences._default.replace1with2) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuel_Sequences._default.replace2with1) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuelAssert_Sequences._default.replace2with1) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuel_Sequences._default.concat) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuelAssert_Sequences._default.concat) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuel_Sequences._default.concat3) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuelAssert_Sequences._default.concat3) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuel_Sequences._default.concatSeq) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuelAssert_Sequences._default.concatSeq) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuel_Sequences._default.IsPrefix) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuelAssert_Sequences._default.IsPrefix) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuel_Sequences._default.IsSuffix) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuelAssert_Sequences._default.IsSuffix) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuelAssert_Sequences._default.SeqIndexIterate) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuel_Sequences._default.SeqIndex) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuelAssert_Sequences._default.SeqIndex) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuel_Sequences._default.SeqOfLength) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuelAssert_Sequences._default.SeqOfLength) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuel_Sequences._default.SeqIndexUpdate) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuelAssert_Sequences._default.SeqIndexUpdate) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuel_Sequences._default.Zip) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuelAssert_Sequences._default.Zip) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuel_Sequences._default.Unzip) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuelAssert_Sequences._default.Unzip) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuel_Sequences._default.Flatten) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuelAssert_Sequences._default.Flatten) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuel_Sequences._default.seqMax) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuelAssert_Sequences._default.seqMax) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuel_Sequences._default.fill) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuelAssert_Sequences._default.fill) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuel_Maps._default.MapRemoveStrong) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuelAssert_Maps._default.MapRemoveStrong) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuel_Maps._default.MapRemove1Strong) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuelAssert_Maps._default.MapRemove1Strong) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuel_Maps._default.IMapInvert) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuelAssert_Maps._default.IMapInvert) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuel_Maps._default.IMapRemove) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuelAssert_Maps._default.IMapRemove) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuel_Maps._default.IMapRemove1) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuelAssert_Maps._default.IMapRemove1) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuelAssert_Maps._default.MapDisjointUnion) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuelAssert_Maps._default.MapUnionPreferA) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuel_Maps._default.MapUnionPreferB) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuelAssert_Maps._default.MapUnionPreferB) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuel_Maps._default.MapUnion) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuelAssert_Maps._default.MapUnion) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuelAssert_Maps._default.IMapUnionPreferA) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuel_Maps._default.IMapUnionPreferB) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuelAssert_Maps._default.IMapUnionPreferB) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuel_Maps._default.IMapUnion) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuelAssert_Maps._default.IMapUnion) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuel_Maps._default.MapDisjointUnion3) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuelAssert_Maps._default.MapDisjointUnion3) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuelAssert_MsgHistoryMod.MsgHistory.LSNSet) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuel_PagedBetree.Path.ReplacedChildren) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (type StartFuelAssert_PagedBetree.Path.ReplacedChildren) LayerTypeType)) ;; !QUANTIFIER-FREE!
(assert (= (ControlFlow 0 0) 333606)) ;; !QUANTIFIER-FREE!
(assert ($IsGoodHeap $Heap@@50)) ;; !QUANTIFIER-FREE!
(assert ($IsHeapAnchor $Heap@@50)) ;; !QUANTIFIER-FREE!
(assert ($Is this@@248 Tclass.PagedBetree.BetreeNode)) ;; !QUANTIFIER-FREE!
(assert ($IsAlloc this@@248 Tclass.PagedBetree.BetreeNode $Heap@@50)) ;; !QUANTIFIER-FREE!
(assert ($Is |key#0@@61| Tclass.KeyType.Key)) ;; !QUANTIFIER-FREE!
(assert (= 10 $FunctionContextHeight)) ;; !QUANTIFIER-FREE!
(assert (= (ControlFlow 0 333606) 49064)) ;; !QUANTIFIER-FREE!
(assert (= $_Frame@0@@0 (|lambda#4| null $Heap@@50 alloc false))) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_Sequences._default.NoDupes) StartFuel_Sequences._default.NoDupes)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_Sequences._default.NoDupes) StartFuelAssert_Sequences._default.NoDupes)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_Sequences._default.Range) StartFuel_Sequences._default.Range)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_Sequences._default.Range) StartFuelAssert_Sequences._default.Range)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_Sequences._default.ApplyOpaque) StartFuel_Sequences._default.ApplyOpaque)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_Sequences._default.ApplyOpaque) StartFuelAssert_Sequences._default.ApplyOpaque)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_Sequences._default.remove) StartFuel_Sequences._default.remove)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_Sequences._default.remove) StartFuelAssert_Sequences._default.remove)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_Sequences._default.RemoveOneValue) StartFuel_Sequences._default.RemoveOneValue)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_Sequences._default.RemoveOneValue) StartFuelAssert_Sequences._default.RemoveOneValue)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_Sequences._default.insert) StartFuel_Sequences._default.insert)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_Sequences._default.insert) StartFuelAssert_Sequences._default.insert)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_Sequences._default.replace1with2) StartFuel_Sequences._default.replace1with2)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_Sequences._default.replace1with2) StartFuelAssert_Sequences._default.replace1with2)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_Sequences._default.replace2with1) StartFuel_Sequences._default.replace2with1)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_Sequences._default.replace2with1) StartFuelAssert_Sequences._default.replace2with1)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_Sequences._default.concat) StartFuel_Sequences._default.concat)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_Sequences._default.concat) StartFuelAssert_Sequences._default.concat)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_Sequences._default.concat3) StartFuel_Sequences._default.concat3)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_Sequences._default.concat3) StartFuelAssert_Sequences._default.concat3)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_Sequences._default.concatSeq) StartFuel_Sequences._default.concatSeq)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_Sequences._default.concatSeq) StartFuelAssert_Sequences._default.concatSeq)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_Sequences._default.IsPrefix) StartFuel_Sequences._default.IsPrefix)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_Sequences._default.IsPrefix) StartFuelAssert_Sequences._default.IsPrefix)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_Sequences._default.IsSuffix) StartFuel_Sequences._default.IsSuffix)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_Sequences._default.IsSuffix) StartFuelAssert_Sequences._default.IsSuffix)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_Sequences._default.SeqIndexIterate) StartFuel_Sequences._default.SeqIndexIterate)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_Sequences._default.SeqIndexIterate) StartFuelAssert_Sequences._default.SeqIndexIterate)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_Sequences._default.SeqIndex) StartFuel_Sequences._default.SeqIndex)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_Sequences._default.SeqIndex) StartFuelAssert_Sequences._default.SeqIndex)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_Sequences._default.SeqOfLength) StartFuel_Sequences._default.SeqOfLength)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_Sequences._default.SeqOfLength) StartFuelAssert_Sequences._default.SeqOfLength)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_Sequences._default.SeqIndexUpdate) StartFuel_Sequences._default.SeqIndexUpdate)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_Sequences._default.SeqIndexUpdate) StartFuelAssert_Sequences._default.SeqIndexUpdate)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_Sequences._default.Zip) StartFuel_Sequences._default.Zip)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_Sequences._default.Zip) StartFuelAssert_Sequences._default.Zip)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_Sequences._default.Unzip) StartFuel_Sequences._default.Unzip)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_Sequences._default.Unzip) StartFuelAssert_Sequences._default.Unzip)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_Sequences._default.FlattenShape) StartFuel_Sequences._default.FlattenShape)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_Sequences._default.FlattenShape) StartFuelAssert_Sequences._default.FlattenShape)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_Sequences._default.FlattenLength) StartFuel_Sequences._default.FlattenLength)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_Sequences._default.FlattenLength) StartFuelAssert_Sequences._default.FlattenLength)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_Sequences._default.Flatten) StartFuel_Sequences._default.Flatten)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_Sequences._default.Flatten) StartFuelAssert_Sequences._default.Flatten)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_Sequences._default.seqMax) StartFuel_Sequences._default.seqMax)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_Sequences._default.seqMax) StartFuelAssert_Sequences._default.seqMax)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_Sequences._default.fill) StartFuel_Sequences._default.fill)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_Sequences._default.fill) StartFuelAssert_Sequences._default.fill)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_MapRemove_s._default.MapRemove1) StartFuel_MapRemove_s._default.MapRemove1)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_MapRemove_s._default.MapRemove1) StartFuelAssert_MapRemove_s._default.MapRemove1)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_Maps._default.MapRemove) StartFuel_Maps._default.MapRemove)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_Maps._default.MapRemove) StartFuelAssert_Maps._default.MapRemove)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_Maps._default.MapRemoveStrong) StartFuel_Maps._default.MapRemoveStrong)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_Maps._default.MapRemoveStrong) StartFuelAssert_Maps._default.MapRemoveStrong)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_Maps._default.MapRemove1Strong) StartFuel_Maps._default.MapRemove1Strong)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_Maps._default.MapRemove1Strong) StartFuelAssert_Maps._default.MapRemove1Strong)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_Maps._default.IMapInvert) StartFuel_Maps._default.IMapInvert)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_Maps._default.IMapInvert) StartFuelAssert_Maps._default.IMapInvert)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_Maps._default.IMapRemove) StartFuel_Maps._default.IMapRemove)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_Maps._default.IMapRemove) StartFuelAssert_Maps._default.IMapRemove)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_Maps._default.IMapRemove1) StartFuel_Maps._default.IMapRemove1)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_Maps._default.IMapRemove1) StartFuelAssert_Maps._default.IMapRemove1)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_Maps._default.MapDisjointUnion) StartFuel_Maps._default.MapDisjointUnion)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_Maps._default.MapDisjointUnion) StartFuelAssert_Maps._default.MapDisjointUnion)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_Maps._default.MapUnionPreferA) StartFuel_Maps._default.MapUnionPreferA)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_Maps._default.MapUnionPreferA) StartFuelAssert_Maps._default.MapUnionPreferA)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_Maps._default.MapUnionPreferB) StartFuel_Maps._default.MapUnionPreferB)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_Maps._default.MapUnionPreferB) StartFuelAssert_Maps._default.MapUnionPreferB)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_Maps._default.MapUnion) StartFuel_Maps._default.MapUnion)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_Maps._default.MapUnion) StartFuelAssert_Maps._default.MapUnion)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_Maps._default.IMapUnionPreferA) StartFuel_Maps._default.IMapUnionPreferA)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_Maps._default.IMapUnionPreferA) StartFuelAssert_Maps._default.IMapUnionPreferA)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_Maps._default.IMapUnionPreferB) StartFuel_Maps._default.IMapUnionPreferB)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_Maps._default.IMapUnionPreferB) StartFuelAssert_Maps._default.IMapUnionPreferB)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_Maps._default.IMapUnion) StartFuel_Maps._default.IMapUnion)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_Maps._default.IMapUnion) StartFuelAssert_Maps._default.IMapUnion)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_Maps._default.MapDisjointUnion3) StartFuel_Maps._default.MapDisjointUnion3)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_Maps._default.MapDisjointUnion3) StartFuelAssert_Maps._default.MapDisjointUnion3)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_MsgHistoryMod.MsgHistory.LSNSet) StartFuel_MsgHistoryMod.MsgHistory.LSNSet)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_MsgHistoryMod.MsgHistory.LSNSet) StartFuelAssert_MsgHistoryMod.MsgHistory.LSNSet)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuel_PagedBetree.Path.ReplacedChildren) StartFuel_PagedBetree.Path.ReplacedChildren)) ;; !QUANTIFIER-FREE!
(assert (= (AsFuelBottom StartFuelAssert_PagedBetree.Path.ReplacedChildren) StartFuelAssert_PagedBetree.Path.ReplacedChildren)) ;; !QUANTIFIER-FREE!
(assert ($IsAlloc this@@248 Tclass.PagedBetree.BetreeNode $Heap@@50)) ;; !QUANTIFIER-FREE!
(assert (or |b$reqreads#0@0| (not (=> (and (= (type $o@@141!1377!5) refType) (= (type $f@@91!1377!4) (FieldType (FieldTypeInv0 (type $f@@91!1377!4)))) false) (U_2_bool (MapType6Select $_Frame@0@@0 $o@@141!1377!5 $f@@91!1377!4)))))) ;; !QUANTIFIER-FREE!
(assert (|PagedBetree.BetreeNode.WF#canCall| this@@248)) ;; !QUANTIFIER-FREE!
(assert (PagedBetree.BetreeNode.WF ($LS $LZ) this@@248)) ;; !QUANTIFIER-FREE!
(assert (PagedBetree.BetreeNode.BetreeNode_q this@@248)) ;; !QUANTIFIER-FREE!
(check-sat)
