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
(assert |b1[typeInv:U_2_int]|) ;; !QUANTIFIED!
(assert |b2[cast:U_2_int]|) ;; !QUANTIFIED!
(assert |b3[funType:int_2_U]|) ;; !QUANTIFIED!
(assert |b4[typeInv:U_2_real]|) ;; !QUANTIFIED!
(assert |b5[cast:U_2_real]|) ;; !QUANTIFIED!
(assert |b6[funType:real_2_U]|) ;; !QUANTIFIED!
(assert |b7[typeInv:U_2_bool]|) ;; !QUANTIFIED!
(assert |b8[cast:U_2_bool]|) ;; !QUANTIFIED!
(assert |b9[funType:bool_2_U]|) ;; !QUANTIFIED!
(assert |b10[typeInv:U_2_rmode]|) ;; !QUANTIFIED!
(assert |b11[cast:U_2_rmode]|) ;; !QUANTIFIED!
(assert |b12[funType:rmode_2_U]|) ;; !QUANTIFIED!
(assert |b13[typeInv:U_2_string]|) ;; !QUANTIFIED!
(assert |b14[cast:U_2_string]|) ;; !QUANTIFIED!
(assert |b15[funType:string_2_U]|) ;; !QUANTIFIED!
(assert |b16[typeInv:U_2_regex]|) ;; !QUANTIFIED!
(assert |b17[cast:U_2_regex]|) ;; !QUANTIFIED!
(assert |b18[funType:regex_2_U]|) ;; !QUANTIFIED!
(assert |b19[funType:Lit]|) ;; !QUANTIFIED!
(assert |b20[DafnyPreludebpl.89:29]|) ;; !QUANTIFIED!
(assert |b21[ctor:IMapType]|) ;; !QUANTIFIED!
(assert |b22[typeInv:IMapTypeInv0]|) ;; !QUANTIFIED!
(assert |b23[typeInv:IMapTypeInv1]|) ;; !QUANTIFIED!
(assert |b24[funType:IMap#Elements]|) ;; !QUANTIFIED!
(assert |b25[funType:IMap#Domain]|) ;; !QUANTIFIED!
(assert |b26[funType:$LS]|) ;; !QUANTIFIED!
(assert |b27[funType:PagedBetree.ChildMap.mapp]|) ;; !QUANTIFIED!
(assert |b28[PagedBetreeidfy.49:15]|) ;; !QUANTIFIED!
(assert |b29[funType:AsFuelBottom]|) ;; !QUANTIFIED!
(assert (or (not (<= 9 $FunctionContextHeight)) |b30[PagedBetreeidfy.49:15!1085]|)) ;; !QUANTIFIED!
(assert |b31[unknown.0:0!1121]|) ;; !QUANTIFIED!
(assert |b32[PagedBetreeidfy.69:5!1156]|) ;; !QUANTIFIED!
(assert (or (not (<= 9 $FunctionContextHeight)) |b33[PagedBetreeidfy.72:15!1188]|)) ;; !QUANTIFIED!
(assert (or (not true) |b34[Buffersidfy.15:20!1659]|)) ;; !QUANTIFIED!
(assert (or (not true) |b35[Buffersidfy.16:19!1676]|)) ;; !QUANTIFIED!
(assert (or (not |b$reqreads#0@0|) |b36[PagedBetreeidfy.77:16]|)) ;; !QUANTIFIED!
(assert (! (=> |b9[funType:bool_2_U]| (= (type (bool_2_U (TotalKMMapMod.__default.TerminalValue (Lit TotalKMMapMod.__default.DefaultV)))) boolType)) :named |0x7fe12995f8c8-funType:bool_2_U[arg0@@4=(TotalKMMapMod.__default.TerminalValue (Lit TotalKMMapMod.__default.DefaultV))]|)) ;; !INST!
(assert (! (=> |b8[cast:U_2_bool]| (=> (= (type (MapType0Select (|IMap#Domain| (PagedBetree.ChildMap.mapp (PagedBetree.BetreeNode.children this@@248))) ($Box |key#0@@61|))) boolType) (= (bool_2_U (U_2_bool (MapType0Select (|IMap#Domain| (PagedBetree.ChildMap.mapp (PagedBetree.BetreeNode.children this@@248))) ($Box |key#0@@61|)))) (MapType0Select (|IMap#Domain| (PagedBetree.ChildMap.mapp (PagedBetree.BetreeNode.children this@@248))) ($Box |key#0@@61|))))) :named |0x7fe12996e288-cast:U_2_bool[x@@1=(MapType0Select (IMap#Domain (PagedBetree.ChildMap.mapp (PagedBetree.BetreeNode.children this@@248))) ($Box key#0@@61))]|)) ;; !INST!
(assert (! (=> |b27[funType:PagedBetree.ChildMap.mapp]| (= (type (PagedBetree.ChildMap.mapp (PagedBetree.BetreeNode.children this@@248))) (IMapType BoxType BoxType))) :named |0x7fe12996e290-funType:PagedBetree.ChildMap.mapp[arg0@@372=(PagedBetree.BetreeNode.children this@@248)]| :named |0x7fe12996e318-funType:PagedBetree.ChildMap.mapp[arg0@@372=(PagedBetree.BetreeNode.children this@@248)]|)) ;; !INST!
(assert (! (=> |b8[cast:U_2_bool]| (=> (= (type (Lit (bool_2_U (TotalKMMapMod.__default.TerminalValue (Lit TotalKMMapMod.__default.DefaultV))))) boolType) (= (bool_2_U (U_2_bool (Lit (bool_2_U (TotalKMMapMod.__default.TerminalValue (Lit TotalKMMapMod.__default.DefaultV)))))) (Lit (bool_2_U (TotalKMMapMod.__default.TerminalValue (Lit TotalKMMapMod.__default.DefaultV))))))) :named |0x7fe12995f8f8-cast:U_2_bool[x@@1=(Lit (bool_2_U (TotalKMMapMod.__default.TerminalValue (Lit TotalKMMapMod.__default.DefaultV))))]|)) ;; !INST!
(assert (! (=> |b26[funType:$LS]| (= (type ($LS ($LS $LZ))) LayerTypeType)) :named |0x7fe12996e2b8-funType:$LS[arg0@@68=($LS $LZ)]|)) ;; !INST!
(assert (! (=> |b19[funType:Lit]| (= (type (Lit TotalKMMapMod.__default.DefaultV)) (type TotalKMMapMod.__default.DefaultV))) :named |0x7fe12995f928-funType:Lit[arg0@@29=TotalKMMapMod.__default.DefaultV]|)) ;; !INST!
(assert (! (=> |b23[typeInv:IMapTypeInv1]| (= (IMapTypeInv1 (IMapType BoxType BoxType)) BoxType)) :named |0x7fe129972d40-typeInv:IMapTypeInv1[arg1@@13=BoxType,arg0@@47=BoxType]| :named |0x7fe129972b18-typeInv:IMapTypeInv1[arg1@@13=BoxType,arg0@@47=BoxType]|)) ;; !INST!
(assert (! (=> |b20[DafnyPreludebpl.89:29]| (= (Lit TotalKMMapMod.__default.DefaultV) TotalKMMapMod.__default.DefaultV)) :named |0x7fe12995f958-DafnyPreludebpl.89:29[x@@8=TotalKMMapMod.__default.DefaultV]|)) ;; !INST!
(assert (! (=> |b21[ctor:IMapType]| (= (Ctor (IMapType BoxType BoxType)) 18)) :named |0x7fe129972d78-ctor:IMapType[arg1@@11=BoxType,arg0@@45=BoxType]| :named |0x7fe129972b50-ctor:IMapType[arg1@@11=BoxType,arg0@@45=BoxType]|)) ;; !INST!
(assert (! (=> |b19[funType:Lit]| (= (type (Lit (bool_2_U (TotalKMMapMod.__default.TerminalValue (Lit TotalKMMapMod.__default.DefaultV))))) (type (bool_2_U (TotalKMMapMod.__default.TerminalValue (Lit TotalKMMapMod.__default.DefaultV)))))) :named |0x7fe12995f988-funType:Lit[arg0@@29=(bool_2_U (TotalKMMapMod.__default.TerminalValue (Lit TotalKMMapMod.__default.DefaultV)))]|)) ;; !INST!
(assert (! (=> |b20[DafnyPreludebpl.89:29]| (= (Lit (bool_2_U (TotalKMMapMod.__default.TerminalValue (Lit TotalKMMapMod.__default.DefaultV)))) (bool_2_U (TotalKMMapMod.__default.TerminalValue (Lit TotalKMMapMod.__default.DefaultV))))) :named |0x7fe12995f9b8-DafnyPreludebpl.89:29[x@@8=(bool_2_U (TotalKMMapMod.__default.TerminalValue (Lit TotalKMMapMod.__default.DefaultV)))]|)) ;; !INST!
(assert (! (=> |b22[typeInv:IMapTypeInv0]| (= (IMapTypeInv0 (IMapType BoxType BoxType)) BoxType)) :named |0x7fe129972db0-typeInv:IMapTypeInv0[arg1@@12=BoxType,arg0@@46=BoxType]| :named |0x7fe129972b88-typeInv:IMapTypeInv0[arg1@@12=BoxType,arg0@@46=BoxType]|)) ;; !INST!
(assert (! (=> |b26[funType:$LS]| (= (type ($LS $LZ)) LayerTypeType)) :named |0x7fe12995f9e8-funType:$LS[arg0@@68=$LZ]|)) ;; !INST!
(assert (! (=> |b37[Buffersidfy.17:12]| (=> (and (= (type |key#0@@61|) (SeqType BoxType)) ($Is |key#0@@61| Tclass.KeyType.Key)) (|Buffers.__default.AnyKey#canCall| |key#0@@61|))) :named |0x7fe12997f9a8-Buffersidfy.17:12[k#0@@81=key#0@@61,keys#0@@1=(IMap#Domain (PagedBetree.ChildMap.mapp (PagedBetree.BetreeNode.children this@@248)))]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_Sequences._default.NoDupes)) LayerTypeType)) :named |0x7fe12995fa18-funType:AsFuelBottom[arg0@@373=StartFuel_Sequences._default.NoDupes]|)) ;; !INST!
(assert (! (=> |b38[]| (=> (= (type |key#0@@61|) (SeqType BoxType)) (=> (and ($Is |key#0@@61| Tclass.KeyType.Key) (Buffers.__default.AnyKey |key#0@@61|)) (U_2_bool (MapType0Select (|IMap#Domain| (PagedBetree.ChildMap.mapp (PagedBetree.BetreeNode.children this@@248))) ($Box |key#0@@61|)))))) :named |0x7fe12997f9d8-Buffersidfy.17:12!1673[k#0@@82=key#0@@61,keys#0@@1=(IMap#Domain (PagedBetree.ChildMap.mapp (PagedBetree.BetreeNode.children this@@248)))]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_Sequences._default.NoDupes)) LayerTypeType)) :named |0x7fe12995fa48-funType:AsFuelBottom[arg0@@373=StartFuelAssert_Sequences._default.NoDupes]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_Sequences._default.Range)) LayerTypeType)) :named |0x7fe12995fa78-funType:AsFuelBottom[arg0@@373=StartFuel_Sequences._default.Range]|)) ;; !INST!
(assert (! (=> |b39[]| (=> (= (type |key#0@@61|) (SeqType BoxType)) (=> (and ($Is |key#0@@61| Tclass.KeyType.Key) (Buffers.__default.AnyKey |key#0@@61|)) (PagedBetree.BetreeNode.WF ($LS $LZ) ($Unbox DatatypeTypeType (MapType0Select (|IMap#Elements| (PagedBetree.ChildMap.mapp (PagedBetree.BetreeNode.children this@@248))) ($Box |key#0@@61|))))))) :named |0x7fe12997fbb8-PagedBetreeidfy.51:18!1084[k#0@@0=key#0@@61,$ly@@3=($LS $LZ),this@@3=(PagedBetree.BetreeNode.children this@@248)]|)) ;; !INST!
(assert (! (=> |b25[funType:IMap#Domain]| (= (type (|IMap#Domain| (PagedBetree.ChildMap.mapp (PagedBetree.BetreeNode.children this@@248)))) (MapType0Type (IMapTypeInv0 (type (PagedBetree.ChildMap.mapp (PagedBetree.BetreeNode.children this@@248)))) boolType))) :named |0x7fe12996e260-funType:IMap#Domain[arg0@@57=(PagedBetree.ChildMap.mapp (PagedBetree.BetreeNode.children this@@248))]| :named |0x7fe12996e2e8-funType:IMap#Domain[arg0@@57=(PagedBetree.ChildMap.mapp (PagedBetree.BetreeNode.children this@@248))]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_Sequences._default.Range)) LayerTypeType)) :named |0x7fe12995faa8-funType:AsFuelBottom[arg0@@373=StartFuelAssert_Sequences._default.Range]|)) ;; !INST!
(assert (! (=> |b40[]| (=> (= (type |key#0@@61|) (SeqType BoxType)) (=> (and ($Is |key#0@@61| Tclass.KeyType.Key) (Buffers.__default.AnyKey |key#0@@61|)) (PagedBetree.BetreeNode.WF $LZ ($Unbox DatatypeTypeType (MapType0Select (|IMap#Elements| (PagedBetree.ChildMap.mapp (PagedBetree.BetreeNode.children this@@248))) ($Box |key#0@@61|))))))) :named |0x7fe12997fbe8-PagedBetreeidfy.51:18!1084[k#0@@0=key#0@@61,$ly@@3=$LZ,this@@3=(PagedBetree.BetreeNode.children this@@248)]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_Sequences._default.ApplyOpaque)) LayerTypeType)) :named |0x7fe12995fad8-funType:AsFuelBottom[arg0@@373=StartFuel_Sequences._default.ApplyOpaque]|)) ;; !INST!
(assert (! (=> |b34[Buffersidfy.15:20!1659]| (=> (and (= (type |key#0@@61|) (SeqType BoxType)) (or (|Buffers.__default.AnyKey#canCall| |key#0@@61|) ($Is |key#0@@61| Tclass.KeyType.Key))) (= (Buffers.__default.AnyKey |key#0@@61|) (U_2_bool (Lit (bool_2_U true)))))) :named |0x7fe12997fc18-Buffersidfy.15:20!1659[key#0@@51=key#0@@61]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_Sequences._default.ApplyOpaque)) LayerTypeType)) :named |0x7fe12995fb08-funType:AsFuelBottom[arg0@@373=StartFuelAssert_Sequences._default.ApplyOpaque]|)) ;; !INST!
(assert (! (=> |b41[]| (=> (and (= (type |key#0@@61|) (SeqType BoxType)) ($Is |key#0@@61| Tclass.KeyType.Key)) (and (|Buffers.__default.AnyKey#canCall| |key#0@@61|) (=> (Buffers.__default.AnyKey |key#0@@61|) (and (PagedBetree.ChildMap.ChildMap_q (PagedBetree.BetreeNode.children this@@248)) (|PagedBetree.BetreeNode.WF#canCall| ($Unbox DatatypeTypeType (MapType0Select (|IMap#Elements| (PagedBetree.ChildMap.mapp (PagedBetree.BetreeNode.children this@@248))) ($Box |key#0@@61|))))))))) :named |0x7fe12997fc48-PagedBetreeidfy.51:18[k#0=key#0@@61,$ly@@3=$LZ,this@@3=(PagedBetree.BetreeNode.children this@@248)]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_Sequences._default.remove)) LayerTypeType)) :named |0x7fe12995fb38-funType:AsFuelBottom[arg0@@373=StartFuel_Sequences._default.remove]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_Sequences._default.remove)) LayerTypeType)) :named |0x7fe12995fb68-funType:AsFuelBottom[arg0@@373=StartFuelAssert_Sequences._default.remove]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_Sequences._default.RemoveOneValue)) LayerTypeType)) :named |0x7fe12995fb98-funType:AsFuelBottom[arg0@@373=StartFuel_Sequences._default.RemoveOneValue]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_Sequences._default.RemoveOneValue)) LayerTypeType)) :named |0x7fe12995fbc8-funType:AsFuelBottom[arg0@@373=StartFuelAssert_Sequences._default.RemoveOneValue]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_Sequences._default.insert)) LayerTypeType)) :named |0x7fe12995fbf8-funType:AsFuelBottom[arg0@@373=StartFuel_Sequences._default.insert]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_Sequences._default.insert)) LayerTypeType)) :named |0x7fe12995fc28-funType:AsFuelBottom[arg0@@373=StartFuelAssert_Sequences._default.insert]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_Sequences._default.replace1with2)) LayerTypeType)) :named |0x7fe12995fc58-funType:AsFuelBottom[arg0@@373=StartFuel_Sequences._default.replace1with2]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_Sequences._default.replace1with2)) LayerTypeType)) :named |0x7fe12995fc88-funType:AsFuelBottom[arg0@@373=StartFuelAssert_Sequences._default.replace1with2]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_Sequences._default.replace2with1)) LayerTypeType)) :named |0x7fe12995fcb8-funType:AsFuelBottom[arg0@@373=StartFuel_Sequences._default.replace2with1]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_Sequences._default.replace2with1)) LayerTypeType)) :named |0x7fe12995fce8-funType:AsFuelBottom[arg0@@373=StartFuelAssert_Sequences._default.replace2with1]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_Sequences._default.concat)) LayerTypeType)) :named |0x7fe12995fd18-funType:AsFuelBottom[arg0@@373=StartFuel_Sequences._default.concat]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_Sequences._default.concat)) LayerTypeType)) :named |0x7fe12995fd48-funType:AsFuelBottom[arg0@@373=StartFuelAssert_Sequences._default.concat]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_Sequences._default.concat3)) LayerTypeType)) :named |0x7fe12995fd78-funType:AsFuelBottom[arg0@@373=StartFuel_Sequences._default.concat3]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_Sequences._default.concat3)) LayerTypeType)) :named |0x7fe12995fda8-funType:AsFuelBottom[arg0@@373=StartFuelAssert_Sequences._default.concat3]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_Sequences._default.concatSeq)) LayerTypeType)) :named |0x7fe12995fdd8-funType:AsFuelBottom[arg0@@373=StartFuel_Sequences._default.concatSeq]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_Sequences._default.concatSeq)) LayerTypeType)) :named |0x7fe12995fe08-funType:AsFuelBottom[arg0@@373=StartFuelAssert_Sequences._default.concatSeq]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_Sequences._default.IsPrefix)) LayerTypeType)) :named |0x7fe12995fe38-funType:AsFuelBottom[arg0@@373=StartFuel_Sequences._default.IsPrefix]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_Sequences._default.IsPrefix)) LayerTypeType)) :named |0x7fe12995fe68-funType:AsFuelBottom[arg0@@373=StartFuelAssert_Sequences._default.IsPrefix]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_Sequences._default.IsSuffix)) LayerTypeType)) :named |0x7fe12995fe98-funType:AsFuelBottom[arg0@@373=StartFuel_Sequences._default.IsSuffix]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_Sequences._default.IsSuffix)) LayerTypeType)) :named |0x7fe12995fec8-funType:AsFuelBottom[arg0@@373=StartFuelAssert_Sequences._default.IsSuffix]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_Sequences._default.SeqIndexIterate)) LayerTypeType)) :named |0x7fe12995fef8-funType:AsFuelBottom[arg0@@373=StartFuel_Sequences._default.SeqIndexIterate]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_Sequences._default.SeqIndexIterate)) LayerTypeType)) :named |0x7fe12995ff28-funType:AsFuelBottom[arg0@@373=StartFuelAssert_Sequences._default.SeqIndexIterate]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_Sequences._default.SeqIndex)) LayerTypeType)) :named |0x7fe12995ff58-funType:AsFuelBottom[arg0@@373=StartFuel_Sequences._default.SeqIndex]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_Sequences._default.SeqIndex)) LayerTypeType)) :named |0x7fe12995ff88-funType:AsFuelBottom[arg0@@373=StartFuelAssert_Sequences._default.SeqIndex]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_Sequences._default.SeqOfLength)) LayerTypeType)) :named |0x7fe12995ffb8-funType:AsFuelBottom[arg0@@373=StartFuel_Sequences._default.SeqOfLength]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_Sequences._default.SeqOfLength)) LayerTypeType)) :named |0x7fe12995ffe8-funType:AsFuelBottom[arg0@@373=StartFuelAssert_Sequences._default.SeqOfLength]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_Sequences._default.SeqIndexUpdate)) LayerTypeType)) :named |0x7fe129960018-funType:AsFuelBottom[arg0@@373=StartFuel_Sequences._default.SeqIndexUpdate]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_Sequences._default.SeqIndexUpdate)) LayerTypeType)) :named |0x7fe129960048-funType:AsFuelBottom[arg0@@373=StartFuelAssert_Sequences._default.SeqIndexUpdate]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_Sequences._default.Zip)) LayerTypeType)) :named |0x7fe129960078-funType:AsFuelBottom[arg0@@373=StartFuel_Sequences._default.Zip]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_Sequences._default.Zip)) LayerTypeType)) :named |0x7fe1299600a8-funType:AsFuelBottom[arg0@@373=StartFuelAssert_Sequences._default.Zip]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_Sequences._default.Unzip)) LayerTypeType)) :named |0x7fe1299600d8-funType:AsFuelBottom[arg0@@373=StartFuel_Sequences._default.Unzip]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_Sequences._default.Unzip)) LayerTypeType)) :named |0x7fe129960108-funType:AsFuelBottom[arg0@@373=StartFuelAssert_Sequences._default.Unzip]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_Sequences._default.FlattenShape)) LayerTypeType)) :named |0x7fe129960138-funType:AsFuelBottom[arg0@@373=StartFuel_Sequences._default.FlattenShape]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_Sequences._default.FlattenShape)) LayerTypeType)) :named |0x7fe129960168-funType:AsFuelBottom[arg0@@373=StartFuelAssert_Sequences._default.FlattenShape]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_Sequences._default.FlattenLength)) LayerTypeType)) :named |0x7fe129960198-funType:AsFuelBottom[arg0@@373=StartFuel_Sequences._default.FlattenLength]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_Sequences._default.FlattenLength)) LayerTypeType)) :named |0x7fe1299601c8-funType:AsFuelBottom[arg0@@373=StartFuelAssert_Sequences._default.FlattenLength]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_Sequences._default.Flatten)) LayerTypeType)) :named |0x7fe1299601f8-funType:AsFuelBottom[arg0@@373=StartFuel_Sequences._default.Flatten]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_Sequences._default.Flatten)) LayerTypeType)) :named |0x7fe129960228-funType:AsFuelBottom[arg0@@373=StartFuelAssert_Sequences._default.Flatten]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_Sequences._default.seqMax)) LayerTypeType)) :named |0x7fe129960258-funType:AsFuelBottom[arg0@@373=StartFuel_Sequences._default.seqMax]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_Sequences._default.seqMax)) LayerTypeType)) :named |0x7fe129960288-funType:AsFuelBottom[arg0@@373=StartFuelAssert_Sequences._default.seqMax]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_Sequences._default.fill)) LayerTypeType)) :named |0x7fe1299602b8-funType:AsFuelBottom[arg0@@373=StartFuel_Sequences._default.fill]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_Sequences._default.fill)) LayerTypeType)) :named |0x7fe1299602e8-funType:AsFuelBottom[arg0@@373=StartFuelAssert_Sequences._default.fill]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_MapRemove_s._default.MapRemove1)) LayerTypeType)) :named |0x7fe129960318-funType:AsFuelBottom[arg0@@373=StartFuel_MapRemove_s._default.MapRemove1]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_MapRemove_s._default.MapRemove1)) LayerTypeType)) :named |0x7fe129960348-funType:AsFuelBottom[arg0@@373=StartFuelAssert_MapRemove_s._default.MapRemove1]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_Maps._default.MapRemove)) LayerTypeType)) :named |0x7fe129960378-funType:AsFuelBottom[arg0@@373=StartFuel_Maps._default.MapRemove]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_Maps._default.MapRemove)) LayerTypeType)) :named |0x7fe1299603a8-funType:AsFuelBottom[arg0@@373=StartFuelAssert_Maps._default.MapRemove]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_Maps._default.MapRemoveStrong)) LayerTypeType)) :named |0x7fe1299603d8-funType:AsFuelBottom[arg0@@373=StartFuel_Maps._default.MapRemoveStrong]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_Maps._default.MapRemoveStrong)) LayerTypeType)) :named |0x7fe129960408-funType:AsFuelBottom[arg0@@373=StartFuelAssert_Maps._default.MapRemoveStrong]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_Maps._default.MapRemove1Strong)) LayerTypeType)) :named |0x7fe129960438-funType:AsFuelBottom[arg0@@373=StartFuel_Maps._default.MapRemove1Strong]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_Maps._default.MapRemove1Strong)) LayerTypeType)) :named |0x7fe129960468-funType:AsFuelBottom[arg0@@373=StartFuelAssert_Maps._default.MapRemove1Strong]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_Maps._default.IMapInvert)) LayerTypeType)) :named |0x7fe129960498-funType:AsFuelBottom[arg0@@373=StartFuel_Maps._default.IMapInvert]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_Maps._default.IMapInvert)) LayerTypeType)) :named |0x7fe1299604c8-funType:AsFuelBottom[arg0@@373=StartFuelAssert_Maps._default.IMapInvert]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_Maps._default.IMapRemove)) LayerTypeType)) :named |0x7fe1299604f8-funType:AsFuelBottom[arg0@@373=StartFuel_Maps._default.IMapRemove]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_Maps._default.IMapRemove)) LayerTypeType)) :named |0x7fe129960528-funType:AsFuelBottom[arg0@@373=StartFuelAssert_Maps._default.IMapRemove]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_Maps._default.IMapRemove1)) LayerTypeType)) :named |0x7fe129960558-funType:AsFuelBottom[arg0@@373=StartFuel_Maps._default.IMapRemove1]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_Maps._default.IMapRemove1)) LayerTypeType)) :named |0x7fe129960588-funType:AsFuelBottom[arg0@@373=StartFuelAssert_Maps._default.IMapRemove1]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_Maps._default.MapDisjointUnion)) LayerTypeType)) :named |0x7fe1299605b8-funType:AsFuelBottom[arg0@@373=StartFuel_Maps._default.MapDisjointUnion]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_Maps._default.MapDisjointUnion)) LayerTypeType)) :named |0x7fe1299605e8-funType:AsFuelBottom[arg0@@373=StartFuelAssert_Maps._default.MapDisjointUnion]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_Maps._default.MapUnionPreferA)) LayerTypeType)) :named |0x7fe129960618-funType:AsFuelBottom[arg0@@373=StartFuel_Maps._default.MapUnionPreferA]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_Maps._default.MapUnionPreferA)) LayerTypeType)) :named |0x7fe129960648-funType:AsFuelBottom[arg0@@373=StartFuelAssert_Maps._default.MapUnionPreferA]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_Maps._default.MapUnionPreferB)) LayerTypeType)) :named |0x7fe129960678-funType:AsFuelBottom[arg0@@373=StartFuel_Maps._default.MapUnionPreferB]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_Maps._default.MapUnionPreferB)) LayerTypeType)) :named |0x7fe1299606a8-funType:AsFuelBottom[arg0@@373=StartFuelAssert_Maps._default.MapUnionPreferB]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_Maps._default.MapUnion)) LayerTypeType)) :named |0x7fe1299606d8-funType:AsFuelBottom[arg0@@373=StartFuel_Maps._default.MapUnion]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_Maps._default.MapUnion)) LayerTypeType)) :named |0x7fe129960708-funType:AsFuelBottom[arg0@@373=StartFuelAssert_Maps._default.MapUnion]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_Maps._default.IMapUnionPreferA)) LayerTypeType)) :named |0x7fe129960738-funType:AsFuelBottom[arg0@@373=StartFuel_Maps._default.IMapUnionPreferA]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_Maps._default.IMapUnionPreferA)) LayerTypeType)) :named |0x7fe129960768-funType:AsFuelBottom[arg0@@373=StartFuelAssert_Maps._default.IMapUnionPreferA]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_Maps._default.IMapUnionPreferB)) LayerTypeType)) :named |0x7fe129960798-funType:AsFuelBottom[arg0@@373=StartFuel_Maps._default.IMapUnionPreferB]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_Maps._default.IMapUnionPreferB)) LayerTypeType)) :named |0x7fe1299607c8-funType:AsFuelBottom[arg0@@373=StartFuelAssert_Maps._default.IMapUnionPreferB]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_Maps._default.IMapUnion)) LayerTypeType)) :named |0x7fe1299607f8-funType:AsFuelBottom[arg0@@373=StartFuel_Maps._default.IMapUnion]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_Maps._default.IMapUnion)) LayerTypeType)) :named |0x7fe129960828-funType:AsFuelBottom[arg0@@373=StartFuelAssert_Maps._default.IMapUnion]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_Maps._default.MapDisjointUnion3)) LayerTypeType)) :named |0x7fe129960858-funType:AsFuelBottom[arg0@@373=StartFuel_Maps._default.MapDisjointUnion3]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_Maps._default.MapDisjointUnion3)) LayerTypeType)) :named |0x7fe129960888-funType:AsFuelBottom[arg0@@373=StartFuelAssert_Maps._default.MapDisjointUnion3]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_MsgHistoryMod.MsgHistory.LSNSet)) LayerTypeType)) :named |0x7fe1299608b8-funType:AsFuelBottom[arg0@@373=StartFuel_MsgHistoryMod.MsgHistory.LSNSet]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_MsgHistoryMod.MsgHistory.LSNSet)) LayerTypeType)) :named |0x7fe1299608e8-funType:AsFuelBottom[arg0@@373=StartFuelAssert_MsgHistoryMod.MsgHistory.LSNSet]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuel_PagedBetree.Path.ReplacedChildren)) LayerTypeType)) :named |0x7fe129960918-funType:AsFuelBottom[arg0@@373=StartFuel_PagedBetree.Path.ReplacedChildren]|)) ;; !INST!
(assert (! (=> |b29[funType:AsFuelBottom]| (= (type (AsFuelBottom StartFuelAssert_PagedBetree.Path.ReplacedChildren)) LayerTypeType)) :named |0x7fe129960948-funType:AsFuelBottom[arg0@@373=StartFuelAssert_PagedBetree.Path.ReplacedChildren]|)) ;; !INST!
(assert (! (=> |b31[unknown.0:0!1121]| (or (not (and (= (type this@@248) DatatypeTypeType) (PagedBetree.BetreeNode.BetreeNode_q this@@248))) (and (= (type (|a#6#0#0@@0!1349!2| this@@248)) DatatypeTypeType) (= (type (|a#6#1#0@@0!1349!1| this@@248)) DatatypeTypeType) (= this@@248 (|#PagedBetree.BetreeNode.BetreeNode| (|a#6#0#0@@0!1349!2| this@@248) (|a#6#1#0@@0!1349!1| this@@248)))))) :named |0x7fe129960978-unknown.0:0!1121[d@@43=this@@248]|)) ;; !INST!
(assert (! (=> |b33[PagedBetreeidfy.72:15!1188]| (=> (and (= (type $LZ) LayerTypeType) (= (type this@@248) DatatypeTypeType) (or (|PagedBetree.BetreeNode.WF#canCall| this@@248) (and (not (= 9 $FunctionContextHeight)) ($Is this@@248 Tclass.PagedBetree.BetreeNode)))) (and (=> (U_2_bool (Lit (bool_2_U true))) (=> (PagedBetree.BetreeNode.BetreeNode_q this@@248) (|PagedBetree.ChildMap.WF#canCall| (PagedBetree.BetreeNode.children this@@248)))) (= (PagedBetree.BetreeNode.WF ($LS $LZ) this@@248) (and true (=> (PagedBetree.BetreeNode.BetreeNode_q this@@248) (PagedBetree.ChildMap.WF $LZ (PagedBetree.BetreeNode.children this@@248)))))))) :named |0x7fe1299609a8-PagedBetreeidfy.72:15!1188[this@@9=this@@248,$ly@@9=$LZ]|)) ;; !INST!
(assert (! (=> |b8[cast:U_2_bool]| (=> (= (type (bool_2_U (TotalKMMapMod.__default.TerminalValue (Lit TotalKMMapMod.__default.DefaultV)))) boolType) (= (bool_2_U (U_2_bool (bool_2_U (TotalKMMapMod.__default.TerminalValue (Lit TotalKMMapMod.__default.DefaultV))))) (bool_2_U (TotalKMMapMod.__default.TerminalValue (Lit TotalKMMapMod.__default.DefaultV)))))) :named |0x7fe12996d998-cast:U_2_bool[x@@1=(bool_2_U (TotalKMMapMod.__default.TerminalValue (Lit TotalKMMapMod.__default.DefaultV)))]|)) ;; !INST!
(assert (! (=> |b32[PagedBetreeidfy.69:5!1156]| (=> (and (= (type (|a#6#0#0@@0!1349!2| this@@248)) DatatypeTypeType) (= (type (|a#6#1#0@@0!1349!1| this@@248)) DatatypeTypeType)) (= (PagedBetree.BetreeNode.children (|#PagedBetree.BetreeNode.BetreeNode| (|a#6#0#0@@0!1349!2| this@@248) (|a#6#1#0@@0!1349!1| this@@248))) (|a#6#1#0@@0!1349!1| this@@248)))) :named |0x7fe12996d9c8-PagedBetreeidfy.69:5!1156[a#12#1#0=(a#6#1#0@@0!1349!1 this@@248),a#12#0#0=(a#6#0#0@@0!1349!2 this@@248)]|)) ;; !INST!
(assert (! (=> |b7[typeInv:U_2_bool]| (= (U_2_bool (bool_2_U true)) true)) :named |0x7fe12996dde8-typeInv:U_2_bool[arg0@@3=true]|)) ;; !INST!
(assert (! (=> |b9[funType:bool_2_U]| (= (type (bool_2_U true)) boolType)) :named |0x7fe12996de18-funType:bool_2_U[arg0@@4=true]|)) ;; !INST!
(assert (! (=> |b28[PagedBetreeidfy.49:15]| (=> (and (= (type $LZ) LayerTypeType) (= (type (PagedBetree.BetreeNode.children this@@248)) DatatypeTypeType)) (= (PagedBetree.ChildMap.WF ($LS $LZ) (PagedBetree.BetreeNode.children this@@248)) (PagedBetree.ChildMap.WF $LZ (PagedBetree.BetreeNode.children this@@248))))) :named |0x7fe12996e1a8-PagedBetreeidfy.49:15[$ly=$LZ,this=(PagedBetree.BetreeNode.children this@@248)]| :named |0x7fe12996e1c0-PagedBetreeidfy.49:15[$ly=$LZ,this=(PagedBetree.BetreeNode.children this@@248)]|)) ;; !INST!
(assert (! (=> |b30[PagedBetreeidfy.49:15!1085]| (or (not (and (= (type $LZ) LayerTypeType) (= (type (PagedBetree.BetreeNode.children this@@248)) DatatypeTypeType) (or (|PagedBetree.ChildMap.WF#canCall| (PagedBetree.BetreeNode.children this@@248)) (and (not (= 9 $FunctionContextHeight)) ($Is (PagedBetree.BetreeNode.children this@@248) Tclass.PagedBetree.ChildMap))))) (and (PagedBetree.ChildMap.ChildMap_q (PagedBetree.BetreeNode.children this@@248)) (|Buffers.__default.Total#canCall| (|IMap#Domain| (PagedBetree.ChildMap.mapp (PagedBetree.BetreeNode.children this@@248)))) (or (not (Buffers.__default.Total (|IMap#Domain| (PagedBetree.ChildMap.mapp (PagedBetree.BetreeNode.children this@@248))))) |b41[]|) (or (not (PagedBetree.ChildMap.WF ($LS $LZ) (PagedBetree.BetreeNode.children this@@248))) (and (Buffers.__default.Total (|IMap#Domain| (PagedBetree.ChildMap.mapp (PagedBetree.BetreeNode.children this@@248)))) |b40[]|)) (or (PagedBetree.ChildMap.WF ($LS $LZ) (PagedBetree.BetreeNode.children this@@248)) (not (Buffers.__default.Total (|IMap#Domain| (PagedBetree.ChildMap.mapp (PagedBetree.BetreeNode.children this@@248))))) (not (=> (= (type (|k#0@@0!1333!0| $LZ (PagedBetree.BetreeNode.children this@@248))) (SeqType BoxType)) (=> (and ($Is (|k#0@@0!1333!0| $LZ (PagedBetree.BetreeNode.children this@@248)) Tclass.KeyType.Key) (Buffers.__default.AnyKey (|k#0@@0!1333!0| $LZ (PagedBetree.BetreeNode.children this@@248)))) (PagedBetree.BetreeNode.WF $LZ ($Unbox DatatypeTypeType (MapType0Select (|IMap#Elements| (PagedBetree.ChildMap.mapp (PagedBetree.BetreeNode.children this@@248))) ($Box (|k#0@@0!1333!0| $LZ (PagedBetree.BetreeNode.children this@@248))))))))))))) :named |0x7fe12996e1f8-PagedBetreeidfy.49:15!1085[$ly@@3=$LZ,this@@3=(PagedBetree.BetreeNode.children this@@248)]| :named |0x7fe12996e1e0-PagedBetreeidfy.49:15!1085[$ly@@3=$LZ,this@@3=(PagedBetree.BetreeNode.children this@@248)]|)) ;; !INST!
(assert (! (=> |b28[PagedBetreeidfy.49:15]| (=> (and (= (type ($LS $LZ)) LayerTypeType) (= (type (PagedBetree.BetreeNode.children this@@248)) DatatypeTypeType)) (= (PagedBetree.ChildMap.WF ($LS ($LS $LZ)) (PagedBetree.BetreeNode.children this@@248)) (PagedBetree.ChildMap.WF ($LS $LZ) (PagedBetree.BetreeNode.children this@@248))))) :named |0x7fe12996e218-PagedBetreeidfy.49:15[$ly=($LS $LZ),this=(PagedBetree.BetreeNode.children this@@248)]|)) ;; !INST!
(assert (! (=> |b35[Buffersidfy.16:19!1676]| (or (not (and (= (type (|IMap#Domain| (PagedBetree.ChildMap.mapp (PagedBetree.BetreeNode.children this@@248)))) (MapType0Type BoxType boolType)) (or (|Buffers.__default.Total#canCall| (|IMap#Domain| (PagedBetree.ChildMap.mapp (PagedBetree.BetreeNode.children this@@248)))) ($Is (|IMap#Domain| (PagedBetree.ChildMap.mapp (PagedBetree.BetreeNode.children this@@248))) (TISet Tclass.KeyType.Key))))) (and |b37[Buffersidfy.17:12]| (or (not (Buffers.__default.Total (|IMap#Domain| (PagedBetree.ChildMap.mapp (PagedBetree.BetreeNode.children this@@248))))) |b38[]|) (or (Buffers.__default.Total (|IMap#Domain| (PagedBetree.ChildMap.mapp (PagedBetree.BetreeNode.children this@@248)))) (not (=> (= (type (|k#0@@82!3099!3| (|IMap#Domain| (PagedBetree.ChildMap.mapp (PagedBetree.BetreeNode.children this@@248))))) (SeqType BoxType)) (=> (and ($Is (|k#0@@82!3099!3| (|IMap#Domain| (PagedBetree.ChildMap.mapp (PagedBetree.BetreeNode.children this@@248)))) Tclass.KeyType.Key) (Buffers.__default.AnyKey (|k#0@@82!3099!3| (|IMap#Domain| (PagedBetree.ChildMap.mapp (PagedBetree.BetreeNode.children this@@248)))))) (U_2_bool (MapType0Select (|IMap#Domain| (PagedBetree.ChildMap.mapp (PagedBetree.BetreeNode.children this@@248))) ($Box (|k#0@@82!3099!3| (|IMap#Domain| (PagedBetree.ChildMap.mapp (PagedBetree.BetreeNode.children this@@248)))))))))))))) :named |0x7fe12996e230-Buffersidfy.16:19!1676[keys#0@@1=(IMap#Domain (PagedBetree.ChildMap.mapp (PagedBetree.BetreeNode.children this@@248)))]| :named |0x7fe129973410-Buffersidfy.16:19!1676[keys#0@@1=(IMap#Domain (PagedBetree.ChildMap.mapp (PagedBetree.BetreeNode.children this@@248)))]|)) ;; !INST!
(assert (! (=> |b30[PagedBetreeidfy.49:15!1085]| (or (not (and (= (type ($LS $LZ)) LayerTypeType) (= (type (PagedBetree.BetreeNode.children this@@248)) DatatypeTypeType) (or (|PagedBetree.ChildMap.WF#canCall| (PagedBetree.BetreeNode.children this@@248)) (and (not (= 9 $FunctionContextHeight)) ($Is (PagedBetree.BetreeNode.children this@@248) Tclass.PagedBetree.ChildMap))))) (and (PagedBetree.ChildMap.ChildMap_q (PagedBetree.BetreeNode.children this@@248)) (|Buffers.__default.Total#canCall| (|IMap#Domain| (PagedBetree.ChildMap.mapp (PagedBetree.BetreeNode.children this@@248)))) (or (not (Buffers.__default.Total (|IMap#Domain| (PagedBetree.ChildMap.mapp (PagedBetree.BetreeNode.children this@@248))))) |b41[]|) (or (not (PagedBetree.ChildMap.WF ($LS ($LS $LZ)) (PagedBetree.BetreeNode.children this@@248))) (and (Buffers.__default.Total (|IMap#Domain| (PagedBetree.ChildMap.mapp (PagedBetree.BetreeNode.children this@@248)))) |b39[]|)) (or (PagedBetree.ChildMap.WF ($LS ($LS $LZ)) (PagedBetree.BetreeNode.children this@@248)) (not (Buffers.__default.Total (|IMap#Domain| (PagedBetree.ChildMap.mapp (PagedBetree.BetreeNode.children this@@248))))) (not (=> (= (type (|k#0@@0!1333!0| ($LS $LZ) (PagedBetree.BetreeNode.children this@@248))) (SeqType BoxType)) (=> (and ($Is (|k#0@@0!1333!0| ($LS $LZ) (PagedBetree.BetreeNode.children this@@248)) Tclass.KeyType.Key) (Buffers.__default.AnyKey (|k#0@@0!1333!0| ($LS $LZ) (PagedBetree.BetreeNode.children this@@248)))) (PagedBetree.BetreeNode.WF ($LS $LZ) ($Unbox DatatypeTypeType (MapType0Select (|IMap#Elements| (PagedBetree.ChildMap.mapp (PagedBetree.BetreeNode.children this@@248))) ($Box (|k#0@@0!1333!0| ($LS $LZ) (PagedBetree.BetreeNode.children this@@248))))))))))))) :named |0x7fe12996e250-PagedBetreeidfy.49:15!1085[$ly@@3=($LS $LZ),this@@3=(PagedBetree.BetreeNode.children this@@248)]|)) ;; !INST!
(assert (! (=> |b7[typeInv:U_2_bool]| (= (U_2_bool (bool_2_U (TotalKMMapMod.__default.TerminalValue (Lit TotalKMMapMod.__default.DefaultV)))) (TotalKMMapMod.__default.TerminalValue (Lit TotalKMMapMod.__default.DefaultV)))) :named |0x7fe12995f898-typeInv:U_2_bool[arg0@@3=(TotalKMMapMod.__default.TerminalValue (Lit TotalKMMapMod.__default.DefaultV))]|)) ;; !INST!
(check-sat)
