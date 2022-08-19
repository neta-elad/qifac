(set-option :produce-unsat-cores true)
(set-option :smt.core.minimize true)
(declare-fun |b7[DafnyPreludebpl.1414:30]| () Bool)
(declare-fun |b24[Testidfy.26:5!253]| () Bool)
(declare-fun |b2[DafnyPreludebpl.89:29]| () Bool)
(declare-fun |b34[]| () Bool)
(declare-fun |b13[Testidfy.7:15]| () Bool)
(declare-fun |b29[Commonidfy.10:20!92]| () Bool)
(declare-fun |b30[]| () Bool)
(declare-fun |b20[Testidfy.19:46!221]| () Bool)
(declare-fun |b21[Testidfy.20:15!236]| () Bool)
(declare-fun |b5[funType:IMap#Domain]| () Bool)
(declare-fun |b14[Testidfy.7:15!153]| () Bool)
(declare-fun |b31[]| () Bool)
(declare-fun |b10[unknown.0:0]| () Bool)
(declare-fun |b18[Testidfy.19:46]| () Bool)
(declare-fun |b33[]| () Bool)
(declare-fun |b22[Testidfy.26:5]| () Bool)
(declare-fun |b12[funType:Test.ChildMap.mapp]| () Bool)
(declare-fun |b15[funType:Test.BetreeNode.children]| () Bool)
(declare-fun |b17[Testidfy.14:15!202]| () Bool)
(declare-fun |b27[Testidfy.36:15]| () Bool)
(declare-fun |b19[unknown.0:0!211]| () Bool)
(declare-fun |b32[]| () Bool)
(declare-fun |b11[unknown.0:0!24]| () Bool)
(declare-fun |b38[]| () Bool)
(declare-fun |b9[DafnyPreludebpl.1419:51]| () Bool)
(declare-fun |b4[typeInv:IMapTypeInv0]| () Bool)
(declare-fun |b16[Testidfy.14:15]| () Bool)
(declare-fun |b26[Testidfy.30:15!306]| () Bool)
(declare-fun |b35[Commonidfy.11:12]| () Bool)
(declare-fun |b28[Commonidfy.6:18!76]| () Bool)
(declare-fun |b1[typeInv:U_2_bool]| () Bool)
(declare-fun |b3[funType:$Unbox]| () Bool)
(declare-fun |b23[unknown.0:0!248]| () Bool)
(declare-fun |b25[Testidfy.26:5!273]| () Bool)
(declare-fun |b6[funType:$LS]| () Bool)
(declare-fun |b36[]| () Bool)
(declare-fun |b37[]| () Bool)
(declare-fun |b8[DafnyPreludebpl.1418:51]| () Bool)
(set-info :smt-lib-version |2.6|)
(set-info :category |"industrial"|)
(set-info :boogie-vc-id CheckWellformed$$Test.QueryReceipt.ChildAt)
(set-option :produce-unsat-cores true)
(set-option :smt.core.minimize true)
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
(set-option :timeout 0)
(set-option :rlimit 16350000)
(declare-sort T@U 0)
(declare-sort T@T 0)
(declare-fun bool_2_U (Bool) T@U)
(declare-fun U_2_bool (T@U) Bool)
(declare-fun Lit (T@U) T@U)
(declare-fun $Unbox (T@T T@U) T@U)
(declare-fun type (T@U) T@T)
(declare-fun IMapType (T@T T@T) T@T)
(declare-fun IMapTypeInv0 (T@T) T@T)
(declare-fun |IMap#Domain| (T@U) T@U)
(declare-fun MapType0Type (T@T T@T) T@T)
(declare-fun boolType () T@T)
(declare-fun $LS (T@U) T@U)
(declare-fun LayerTypeType () T@T)
(declare-fun INTERNAL_sub_boogie (Int Int) Int)
(declare-fun INTERNAL_lt_boogie (Int Int) Bool)
(declare-fun INTERNAL_le_boogie (Int Int) Bool)
(declare-fun $IsBox (T@U T@U) Bool)
(declare-fun Tclass._System.___hTotalFunc2 (T@U T@U T@U) T@U)
(declare-fun $Is (T@U T@U) Bool)
(declare-fun HandleTypeType () T@T)
(declare-fun $Box (T@U) T@U)
(declare-fun BoxType () T@T)
(declare-fun TyType () T@T)
(declare-fun Tclass._System.Tuple2 (T@U T@U) T@U)
(declare-fun DatatypeTypeType () T@T)
(declare-fun Test.ChildMap.mapp (T@U) T@U)
(declare-fun Test.ChildMap.WF (T@U T@U) Bool)
(declare-fun $LZ () T@U)
(declare-fun Test.BetreeNode.WF (T@U T@U) Bool)
(declare-fun MapType0Select (T@U T@U) T@U)
(declare-fun |k#0@@0!906!110| (T@U T@U) T@U)
(declare-fun |IMap#Elements| (T@U) T@U)
(declare-fun Common.__default.AnyKey (T@U) Bool)
(declare-fun Tclass.Common.Key () T@U)
(declare-fun SeqType (T@T) T@T)
(declare-fun Common.__default.TotalSet (T@U) Bool)
(declare-fun |Test.BetreeNode.WF#canCall| (T@U) Bool)
(declare-fun Test.ChildMap.ChildMap_q (T@U) Bool)
(declare-fun |Common.__default.AnyKey#canCall| (T@U) Bool)
(declare-fun |Common.__default.TotalSet#canCall| (T@U) Bool)
(declare-fun Tclass.Test.ChildMap () T@U)
(declare-fun $FunctionContextHeight () Int)
(declare-fun |Test.ChildMap.WF#canCall| (T@U) Bool)
(declare-fun Test.BetreeNode.children (T@U) T@U)
(declare-fun Test.BetreeNode.BetreeNode_q (T@U) Bool)
(declare-fun Tclass.Test.BetreeNode () T@U)
(declare-fun |#Test.QueryReceiptLine.QueryReceiptLine| (T@U) T@U)
(declare-fun |##Test.QueryReceiptLine.QueryReceiptLine| () T@U)
(declare-fun DatatypeCtorId (T@U) T@U)
(declare-fun Test.QueryReceiptLine.QueryReceiptLine_q (T@U) Bool)
(declare-fun |a#1#0#0@@0!944!113| (T@U) T@U)
(declare-fun Test.QueryReceiptLine.node (T@U) T@U)
(declare-fun Test.QueryReceiptLine.WF (T@U) Bool)
(declare-fun Tclass.Test.QueryReceiptLine () T@U)
(declare-fun |Test.QueryReceiptLine.WF#canCall| (T@U) Bool)
(declare-fun |#Test.QueryReceipt.QueryReceipt| (T@U T@U T@U) T@U)
(declare-fun |##Test.QueryReceipt.QueryReceipt| () T@U)
(declare-fun Test.QueryReceipt.QueryReceipt_q (T@U) Bool)
(declare-fun |a#1#2#0!964!115| (T@U) T@U)
(declare-fun |a#1#1#0@@0!964!116| (T@U) T@U)
(declare-fun |a#1#0#0@@1!964!114| (T@U) T@U)
(declare-fun Tclass.Test.QueryReceipt () T@U)
(declare-fun TSeq (T@U) T@U)
(declare-fun Test.QueryReceipt.key (T@U) T@U)
(declare-fun Test.QueryReceipt.Structure (T@U) Bool)
(declare-fun |Seq#Length| (T@U) Int)
(declare-fun Test.QueryReceipt.lines (T@U) T@U)
(declare-fun |i#0@@0!985!117| (T@U) Int)
(declare-fun |Seq#Index| (T@U Int) T@U)
(declare-fun |Test.BetreeNode#Equal| (T@U T@U) Bool)
(declare-fun Test.QueryReceipt.root (T@U) T@U)
(declare-fun LitInt (Int) Int)
(declare-fun |$IsA#Test.BetreeNode| (T@U) Bool)
(declare-fun |Test.QueryReceipt.Structure#canCall| (T@U) Bool)
(declare-fun Test.QueryReceipt.AllLinesWF (T@U) Bool)
(declare-fun |i#0@@2!995!119| (T@U) Int)
(declare-fun |Test.QueryReceipt.AllLinesWF#canCall| (T@U) Bool)
(declare-fun |k#0@@2!1032!121| (T@U) T@U)
(declare-fun TISet (T@U) T@U)
(declare-fun this@@27 () T@U)
(declare-fun |i#0@@9| () Int)
(declare-fun MapType4Select (T@U T@U T@U) T@U)
(declare-fun $f@@11!1008!124 () T@U)
(declare-fun $o@@25!1008!123 () T@U)
(declare-fun $_Frame@0@@0 () T@U)
(declare-fun FieldType (T@T) T@T)
(declare-fun FieldTypeInv0 (T@T) T@T)
(declare-fun refType () T@T)
(declare-fun |b$reqreads#0@0| () Bool)
(declare-fun $f@@12!1009!125 () T@U)
(declare-fun $o@@26!1009!126 () T@U)
(declare-fun |b$reqreads#1@0| () Bool)
(declare-fun ControlFlow (Int Int) Int)
(declare-fun |k#1@@3!1012!128| () T@U)
(declare-fun |k#0@@3!1010!127| () T@U)
(declare-fun $IsAlloc (T@U T@U T@U) Bool)
(declare-fun $Heap () T@U)
(declare-fun |lambda#11| (T@U T@U T@U Bool) T@U)
(declare-fun alloc () T@U)
(declare-fun null () T@U)
(declare-fun $_Frame@0 () T@U)
(assert (! |b1[typeInv:U_2_bool]|))
(assert (! |b2[DafnyPreludebpl.89:29]|))
(assert (! |b3[funType:$Unbox]|))
(assert (! |b4[typeInv:IMapTypeInv0]|))
(assert (! |b5[funType:IMap#Domain]|))
(assert (! |b7[DafnyPreludebpl.1414:30]|))
(assert (! |b8[DafnyPreludebpl.1418:51]|))
(assert (! |b9[DafnyPreludebpl.1419:51]|))
(assert (! |b12[funType:Test.ChildMap.mapp]|))
(assert (! |b13[Testidfy.7:15]|))
(assert (! (= (type $LZ) LayerTypeType)))
(assert (! (or (not (<= 5 $FunctionContextHeight)) |b14[Testidfy.7:15!153]|)))
(assert (! |b15[funType:Test.BetreeNode.children]|))
(assert (! (or (not (<= 5 $FunctionContextHeight)) |b17[Testidfy.14:15!202]|)))
(assert (! |b19[unknown.0:0!211]|))
(assert (! |b20[Testidfy.19:46!221]|))
(assert (! (or (not (<= 6 $FunctionContextHeight)) |b21[Testidfy.20:15!236]|)))
(assert (! |b23[unknown.0:0!248]|))
(assert (! |b24[Testidfy.26:5!253]|))
(assert (! |b25[Testidfy.26:5!273]|))
(assert (! (or (not (<= 8 $FunctionContextHeight)) |b26[Testidfy.30:15!306]|)))
(assert (! (or (not (<= 7 $FunctionContextHeight)) |b27[Testidfy.36:15]|)))
(assert (! (or (not true) |b28[Commonidfy.6:18!76]|)))
(assert (! (or (not true) |b29[Commonidfy.10:20!92]|)))
(assert (! (= (type this@@27) DatatypeTypeType)))
(assert (! ($Is this@@27 Tclass.Test.QueryReceipt)))
(assert (! (INTERNAL_le_boogie 0 |i#0@@9|)))
(assert (! (= 9 $FunctionContextHeight)))
(assert (! (or |b$reqreads#0@0| (not (=> (and (= (type $o@@25!1008!123) refType) (= (type $f@@11!1008!124) (FieldType (FieldTypeInv0 (type $f@@11!1008!124)))) false) (U_2_bool (MapType4Select $_Frame@0@@0 $o@@25!1008!123 $f@@11!1008!124)))))))
(assert (! (Test.QueryReceipt.AllLinesWF this@@27)))
(assert (! (or |b$reqreads#1@0| (not (=> (and (= (type $o@@26!1009!126) refType) (= (type $f@@12!1009!125) (FieldType (FieldTypeInv0 (type $f@@12!1009!125)))) false) (U_2_bool (MapType4Select $_Frame@0@@0 $o@@26!1009!126 $f@@12!1009!125)))))))
(assert (! (Test.QueryReceipt.Structure this@@27)))
(assert (! (INTERNAL_lt_boogie |i#0@@9| (INTERNAL_sub_boogie (|Seq#Length| (Test.QueryReceipt.lines this@@27)) 1))))
(assert (! (or (not (=> (= (ControlFlow 0 39141) (- 0 56539)) |b$reqreads#0@0|)) (and |b$reqreads#0@0| (or (not (=> (= (ControlFlow 0 39141) (- 0 56540)) |b$reqreads#1@0|)) (and |b$reqreads#1@0| (or (not (=> (= (ControlFlow 0 39141) 39145) true)) (and (= (ControlFlow 0 39141) 39147) (= $_Frame@0 (|lambda#11| null $Heap alloc false)) (Test.QueryReceipt.QueryReceipt_q this@@27) (or (not (=> (= (ControlFlow 0 39147) (- 0 56573)) (and (<= 0 |i#0@@9|) (< |i#0@@9| (|Seq#Length| (Test.QueryReceipt.lines this@@27)))))) (and (Test.QueryReceiptLine.QueryReceiptLine_q ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))) (or (not (=> (= (ControlFlow 0 39147) (- 0 56605)) (Test.BetreeNode.BetreeNode_q (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))))) (and (Test.BetreeNode.BetreeNode_q (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))) ($IsAlloc (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))) Tclass.Test.ChildMap $Heap) (|Test.ChildMap.WF#canCall| (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))))) (Test.QueryReceipt.QueryReceipt_q this@@27) (Test.QueryReceiptLine.QueryReceiptLine_q ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))) (|Test.ChildMap.WF#canCall| (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))))) (or (and (= (ControlFlow 0 39147) (- 0 56701)) (|Test.ChildMap.WF#canCall| (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))))) (not (Test.ChildMap.WF ($LS $LZ) (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))))) (|Common.__default.TotalSet#canCall| (|IMap#Domain| (Test.ChildMap.mapp (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))))))) (not (Common.__default.TotalSet (|IMap#Domain| (Test.ChildMap.mapp (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))))))) (not (=> (= (type |k#0@@3!1010!127|) (SeqType BoxType)) (=> (and ($Is |k#0@@3!1010!127| Tclass.Common.Key) (Common.__default.AnyKey |k#0@@3!1010!127|)) (U_2_bool (MapType0Select (|IMap#Domain| (Test.ChildMap.mapp (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))))) ($Box |k#0@@3!1010!127|))))))) (and (= (ControlFlow 0 39147) (- 0 56869)) (|Test.ChildMap.WF#canCall| (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))))) (not (Test.ChildMap.WF ($LS $LZ) (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))))) (not (=> (= (type |k#1@@3!1012!128|) (SeqType BoxType)) (=> (and ($Is |k#1@@3!1012!128| Tclass.Common.Key) (Common.__default.AnyKey |k#1@@3!1012!128|)) (Test.BetreeNode.WF ($LS ($LS $LZ)) ($Unbox DatatypeTypeType (MapType0Select (|IMap#Elements| (Test.ChildMap.mapp (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))))) ($Box |k#1@@3!1012!128|)))))))) (not (=> (and (Test.ChildMap.WF ($LS ($LS $LZ)) (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))))) (Test.QueryReceipt.QueryReceipt_q this@@27)) (and (=> (= (ControlFlow 0 39147) (- 0 57033)) (and (<= 0 |i#0@@9|) (< |i#0@@9| (|Seq#Length| (Test.QueryReceipt.lines this@@27))))) (=> (and (<= 0 |i#0@@9|) (< |i#0@@9| (|Seq#Length| (Test.QueryReceipt.lines this@@27)))) (=> (Test.QueryReceiptLine.QueryReceiptLine_q ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))) (and (=> (= (ControlFlow 0 39147) (- 0 57065)) (Test.BetreeNode.BetreeNode_q (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))))) (=> (Test.BetreeNode.BetreeNode_q (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))) (=> (Test.ChildMap.ChildMap_q (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))))) (=> (and (Test.QueryReceipt.QueryReceipt_q this@@27) (= (ControlFlow 0 39147) (- 0 57103))) (U_2_bool (MapType0Select (|IMap#Domain| (Test.ChildMap.mapp (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))))) ($Box (Test.QueryReceipt.key this@@27))))))))))))))))))))))))))
(assert (! (=> (! |b4[typeInv:IMapTypeInv0]|) (= (IMapTypeInv0 (IMapType BoxType BoxType)) BoxType))))
(assert (! (=> (! |b2[DafnyPreludebpl.89:29]|) (= (Lit (bool_2_U true)) (bool_2_U true)))))
(assert (! (=> (! |b24[Testidfy.26:5!253]|) (=> (and (= (type (|a#1#0#0@@1!964!114| this@@27)) (SeqType BoxType)) (= (type (|a#1#1#0@@0!964!116| this@@27)) DatatypeTypeType) (= (type (|a#1#2#0!964!115| this@@27)) (SeqType BoxType))) (= ($Is (|#Test.QueryReceipt.QueryReceipt| (|a#1#0#0@@1!964!114| this@@27) (|a#1#1#0@@0!964!116| this@@27) (|a#1#2#0!964!115| this@@27)) Tclass.Test.QueryReceipt) (and ($Is (|a#1#0#0@@1!964!114| this@@27) Tclass.Common.Key) ($Is (|a#1#1#0@@0!964!116| this@@27) Tclass.Test.BetreeNode) ($Is (|a#1#2#0!964!115| this@@27) (TSeq Tclass.Test.QueryReceiptLine))))))))
(assert (! (=> (! |b1[typeInv:U_2_bool]|) (= (U_2_bool (bool_2_U true)) true))))
(assert (! (=> (! |b19[unknown.0:0!211]|) (or (not (and (= (type ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))) DatatypeTypeType) (Test.QueryReceiptLine.QueryReceiptLine_q ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))))) (and (= (type (|a#1#0#0@@0!944!113| ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))) DatatypeTypeType) (= ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)) (|#Test.QueryReceiptLine.QueryReceiptLine| (|a#1#0#0@@0!944!113| ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))))))))))
(assert (! (=> |b32[]| (=> (! (INTERNAL_le_boogie 0 |i#0@@9|)) (and (Test.QueryReceipt.QueryReceipt_q this@@27) (=> (INTERNAL_lt_boogie |i#0@@9| (|Seq#Length| (Test.QueryReceipt.lines this@@27))) (and (Test.QueryReceipt.QueryReceipt_q this@@27) (|Test.QueryReceiptLine.WF#canCall| ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))))))))))
(assert (! (=> (! |b3[funType:$Unbox]|) (= (type ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))) (type this@@27)))))
(assert (! (=> |b26[Testidfy.30:15!306]| (or (not (and (! (= (type this@@27) DatatypeTypeType)) (or (|Test.QueryReceipt.Structure#canCall| this@@27) (and (not (= 8 $FunctionContextHeight)) (! ($Is this@@27 Tclass.Test.QueryReceipt)))))) (and (Test.QueryReceipt.QueryReceipt_q this@@27) (or (not (INTERNAL_lt_boogie 0 (|Seq#Length| (Test.QueryReceipt.lines this@@27)))) (and (|$IsA#Test.BetreeNode| (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@27) (LitInt 0))))) (|$IsA#Test.BetreeNode| (Test.QueryReceipt.root this@@27)) (Test.QueryReceipt.QueryReceipt_q this@@27) (Test.QueryReceiptLine.QueryReceiptLine_q ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@27) (LitInt 0)))) (Test.QueryReceipt.QueryReceipt_q this@@27) (or (not (|Test.BetreeNode#Equal| (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@27) (LitInt 0)))) (Test.QueryReceipt.root this@@27))) |b33[]|))) (or (not (! (Test.QueryReceipt.Structure this@@27))) (and (and (INTERNAL_lt_boogie 0 (|Seq#Length| (Test.QueryReceipt.lines this@@27))) (|Test.BetreeNode#Equal| (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@27) (LitInt 0)))) (Test.QueryReceipt.root this@@27))) |b34[]|)) (or (! (Test.QueryReceipt.Structure this@@27)) (not (and (INTERNAL_lt_boogie 0 (|Seq#Length| (Test.QueryReceipt.lines this@@27))) (|Test.BetreeNode#Equal| (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@27) (LitInt 0)))) (Test.QueryReceipt.root this@@27)))) (not (=> (and (INTERNAL_le_boogie 0 (|i#0@@0!985!117| this@@27)) (INTERNAL_lt_boogie (|i#0@@0!985!117| this@@27) (|Seq#Length| (Test.QueryReceipt.lines this@@27)))) (= (Test.BetreeNode.BetreeNode_q (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@27) (|i#0@@0!985!117| this@@27))))) (INTERNAL_lt_boogie (|i#0@@0!985!117| this@@27) (INTERNAL_sub_boogie (|Seq#Length| (Test.QueryReceipt.lines this@@27)) 1)))))))))))
(assert (! (=> |b29[Commonidfy.10:20!92]| (or (not (and (= (type (|IMap#Domain| (Test.ChildMap.mapp (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))))))) (MapType0Type BoxType boolType)) (or (|Common.__default.TotalSet#canCall| (|IMap#Domain| (Test.ChildMap.mapp (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))))))) ($Is (|IMap#Domain| (Test.ChildMap.mapp (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))))) (TISet Tclass.Common.Key))))) (and |b35[Commonidfy.11:12]| (or (not (Common.__default.TotalSet (|IMap#Domain| (Test.ChildMap.mapp (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))))))) |b36[]|) (or (Common.__default.TotalSet (|IMap#Domain| (Test.ChildMap.mapp (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))))))) (not (=> (= (type (|k#0@@2!1032!121| (|IMap#Domain| (Test.ChildMap.mapp (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))))))) (SeqType BoxType)) (=> (and ($Is (|k#0@@2!1032!121| (|IMap#Domain| (Test.ChildMap.mapp (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))))))) Tclass.Common.Key) (Common.__default.AnyKey (|k#0@@2!1032!121| (|IMap#Domain| (Test.ChildMap.mapp (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))))))))) (U_2_bool (MapType0Select (|IMap#Domain| (Test.ChildMap.mapp (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))))) ($Box (|k#0@@2!1032!121| (|IMap#Domain| (Test.ChildMap.mapp (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))))))))))))))))))
(assert (! (=> |b37[]| (=> (and (! (INTERNAL_le_boogie 0 |i#0@@9|)) (INTERNAL_lt_boogie |i#0@@9| (|Seq#Length| (Test.QueryReceipt.lines this@@27)))) (Test.QueryReceiptLine.WF ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))))))
(assert (! (=> |b34[]| (=> (and (! (INTERNAL_le_boogie 0 |i#0@@9|)) (INTERNAL_lt_boogie |i#0@@9| (|Seq#Length| (Test.QueryReceipt.lines this@@27)))) (= (Test.BetreeNode.BetreeNode_q (Test.QueryReceiptLine.node ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))) (! (INTERNAL_lt_boogie |i#0@@9| (INTERNAL_sub_boogie (|Seq#Length| (Test.QueryReceipt.lines this@@27)) 1))))))))
(assert (! (=> (! |b13[Testidfy.7:15]|) (=> (and (! (= (type $LZ) LayerTypeType)) (= (type (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))))) DatatypeTypeType)) (= (Test.ChildMap.WF ($LS $LZ) (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))))) (Test.ChildMap.WF $LZ (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))))))))))
(assert (! (=> (! |b20[Testidfy.19:46!221]|) (=> (= (type (|a#1#0#0@@0!944!113| ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))) DatatypeTypeType) (= (Test.QueryReceiptLine.node (|#Test.QueryReceiptLine.QueryReceiptLine| (|a#1#0#0@@0!944!113| ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))))) (|a#1#0#0@@0!944!113| ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))))))))
(assert (! (=> (! |b8[DafnyPreludebpl.1418:51]|) (= (INTERNAL_lt_boogie |i#0@@9| (|Seq#Length| (Test.QueryReceipt.lines this@@27))) (< |i#0@@9| (|Seq#Length| (Test.QueryReceipt.lines this@@27)))))))
(assert (! (=> |b17[Testidfy.14:15!202]| (=> (and (! (= (type $LZ) LayerTypeType)) (= (type (Test.QueryReceiptLine.node (|#Test.QueryReceiptLine.QueryReceiptLine| (|a#1#0#0@@0!944!113| ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))))) DatatypeTypeType) (or (|Test.BetreeNode.WF#canCall| (Test.QueryReceiptLine.node (|#Test.QueryReceiptLine.QueryReceiptLine| (|a#1#0#0@@0!944!113| ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))))) (and (not (= 5 $FunctionContextHeight)) ($Is (Test.QueryReceiptLine.node (|#Test.QueryReceiptLine.QueryReceiptLine| (|a#1#0#0@@0!944!113| ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))))) Tclass.Test.BetreeNode)))) (and (=> (U_2_bool (Lit (bool_2_U true))) (=> (Test.BetreeNode.BetreeNode_q (Test.QueryReceiptLine.node (|#Test.QueryReceiptLine.QueryReceiptLine| (|a#1#0#0@@0!944!113| ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))))) (|Test.ChildMap.WF#canCall| (Test.BetreeNode.children (Test.QueryReceiptLine.node (|#Test.QueryReceiptLine.QueryReceiptLine| (|a#1#0#0@@0!944!113| ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))))))))) (= (Test.BetreeNode.WF ($LS $LZ) (Test.QueryReceiptLine.node (|#Test.QueryReceiptLine.QueryReceiptLine| (|a#1#0#0@@0!944!113| ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))))) (and true (=> (Test.BetreeNode.BetreeNode_q (Test.QueryReceiptLine.node (|#Test.QueryReceiptLine.QueryReceiptLine| (|a#1#0#0@@0!944!113| ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))))) (Test.ChildMap.WF $LZ (Test.BetreeNode.children (Test.QueryReceiptLine.node (|#Test.QueryReceiptLine.QueryReceiptLine| (|a#1#0#0@@0!944!113| ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))))))))))))))
(assert (! (=> |b21[Testidfy.20:15!236]| (=> (and (= (type ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))) DatatypeTypeType) (or (|Test.QueryReceiptLine.WF#canCall| ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))) (and (not (= 6 $FunctionContextHeight)) ($Is ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)) Tclass.Test.QueryReceiptLine)))) (and (=> (U_2_bool (Lit (bool_2_U true))) (and (Test.QueryReceiptLine.QueryReceiptLine_q ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))) (|Test.BetreeNode.WF#canCall| (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))))) (= (Test.QueryReceiptLine.WF ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))) (and true (Test.BetreeNode.WF ($LS $LZ) (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))))))))))
(assert (! (=> |b27[Testidfy.36:15]| (or (not (and (! (= (type this@@27) DatatypeTypeType)) (or (|Test.QueryReceipt.AllLinesWF#canCall| this@@27) (and (not (= 7 $FunctionContextHeight)) (! ($Is this@@27 Tclass.Test.QueryReceipt)))))) (and (or (not (U_2_bool (Lit (bool_2_U true)))) |b32[]|) (or (not (! (Test.QueryReceipt.AllLinesWF this@@27))) (and true |b37[]|)) (or (! (Test.QueryReceipt.AllLinesWF this@@27)) (not true) (not (=> (and (INTERNAL_le_boogie 0 (|i#0@@2!995!119| this@@27)) (INTERNAL_lt_boogie (|i#0@@2!995!119| this@@27) (|Seq#Length| (Test.QueryReceipt.lines this@@27)))) (Test.QueryReceiptLine.WF ($Unbox DatatypeTypeType (|Seq#Index| (Test.QueryReceipt.lines this@@27) (|i#0@@2!995!119| this@@27))))))))))))
(assert (! (=> (! |b15[funType:Test.BetreeNode.children]|) (= (type (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))))) DatatypeTypeType))))
(assert (! (=> (! |b7[DafnyPreludebpl.1414:30]|) (= (INTERNAL_sub_boogie (|Seq#Length| (Test.QueryReceipt.lines this@@27)) 1) (- (|Seq#Length| (Test.QueryReceipt.lines this@@27)) 1)))))
(assert (! (=> (! |b8[DafnyPreludebpl.1418:51]|) (= (! (INTERNAL_lt_boogie |i#0@@9| (INTERNAL_sub_boogie (|Seq#Length| (Test.QueryReceipt.lines this@@27)) 1))) (< |i#0@@9| (INTERNAL_sub_boogie (|Seq#Length| (Test.QueryReceipt.lines this@@27)) 1))))))
(assert (! (=> (! |b25[Testidfy.26:5!273]|) (=> (and (= (type (|a#1#0#0@@1!964!114| this@@27)) (SeqType BoxType)) (= (type (|a#1#1#0@@0!964!116| this@@27)) DatatypeTypeType) (= (type (|a#1#2#0!964!115| this@@27)) (SeqType BoxType))) (= (Test.QueryReceipt.key (|#Test.QueryReceipt.QueryReceipt| (|a#1#0#0@@1!964!114| this@@27) (|a#1#1#0@@0!964!116| this@@27) (|a#1#2#0!964!115| this@@27))) (|a#1#0#0@@1!964!114| this@@27))))))
(assert (! (=> (! |b9[DafnyPreludebpl.1419:51]|) (= (! (INTERNAL_le_boogie 0 |i#0@@9|)) (<= 0 |i#0@@9|)))))
(assert (! (=> |b36[]| (=> (= (type (Test.QueryReceipt.key this@@27)) (SeqType BoxType)) (=> (and ($Is (Test.QueryReceipt.key this@@27) Tclass.Common.Key) (Common.__default.AnyKey (Test.QueryReceipt.key this@@27))) (U_2_bool (MapType0Select (|IMap#Domain| (Test.ChildMap.mapp (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))))) ($Box (Test.QueryReceipt.key this@@27)))))))))
(assert (! (=> |b14[Testidfy.7:15!153]| (or (not (and (! (= (type $LZ) LayerTypeType)) (= (type (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))))) DatatypeTypeType) (or (|Test.ChildMap.WF#canCall| (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))))) (and (not (= 5 $FunctionContextHeight)) ($Is (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))) Tclass.Test.ChildMap))))) (and (Test.ChildMap.ChildMap_q (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))))) (|Common.__default.TotalSet#canCall| (|IMap#Domain| (Test.ChildMap.mapp (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))))))) (or (not (Common.__default.TotalSet (|IMap#Domain| (Test.ChildMap.mapp (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))))))) |b30[]|) (or (not (Test.ChildMap.WF ($LS $LZ) (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))))) (and (Common.__default.TotalSet (|IMap#Domain| (Test.ChildMap.mapp (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))))))) |b38[]|)) (or (Test.ChildMap.WF ($LS $LZ) (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))))) (not (Common.__default.TotalSet (|IMap#Domain| (Test.ChildMap.mapp (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))))))) (not (=> (= (type (|k#0@@0!906!110| (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))) $LZ)) (SeqType BoxType)) (=> (and ($Is (|k#0@@0!906!110| (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))) $LZ) Tclass.Common.Key) (Common.__default.AnyKey (|k#0@@0!906!110| (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))) $LZ))) (Test.BetreeNode.WF $LZ ($Unbox DatatypeTypeType (MapType0Select (|IMap#Elements| (Test.ChildMap.mapp (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))))) ($Box (|k#0@@0!906!110| (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))) $LZ))))))))))))))
(assert (! (=> (! |b23[unknown.0:0!248]|) (or (not (and (! (= (type this@@27) DatatypeTypeType)) (Test.QueryReceipt.QueryReceipt_q this@@27))) (and (= (type (|a#1#0#0@@1!964!114| this@@27)) (SeqType BoxType)) (= (type (|a#1#1#0@@0!964!116| this@@27)) DatatypeTypeType) (= (type (|a#1#2#0!964!115| this@@27)) (SeqType BoxType)) (= this@@27 (|#Test.QueryReceipt.QueryReceipt| (|a#1#0#0@@1!964!114| this@@27) (|a#1#1#0@@0!964!116| this@@27) (|a#1#2#0!964!115| this@@27))))))))
(assert (! (=> (! |b5[funType:IMap#Domain]|) (= (type (|IMap#Domain| (Test.ChildMap.mapp (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))))))) (MapType0Type (IMapTypeInv0 (type (Test.ChildMap.mapp (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))))))) boolType)))))
(assert (! (=> |b28[Commonidfy.6:18!76]| (=> (and (= (type (|a#1#0#0@@1!964!114| this@@27)) (SeqType BoxType)) (or (|Common.__default.AnyKey#canCall| (|a#1#0#0@@1!964!114| this@@27)) ($Is (|a#1#0#0@@1!964!114| this@@27) Tclass.Common.Key))) (= (Common.__default.AnyKey (|a#1#0#0@@1!964!114| this@@27)) (U_2_bool (Lit (bool_2_U true))))))))
(assert (! (=> (! |b12[funType:Test.ChildMap.mapp]|) (= (type (Test.ChildMap.mapp (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))))) (IMapType BoxType BoxType)))))
(check-sat)
;;! DafnyPreludebpl.1414:30[y@@13=1,x@@43=(Seq#Length (Test.QueryReceipt.lines this@@27))]
;;! DafnyPreludebpl.1414:30
;;! y@@13
;;! 1
;;! x@@43
;;! (|Seq#Length| (Test.QueryReceipt.lines this@@27))
;;! ###
;;! DafnyPreludebpl.1418:51[x@@47=i#0@@9,y@@17=(INTERNAL_sub_boogie (Seq#Length (Test.QueryReceipt.lines this@@27)) 1)]
;;! DafnyPreludebpl.1418:51
;;! x@@47
;;! |i#0@@9|
;;! y@@17
;;! (INTERNAL_sub_boogie (|Seq#Length| (Test.QueryReceipt.lines this@@27)) 1)
;;! ###
;;! DafnyPreludebpl.1419:51[x@@48=0,y@@18=i#0@@9]
;;! DafnyPreludebpl.1419:51
;;! x@@48
;;! 0
;;! y@@18
;;! |i#0@@9|
;;! ###
;;! unknown.0:0!248[d@@29=this@@27]
;;! unknown.0:0!248
;;! d@@29
;;! this@@27
;;! ###
;;! Testidfy.30:15!306[this@@17=this@@27]
;;! Testidfy.30:15!306
;;! this@@17
;;! this@@27
;;! ###
;;! Testidfy.36:15[this@@21=this@@27]
;;! Testidfy.36:15
;;! this@@21
;;! this@@27
;;! ###
;;! Testidfy.26:5!273[a#5#1#0@@0=(a#1#1#0@@0!964!116 this@@27),a#5#0#0@@2=(a#1#0#0@@1!964!114 this@@27),a#5#2#0=(a#1#2#0!964!115 this@@27)]
;;! Testidfy.26:5!273
;;! |a#5#1#0@@0|
;;! (|a#1#1#0@@0!964!116| this@@27)
;;! |a#5#0#0@@2|
;;! (|a#1#0#0@@1!964!114| this@@27)
;;! |a#5#2#0|
;;! (|a#1#2#0!964!115| this@@27)
;;! ###
;;! Testidfy.26:5!253[a#2#2#0=(a#1#2#0!964!115 this@@27),a#2#1#0@@0=(a#1#1#0@@0!964!116 this@@27),a#2#0#0@@1=(a#1#0#0@@1!964!114 this@@27)]
;;! Testidfy.26:5!253
;;! |a#2#2#0|
;;! (|a#1#2#0!964!115| this@@27)
;;! |a#2#1#0@@0|
;;! (|a#1#1#0@@0!964!116| this@@27)
;;! |a#2#0#0@@1|
;;! (|a#1#0#0@@1!964!114| this@@27)
;;! ###
;;! unknown.0:0!211[d@@24=($Unbox (type this@@27) (Seq#Index (Test.QueryReceipt.lines this@@27) i#0@@9))]
;;! unknown.0:0!211
;;! d@@24
;;! ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))
;;! ###
;;! funType:$Unbox[arg0@@34=(Seq#Index (Test.QueryReceipt.lines this@@27) i#0@@9),T@@0=(type this@@27)]
;;! funType:$Unbox
;;! arg0@@34
;;! (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)
;;! T@@0
;;! (type this@@27)
;;! ###
;;! Testidfy.37:20!1[i#0@@2=i#0@@9,this@@21=this@@27]
;;! Testidfy.37:20!1
;;! |i#0@@2|
;;! |i#0@@9|
;;! this@@21
;;! this@@27
;;! ###
;;! Testidfy.33:20!305[i#0@@0=i#0@@9,this@@17=this@@27]
;;! Testidfy.33:20!305
;;! |i#0@@0|
;;! |i#0@@9|
;;! this@@17
;;! this@@27
;;! ###
;;! Testidfy.19:46!221[a#5#0#0@@1=(a#1#0#0@@0!944!113 ($Unbox (type this@@27) (Seq#Index (Test.QueryReceipt.lines this@@27) i#0@@9)))]
;;! Testidfy.19:46!221
;;! |a#5#0#0@@1|
;;! (|a#1#0#0@@0!944!113| ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))
;;! ###
;;! DafnyPreludebpl.1418:51[x@@47=i#0@@9,y@@17=(Seq#Length (Test.QueryReceipt.lines this@@27))]
;;! DafnyPreludebpl.1418:51
;;! x@@47
;;! |i#0@@9|
;;! y@@17
;;! (|Seq#Length| (Test.QueryReceipt.lines this@@27))
;;! ###
;;! Testidfy.20:15!236[this@@13=($Unbox (type this@@27) (Seq#Index (Test.QueryReceipt.lines this@@27) i#0@@9))]
;;! Testidfy.20:15!236
;;! this@@13
;;! ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))
;;! ###
;;! funType:Test.BetreeNode.children[arg0@@174=(Test.QueryReceiptLine.node ($Unbox (type this@@27) (Seq#Index (Test.QueryReceipt.lines this@@27) i#0@@9)))]
;;! funType:Test.BetreeNode.children
;;! arg0@@174
;;! (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))
;;! ###
;;! Commonidfy.10:20!92[keys#0@@1=(IMap#Domain (Test.ChildMap.mapp (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (Seq#Index (Test.QueryReceipt.lines this@@27) i#0@@9))))))]
;;! Commonidfy.10:20!92
;;! |keys#0@@1|
;;! (|IMap#Domain| (Test.ChildMap.mapp (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))))))
;;! ###
;;! Testidfy.7:15[$ly=$LZ,this=(Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (Seq#Index (Test.QueryReceipt.lines this@@27) i#0@@9))))]
;;! Testidfy.7:15
;;! $ly
;;! $LZ
;;! this
;;! (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))))
;;! ###
;;! Testidfy.7:15!153[$ly@@3=$LZ,this@@3=(Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (Seq#Index (Test.QueryReceipt.lines this@@27) i#0@@9))))]
;;! Testidfy.7:15!153
;;! $ly@@3
;;! $LZ
;;! this@@3
;;! (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))))
;;! ###
;;! funType:IMap#Domain[arg0@@57=(Test.ChildMap.mapp (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (Seq#Index (Test.QueryReceipt.lines this@@27) i#0@@9)))))]
;;! funType:IMap#Domain
;;! arg0@@57
;;! (Test.ChildMap.mapp (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))))
;;! ###
;;! funType:Test.ChildMap.mapp[arg0@@171=(Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (Seq#Index (Test.QueryReceipt.lines this@@27) i#0@@9))))]
;;! funType:Test.ChildMap.mapp
;;! arg0@@171
;;! (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))))
;;! ###
;;! typeInv:IMapTypeInv0[arg0@@46=BoxType,arg1@@12=BoxType]
;;! typeInv:IMapTypeInv0
;;! arg0@@46
;;! BoxType
;;! arg1@@12
;;! BoxType
;;! ###
;;! DafnyPreludebpl.89:29[x@@8=(bool_2_U true)]
;;! DafnyPreludebpl.89:29
;;! x@@8
;;! (bool_2_U true)
;;! ###
;;! typeInv:U_2_bool[arg0@@3=true]
;;! typeInv:U_2_bool
;;! arg0@@3
;;! true
;;! ###
;;! Testidfy.37:20[i#0@@1=i#0@@9,this@@21=this@@27]
;;! Testidfy.37:20
;;! |i#0@@1|
;;! |i#0@@9|
;;! this@@21
;;! this@@27
;;! ###
;;! Testidfy.14:15!202[$ly@@9=$LZ,this@@9=(Test.QueryReceiptLine.node (#Test.QueryReceiptLine.QueryReceiptLine (a#1#0#0@@0!944!113 ($Unbox (type this@@27) (Seq#Index (Test.QueryReceipt.lines this@@27) i#0@@9)))))]
;;! Testidfy.14:15!202
;;! $ly@@9
;;! $LZ
;;! this@@9
;;! (Test.QueryReceiptLine.node (|#Test.QueryReceiptLine.QueryReceiptLine| (|a#1#0#0@@0!944!113| ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|)))))
;;! ###
;;! Commonidfy.11:12!90[k#0@@2=(Test.QueryReceipt.key this@@27),keys#0@@1=(IMap#Domain (Test.ChildMap.mapp (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (Seq#Index (Test.QueryReceipt.lines this@@27) i#0@@9))))))]
;;! Commonidfy.11:12!90
;;! |k#0@@2|
;;! (Test.QueryReceipt.key this@@27)
;;! |keys#0@@1|
;;! (|IMap#Domain| (Test.ChildMap.mapp (Test.BetreeNode.children (Test.QueryReceiptLine.node ($Unbox (type this@@27) (|Seq#Index| (Test.QueryReceipt.lines this@@27) |i#0@@9|))))))
;;! ###
;;! Commonidfy.6:18!76[key#0@@1=(a#1#0#0@@1!964!114 this@@27)]
;;! Commonidfy.6:18!76
;;! |key#0@@1|
;;! (|a#1#0#0@@1!964!114| this@@27)
;;! ###
