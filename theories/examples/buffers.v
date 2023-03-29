From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From iris.prelude Require Import options.
From melocoton Require Import named_props.
From melocoton.interop Require Import basics basics_resources.
From melocoton.lang_to_mlang Require Import lang weakestpre.
From melocoton.interop Require Import lang weakestpre update_laws wp_utils wp_ext_call_laws wp_simulation.
From melocoton.c_interop Require Import rules.
From melocoton.ml_lang Require Import notation lang_instantiation.
From melocoton.c_lang Require Import mlang_instantiation lang_instantiation.
From melocoton.ml_lang Require proofmode.
From melocoton.c_lang Require notation proofmode.
From melocoton.mlanguage Require Import progenv.
From melocoton.mlanguage Require weakestpre.
From melocoton.linking Require Import lang weakestpre.


Section C_prog.
Import melocoton.c_lang.notation melocoton.c_lang.proofmode.

Context `{SI:indexT}.
Context `{!heapG_C Σ, !heapG_ML Σ, !invG Σ, !primitive_laws.heapG_ML Σ, !wrapperG Σ}.

Definition CAMLlocal (n:string) (e : expr) : expr :=
  (let: n := malloc (#1) in
    (Var n <- (call: &"int2val" with (Val (#0))));;
    (call: &"registerroot" with (Var n));; e).

Notation "'CAMLlocal:' x 'in' e2" := (CAMLlocal x%string e2%CE)
  (at level 200, x at level 1, e2 at level 200,
   format "'[' 'CAMLlocal:'  x   'in'  '/' e2 ']'") : c_expr_scope.

Definition buf_alloc_code (cap : expr) : expr :=
  CAMLlocal: "bk" in
  "bk" <- call: &"allocforeign" with ( ) ;;
  call: &"writeforeign" with ( *"bk", malloc (call: &"val2int" with (cap))) ;;
  CAMLlocal: "bf" in
  "bf" <- call: &"alloc" with (Val #2, Val #0) ;;
  CAMLlocal: "bf2" in
  "bf2" <- call: &"alloc" with (Val #2, Val #0) ;;
  CAMLlocal: "bfref" in
  "bfref" <- call: &"alloc" with (Val #1, Val #0) ;;
  call: &"modify" with ( *"bf", Val #0, *"bfref") ;;
  call: &"modify" with ( *"bf", Val #1, *"bf2") ;;
  call: &"modify" with ( *"bf2", Val #0, cap ) ;;
  call: &"modify" with ( *"bf2", Val #1, *"bk") ;;
  call: &"modify" with ( *"bfref", Val #0, call: &"int2val" with (Val #0) ) ;;
  call: &"unregisterroot" with ( *"bk" ) ;;
  call: &"unregisterroot" with ( *"bf" ) ;;
  call: &"unregisterroot" with ( *"bf2" ) ;;
  call: &"unregisterroot" with ( *"bfref" ) ;;
  let: "retval" := *"bf" in
  free ("bk", #1) ;; free ("bf", #1) ;; free ("bf2", #1) ;; free ("bfref", #1) ;;
  "retval".

Definition buf_upd_code (iv jv f_arg bf_arg : expr) : expr :=
  CAMLlocal: "f" in
  "f" <- f_arg ;;
  CAMLlocal: "bf" in
  "bf" <- bf_arg ;;
  let: "bts" := call: &"readforeign" with (
      call: &"readfield" with ( call: &"readfield" with ( *"bf", Val #1), Val #1)) in
  let: "j" := call: &"val2int" with ( jv ) in
  let: "i" := malloc ( #1 ) in
  "i" <- call: &"val2int" with ( iv ) ;;
  while: * "i" ≤ "j" do
    ( "bts" +ₗ ( *"i") <- call: &"val2int" with (call: &"callback" with ( *"f", call: &"int2val" with ( *"i"))) ;;
      if: (call: &"val2int" with (call: &"readfield" with (call: &"readfield" with ( *"bf", Val #0), Val #0)) < *"i" + #1)
      then (call: &"modify" with (call: &"readfield" with ( *"bf", Val #0), Val #0, call: &"int2val" with ( *"i" + #1)))
      else Skip ;;
      "i" <- *"i" + #1 ) ;;
  call: &"unregisterroot" with ( *"f" ) ;;
  call: &"unregisterroot" with ( *"bf" ) ;;
  free ("f", #1);; free ("bf", #1);; free ("i", #1) ;;
  call: &"int2val" with (Val #0).
  

Definition swap_pair_code (x : expr) : expr :=
  let: "lv" := malloc (#2) in
  ("lv" +ₗ #0 <- (call: &"readfield" with (x, Val #0))) ;;
  ("lv" +ₗ #1 <- (call: &"readfield" with (x, Val #1))) ;;
  (call: &"registerroot" with ( Var "lv" +ₗ #0 )) ;;
  (call: &"registerroot" with ( Var "lv" +ₗ #1 )) ;;
  let: "np" := (call: &"alloc" with (Val #0, Val #2)) in
  (call: &"modify" with (Var "np", Val #1, * ("lv" +ₗ #0))) ;;
  (call: &"modify" with (Var "np", Val #0, * ("lv" +ₗ #1))) ;;
  (call: &"unregisterroot" with ( Var "lv" +ₗ #0 )) ;;
  (call: &"unregisterroot" with ( Var "lv" +ₗ #1 )) ;;
  (free ("lv", #2)) ;;
  "np".

Definition swap_pair_func : function := Fun [BNamed "x"] (swap_pair_code "x").
Definition swap_pair_prog : lang_prog C_lang := {[ "swap_pair" := swap_pair_func ]}.

Definition swap_pair_ml_spec : protocol ML_lang.val Σ := (
  λ s l wp, ∃ v1 v2, ⌜s = "swap_pair"⌝ ∗ ⌜l = [ (v1,v2)%MLV ]⌝ ∗ wp ((v2,v1)%MLV)
)%I.

Lemma swap_pair_correct E e :
  wrap_proto swap_pair_ml_spec ⊑
  prog_proto E swap_pair_prog (prims_proto ∅ e swap_pair_ml_spec).
Proof.
  iIntros (fn ws Φ) "H". iNamed "H".
  iDestruct "Hproto" as (v1 v2) "(->&->&Hψ)".
  rewrite /prog_proto lookup_insert.
  iAssert (⌜length lvs = 1⌝)%I with "[Hsim]" as %Hlen.
  { by iDestruct (big_sepL2_length with "Hsim") as %?. }
  destruct lvs as [|lv []]; try by (exfalso; eauto with lia); []. clear Hlen.
  destruct ws as [|w []]; try by (exfalso; apply Forall2_length in Hrepr; eauto with lia); [].
  apply Forall2_cons_1 in Hrepr as [Hrepr _].
  iExists _. iSplit; first done. iNext.
  iPoseProof (big_sepL2_cons_inv_l with "Hsim") as (l lr ?) "[Hsim _]".
  simplify_eq.

  wp_pures.
  wp_alloc rr as "H"; first done.
  change (Z.to_nat 2) with 2. cbn. iDestruct "H" as "(H1&H2&_)". destruct rr as [rr].
  wp_pures.

  (* readfield 1 *)
  iDestruct "Hsim" as (γ lv1 lv2 ->) "(#Hptpair & #Hlv1 & #Hlv2)".
  wp_apply (wp_readfield with "[$HGC $Hptpair]"); [done..|].
  iIntros (v wlv1) "(HGC & _ & %Heq & %Hrepr1)".
  change (Z.to_nat 0) with 0 in Heq. cbn in *. symmetry in Heq. simplify_eq.
  wp_apply (wp_store with "H1"). iIntros "H1". wp_pures.

  (* readfield 2 *)
  wp_apply (wp_readfield with "[$HGC $Hptpair]"); [done..|].
  iIntros (v wlv2) "(HGC & _ & %Heq & %Hrepr2)".
  change (Z.to_nat 1) with 1 in Heq. cbn in *. symmetry in Heq. simplify_eq.
  wp_apply (wp_store with "H2"). iIntros "H2". wp_pures.

  (* registerroot 1 *)
  wp_apply (wp_registerroot with "[$HGC $H1]"); [done..|].
  iIntros "(HGC & H1r)". wp_pures.

  (* registerroot 2 *)
  wp_apply (wp_registerroot with "[$HGC $H2]"); [done..|].
  iIntros "(HGC & H2r)". wp_pures.

  (* alloc *)
  wp_apply (wp_alloc _ _ _ _ TagDefault with "HGC"); [done..|].
  iIntros (θ' γnew wnew) "(HGC & Hnew & %Hreprnew)".
  wp_pures. change (Z.to_nat 2) with 2. cbn [repeat].

  (* load from root *)
  wp_apply (load_from_root with "[HGC H1r]"); first iFrame.
  iIntros (wlv1') "(Hr1&HGC&%Hrepr1')".

  (* modify 1 *)
  wp_apply (wp_modify with "[$HGC $Hnew]"); [done..|].
  iIntros "(HGC & Hnew)". change (Z.to_nat 1) with 1. cbn.
  wp_pures.

  (* load from root *)
  wp_bind (Load _).
  wp_apply (load_from_root with "[HGC H2r]"); first iFrame.
  iIntros (wlv2') "(Hr2&HGC&%Hrepr2')".

  (* modify 2 *)
  wp_apply (wp_modify with "[$HGC $Hnew]"); [done..|].
  iIntros "(HGC & Hnew)". change (Z.to_nat 0) with 0. cbn.
  wp_pures.

  (* unregisterroot 1 *)
  wp_apply (wp_unregisterroot with "[$HGC $Hr1]"); [done..|].
  iIntros (wlv1'') "(HGC & H1 & %Hrepr1'1)".
  repr_lval_inj. wp_pures.

  (* unregisterroot 2 *)
  wp_apply (wp_unregisterroot with "[$HGC $Hr2]"); [done..|].
  iIntros (wlv2'') "(HGC & H2 & %Hrepr2'1)".
  repr_lval_inj. wp_pures.

  (* free *)
  iAssert ((Loc rr) ↦C∗ [Some wlv1'; Some wlv2'])%I with "[H1 H2]" as "Hrr".
  1: cbn; iFrame.
  wp_apply (wp_free_array' with "Hrr"); first done. iIntros "_".
  wp_pures.

  (* Finish, convert the new points-to to an immutable pointsto *)
  iMod (freeze_to_immut γnew _ θ' with "[$]") as "(HGC&#Hnew)".

  iModIntro. iApply ("Cont" with "HGC Hψ [] []").
  - cbn. do 3 iExists _. iFrame "Hnew Hlv1 Hlv2". done.
  - done.
Qed.


Definition main_C_program := (call: &"main" with ( ) )%CE.

End C_prog.

Section ML_prog.

Import melocoton.c_lang.primitive_laws.
Import melocoton.ml_lang.proofmode.

Context `{SI:indexT}.
Context `{!heapG_C Σ, !invG Σ, !heapG_ML Σ, !wrapperG Σ, !linkG Σ}.

Definition swap_pair_client : mlanguage.expr (lang_to_mlang ML_lang) :=
  (Fst (Extern "swap_pair" [ ((#3, (#1, #2)))%MLE ])).

Lemma ML_prog_correct_axiomatic E :
  ⊢ WP swap_pair_client @ ⟨∅, swap_pair_ml_spec⟩ ; E {{v, ⌜v = (#1, #2)⌝%MLV}}.
Proof.
  iStartProof. unfold swap_pair_client. wp_pures.
  wp_extern.
  iModIntro. cbn. do 2 iExists _.
  do 2 (iSplitR; first done).
  wp_pures. done.
Qed.

Import melocoton.mlanguage.weakestpre.

Lemma is_linkable_swap_pair e :
  can_link wrap_lang C_mlang
    (wrap_prog e)  (wrap_proto swap_pair_ml_spec)
    swap_pair_prog (prims_proto ∅ e swap_pair_ml_spec)
    ⊥.
Proof.
  constructor; intros.
  - rewrite !dom_insert_L !dom_empty_L. set_solver.
  - rewrite proto_on_refines swap_pair_correct lang_to_mlang_refines //.
  - rewrite proto_on_refines wrap_refines.
    2: { iIntros (? ? ?). rewrite /proto_on.
         iIntros "(% & H)". iDestruct "H" as (? ? ->) "_". exfalso.
         by vm_compute in H. }
    eapply mprog_proto_mono; first set_solver. done.
  - iIntros (? ? ?) "H". rewrite /proto_except.
    iDestruct "H" as (?) "H". iNamed "H".
    iDestruct "Hproto" as (? ? ->) "H". set_solver.
  - apply prims_proto_except_dom.
Qed.

Notation link_in_state := (link_in_state wrap_lang C_mlang).

Definition linked_lang : mlanguage Cval := link_lang wrap_lang C_mlang.
Definition linked_prog_env : prog_environ linked_lang Σ := 
    ⟪ link_prog wrap_lang C_mlang (wrap_prog swap_pair_client) swap_pair_prog, ⊥ ⟫.
Definition linked_start : expr linked_lang := LkSE (Link.Expr2 (main_C_program : expr C_mlang)).

(* Unsure why this is necessary -- typeclass inference fails without this *)
Global Instance foo : (linkableG C_mlang public_state_interp).
Proof. apply (@lang_to_mlang_linkableG SI Σ Cval C_lang (@heapG_langG_C SI SI Σ heapG_C0)). Qed.
Import melocoton.c_lang.notation melocoton.c_lang.proofmode.


Lemma global_c_prog_correct E : 
(⊢ link_in_state In2
-∗ at_init
-∗ WP linked_start @ linked_prog_env; E {{ v, ∃ θ γ, GC θ ∗ ⌜repr_lval θ (Lloc γ) v⌝ ∗ γ ↦imm (TagDefault, [Lint 1; Lint 2]) }})%I.
Proof.
  iIntros "H1 Hinit". unfold linked_prog_env.
  iApply (wp_link_run2' with "H1 [Hinit]").
  1: apply is_linkable_swap_pair.
  2: iIntros (v) "(H&_)"; iApply "H". cbn.
  iApply wp_lang_to_mlang.
  wp_apply (wp_main with "[Hinit]").
  - done.
  - rewrite main_refines_prims_proto //.
  - iFrame. iNext. iApply ML_prog_correct_axiomatic.
  - iIntros (θ' vret lvret wret) "(HGC&->&(%γ&%&%&->&Himm&->&->)&%HH)".
    cbn. iSplitL; last done.
    iExists _, _. iFrame. done.
Qed.

End ML_prog.

Check @global_c_prog_correct.
Print Assumptions global_c_prog_correct.

