From transfinite.base_logic.lib Require Import na_invariants.
From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From iris.prelude Require Import options.
From melocoton Require Import named_props.
From melocoton.interop Require Import basics basics_resources.
From melocoton.interop Require Import lang weakestpre update_laws wp_utils prims_proto.
From melocoton.language Require Import weakestpre progenv.
From melocoton.c_interop Require Import rules notation.
From melocoton.ml_lang Require Import notation lang_instantiation.
From melocoton.c_lang Require Import mlang_instantiation lang_instantiation.
From melocoton.ml_lang Require primitive_laws proofmode.
From melocoton.ml_lang.logrel Require Import persistent_pred.
From melocoton.ml_lang.logrel Require typing logrel fundamental.
From melocoton.c_lang Require Import notation proofmode derived_laws.

Definition is_eq_code (x_arg y_arg : expr) : C_lang.expr :=
  let: "bx" := call: &"isblock" with (x_arg) in
  let: "res" := (
    (* Both values must agree whether they are a block since they have the same type. *)
    if: ! "bx" then
      (call: &"val2int" with (x_arg)) = (call: &"val2int" with (y_arg))
    else
      if: (call: &"read_tag" with (x_arg)) ≠ (call: &"read_tag" with (y_arg)) then #false else
      let: "lengthx" := (call: &"length" with (x_arg)) in
      let: "lengthy" := (call: &"length" with (y_arg)) in
      if: "lengthx" ≠ "lengthy" then #false else
      let: "i" := malloc ( #1 ) in "i" <- #0;;
      let: "r" := malloc ( #1 ) in "r" <- #true;;
      (while: * "i" < "lengthx" do
         let: "res" := call: &"is_eq" with (Field(x_arg, *"i"), Field(y_arg, *"i")) in
         if: !(call: &"val2int" with ("res")) then
           "r" <- #false;;
           "i" <- "lengthx"
         else
           "i" <- *"i" + #1);;
        let: "res" := *"r" in
        free ("i", #1);; free ("r", #1);;
        "res"
   ) in
   call: &"int2val" with ("res").

Lemma is_eq_code_subst (wx wy : val) :
  C_lang.subst_all (<["x_arg":=wx]> (<["y_arg":=wy]> ∅)) (is_eq_code "x_arg" "y_arg")
  = (is_eq_code wx wy).
Proof. done. Qed.

Definition is_eq_prog : lang_prog C_lang :=
  {[ "is_eq" := Fun [BNamed "x_arg"; BNamed "y_arg"] (is_eq_code "x_arg" "y_arg") ]}.

Section C_specs.
  Context `{SI:indexT}.
  Context `{!heapG_C Σ, !heapG_ML Σ, !invG Σ, !primitive_laws.heapG_ML Σ, !wrapperG Σ}.
  Context `{!logrel.logrelG Σ}.

  Import melocoton.ml_lang.logrel.typing.
  Fixpoint valid_is_eq_type (τ : type) : Prop :=
    match τ with
    | TUnit | TNat | TBool => True
    | TProd τ1 τ2 | TSum τ1 τ2 => valid_is_eq_type τ1 ∧ valid_is_eq_type τ2
    | TBoxedNat
    | TArray _ | TArrow _ _ | TRec _ | TVar _ | TForall _ | TExist _ => False
    end.


  Notation "⟦ τ ⟧  x" := (logrel.interp x τ) (at level 10).
  Notation na_tok := (na_own logrel.logrel_nais ⊤).

  Definition is_eq_spec_ML : protocol ML_lang.val Σ :=
    !! x y τ Δ p
    {{
       "%Hτ" ∷ ⌜valid_is_eq_type τ⌝ ∗
       "Hτx" ∷ ⟦ τ ⟧ p Δ x ∗
       "Hτy" ∷ ⟦ τ ⟧ p Δ y ∗
       "Htok" ∷ na_tok
    }}
      "is_eq" with [x; y]
    {{ RETV (#ML (bool_decide (x = y))); na_tok }}.

  Lemma is_eq_correct Ψ :
    prims_proto Ψ ||- is_eq_prog :: wrap_proto is_eq_spec_ML.
  Proof.
    iIntros (s ws Φ) "H". iNamed "H". iNamedProto "Hproto".
    iSplit; first done. iIntros (Φ'') "HΦ".
    unfold progwp.
    destruct lvs as [|lvx [|lvy [|??]]]; try done.
    all: cbn; iDestruct "Hsim" as "(Hx&Hsim)"; try done.
    all: cbn; iDestruct "Hsim" as "(Hy&?)"; try done.
    destruct ws as [|wx [|wy [|??]]]; decompose_Forall.
    iDestruct "Hx" as "-#Hx". iDestruct "Hy" as "-#Hy".
    iAssert (▷ ∀ wret, GC θ -∗ current_fc fc -∗ na_tok -∗
       ⌜repr_lval θ (Lint (bool_to_Z (bool_decide (x = y)))) wret⌝ -∗
       Φ'' (OVal wret))%I with "[Return Cont HΦ]" as "Return". {
      iIntros "!>" (?) "???". iIntros (?).
      iApply "HΦ". iApply ("Return" with "[$] [$] [-] [] [//]").
      { by iApply "Cont". } done.
    }
    iLöb as "IH" forall (τ x lvx wx y lvy wy Φ'' Hτ H1 H2).
    wp_call_direct.
    destruct τ => //=; iEval (unfold is_eq_code).
    - (* TUnit *)
      iDestruct "Hτx" as %->.
      iDestruct "Hτy" as %->.
      iDestruct "Hx" as %->.
      iDestruct "Hy" as %->.
      wp_apply (wp_isblock with "HGC"); [done..|].
      iIntros "HGC". wp_pures.
      wp_apply (wp_val2int with "HGC"); [done..|].
      iIntros "HGC".
      cbn; wp_apply (wp_val2int with "HGC"); [done..|].
      iIntros "HGC". wp_pures => /=.
      wp_apply (wp_int2val with "HGC"); [done..|].
      iIntros (w) "[HGC %]".
      by iApply ("Return" with "HGC Hfc Htok").
    - (* TNat *)
      iDestruct "Hτx" as %[? ->].
      iDestruct "Hτy" as %[? ->].
      iDestruct "Hx" as %->.
      iDestruct "Hy" as %->.
      wp_apply (wp_isblock with "HGC"); [done..|].
      iIntros "HGC". wp_pures.
      wp_apply (wp_val2int with "HGC"); [done..|].
      iIntros "HGC".
      cbn; wp_apply (wp_val2int with "HGC"); [done..|].
      iIntros "HGC". wp_pures => /=.
      wp_apply (wp_int2val with "HGC"); [done..|].
      iIntros (w) "[HGC %]". iApply ("Return" with "HGC Hfc Htok").
      iPureIntro. repeat case_bool_decide; naive_solver.
    - (* TBool *)
      iDestruct "Hτx" as %[? ->].
      iDestruct "Hτy" as %[? ->].
      iDestruct "Hx" as %->.
      iDestruct "Hy" as %->.
      wp_apply (wp_isblock with "HGC"); [done..|].
      iIntros "HGC". wp_pures.
      wp_apply (wp_val2int with "HGC"); [done..|].
      iIntros "HGC".
      cbn; wp_apply (wp_val2int with "HGC"); [done..|].
      iIntros "HGC". wp_pures => /=.
      wp_apply (wp_int2val with "HGC"); [done..|].
      iIntros (w) "[HGC %]". iApply ("Return" with "HGC Hfc Htok").
      iPureIntro. repeat case_match; naive_solver.
    - (* TProd *)
      destruct Hτ as [??].
      iDestruct "Hτx" as (?? ->) "[Hτx1 Hτx2]".
      iDestruct "Hτy" as (?? ->) "[Hτy1 Hτy2]". simpl.
      iDestruct "Hx" as (γx ?? ?) "[#Hγx [#? #?]]".
      iDestruct "Hy" as (γy ?? ?) "[#Hγy [#? #?]]". simplify_eq.
      wp_apply (wp_isblock with "HGC"); [done..|].
      iIntros "HGC". wp_pures.
      wp_bind (if: _ then _ else _)%CE.
      wp_apply (wp_read_tag with "[$HGC ]"); [done..| |].
      { by iDestruct "Hγx" as "[??]". }
      iIntros "[HGC _]". wp_pures.
      wp_apply (wp_read_tag with "[$HGC ]"); [done..| |].
      { by iDestruct "Hγy" as "[??]". }
      iIntros "[HGC _]". wp_pures.
      wp_apply (wp_length with "[$HGC ]"); [done..|].
      iIntros "[HGC _]". wp_pures.
      wp_apply (wp_length with "[$HGC ]"); [done..|].
      iIntros "[HGC _]". wp_pures.
      wp_apply (wp_Malloc); [done..|].
      change (Z.to_nat 1) with 1; cbn.
      iIntros (ℓi) "(Hℓi&_)". rewrite !loc_add_0. wp_pure _.
      wp_apply (wp_store with "Hℓi").
      iIntros "Hℓi". wp_pure _.
      wp_apply (wp_Malloc); [done..|].
      change (Z.to_nat 1) with 1; cbn.
      iIntros (ℓr) "(Hℓr&_)". rewrite !loc_add_0. wp_pure _.
      wp_apply (wp_store with "Hℓr").

      iIntros "Hℓr". wp_pures.
      wp_apply (wp_load with "Hℓi").
      iIntros "Hℓi". wp_pures.
      wp_apply (wp_load with "Hℓi").
      iIntros "Hℓi". wp_pures.
      wp_apply (wp_readfield with "[$HGC ]"); [try done..|] => //=.
      iIntros (??) "(HGC&_&%&%)". simplify_eq.
      wp_apply (wp_load with "Hℓi").
      iIntros "Hℓi". wp_pures.
      wp_apply (wp_readfield with "[$HGC ]"); [try done..|] => //=.
      iIntros (??) "(HGC&_&%&%)". simplify_eq.
      wp_bind (FunCall _ _).
      iApply ("IH" with "[] [] [] HGC Hfc Hτx1 Hτy1 Htok"); [done..|].
      iIntros "!>" (?) "HGC Hfc Htok". iIntros (?). wp_pures.
      wp_apply (wp_val2int with "HGC"); [done..|].
      iIntros "HGC". case_bool_decide. 2: {
        wp_pures.
        wp_apply (wp_store with "Hℓr").
        iIntros "Hℓr". wp_pures.
        wp_apply (wp_store with "Hℓi").
        iIntros "Hℓi". wp_pures.
        wp_apply (wp_load with "Hℓi").
        iIntros "Hℓi". wp_pures.
        wp_apply (wp_load with "Hℓr").
        iIntros "Hℓr". wp_pures.
        wp_apply (wp_free with "Hℓi"). iIntros "_". wp_pures.
        wp_apply (wp_free with "Hℓr"). iIntros "_". wp_pures.
        wp_apply (wp_int2val with "HGC"); [done..|].
        iIntros (w) "[HGC %]". iApply ("Return" with "HGC Hfc Htok").
        iPureIntro. repeat case_bool_decide; naive_solver.
      }
      wp_pures.
      wp_apply (wp_load with "Hℓi").
      iIntros "Hℓi". wp_pures.
      wp_apply (wp_store with "Hℓi").
      iIntros "Hℓi". wp_pures.

      wp_apply (wp_load with "Hℓi").
      iIntros "Hℓi". wp_pures.
      wp_apply (wp_load with "Hℓi").
      iIntros "Hℓi". wp_pures.
      wp_apply (wp_readfield with "[$HGC ]"); [try done..|] => //=.
      iIntros (??) "(HGC&_&%&%)". simplify_eq.
      wp_apply (wp_load with "Hℓi").
      iIntros "Hℓi". wp_pures.
      wp_apply (wp_readfield with "[$HGC ]"); [try done..|] => //=.
      iIntros (??) "(HGC&_&%&%)". simplify_eq.
      wp_bind (FunCall _ _).
      iApply ("IH" with "[] [] [] HGC Hfc Hτx2 Hτy2 Htok"); [done..|].
      iIntros "!>" (?) "HGC Hfc Htok". iIntros (?). wp_pures.
      wp_apply (wp_val2int with "HGC"); [done..|].
      iIntros "HGC". case_bool_decide. 2: {
        wp_pures.
        wp_apply (wp_store with "Hℓr").
        iIntros "Hℓr". wp_pures.
        wp_apply (wp_store with "Hℓi").
        iIntros "Hℓi". wp_pures.
        wp_apply (wp_load with "Hℓi").
        iIntros "Hℓi". wp_pures.
        wp_apply (wp_load with "Hℓr").
        iIntros "Hℓr". wp_pures.
        wp_apply (wp_free with "Hℓi"). iIntros "_". wp_pures.
        wp_apply (wp_free with "Hℓr"). iIntros "_". wp_pures.
        wp_apply (wp_int2val with "HGC"); [done..|].
        iIntros (w) "[HGC %]". iApply ("Return" with "HGC Hfc Htok").
        iPureIntro. repeat case_bool_decide; naive_solver.
      }
      wp_pures.
      wp_apply (wp_load with "Hℓi").
      iIntros "Hℓi". wp_pures.
      wp_apply (wp_store with "Hℓi").
      iIntros "Hℓi". wp_pures.

      wp_apply (wp_load with "Hℓi").
      iIntros "Hℓi". wp_pures.
      wp_apply (wp_load with "Hℓr").
      iIntros "Hℓr". wp_pures.
      wp_apply (wp_free with "Hℓi"). iIntros "_". wp_pures.
      wp_apply (wp_free with "Hℓr"). iIntros "_". wp_pures.
      wp_apply (wp_int2val with "HGC"); [done..|].
      iIntros (w) "[HGC %]". iApply ("Return" with "HGC Hfc Htok").
      iPureIntro. repeat case_bool_decide; naive_solver.
    - (* TSum *)
      destruct Hτ as [??].
      iAssert (∃ wx γx lvx' tg, ⌜lvx = Lloc γx⌝ ∗ ⌜if tg is TagDefault then x = InjLV wx else x = InjRV wx⌝ ∗ γx ↦imm (tg, [lvx']) ∗ lvx' ~~ wx)%I as (wx' γx lvx' tgx) "[% [% [#Hγx #?]]]". {
        iDestruct "Hτx" as "[[%w [% ?]]|[%w [% ?]]]"; simplify_eq/=.
        all: iDestruct "Hx" as (???) "[Hγ ?]"; simplify_eq.
        all: iExists _, _, _, _; iSplit; [done|]; iFrame "Hγ"; by iFrame.
      }
      iClear "Hx". simplify_eq.
      iAssert (∃ w γ lv' tg, ⌜lvy = Lloc γ⌝ ∗ ⌜if tg is TagDefault then y = InjLV w else y = InjRV w⌝ ∗ γ ↦imm (tg, [lv']) ∗ lv' ~~ w)%I as (wy' γy lvy' tgy) "[% [% [#Hγy #?]]]". {
        iDestruct "Hτy" as "[[%w [% ?]]|[%w [% ?]]]"; simplify_eq/=.
        all: iDestruct "Hy" as (???) "[Hγ ?]"; simplify_eq.
        all: iExists _, _, _, _; iSplit; [done|]; iFrame "Hγ"; by iFrame.
      }
      iClear "Hy". simplify_eq.
      wp_apply (wp_isblock with "HGC"); [done..|].
      iIntros "HGC". wp_pures.
      wp_bind (if: _ then _ else _)%CE.
      wp_apply (wp_read_tag with "[$HGC ]"); [done..| |].
      { by iDestruct "Hγx" as "[??]". }
      iIntros "[HGC _]". wp_pures.
      wp_apply (wp_read_tag with "[$HGC ]"); [done..| |].
      { by iDestruct "Hγy" as "[??]". }
      iIntros "[HGC _]". wp_pures.
      destruct_decide (bool_decide_reflect (vblock_tag_as_int tgx = vblock_tag_as_int tgy)). 2: {
        wp_pures.
        wp_apply (wp_int2val with "HGC"); [done..|].
        iIntros (w) "[HGC %]". iApply ("Return" with "HGC Hfc Htok").
        iPureIntro. repeat case_match; case_bool_decide; naive_solver.
      }
      wp_pures.
      iAssert (∃ τ, ⌜valid_is_eq_type τ⌝ ∗ (⟦ τ ⟧ p) Δ wx' ∗ (⟦ τ ⟧ p) Δ wy')%I
        as (??) "[#Hτx' #Hτy']". {
        repeat case_match => //; simplify_eq.
        - iDestruct "Hτx" as "[[%w [% ?]]|[%w [% ?]]]"; simplify_eq/=.
          iDestruct "Hτy" as "[[% [% ?]]|[% [% ?]]]"; simplify_eq/=.
          iExists _. by iFrame.
        - iDestruct "Hτx" as "[[%w [% ?]]|[%w [% ?]]]"; simplify_eq/=.
          iDestruct "Hτy" as "[[% [% ?]]|[% [% ?]]]"; simplify_eq/=.
          iExists _. by iFrame.
      }
      wp_apply (wp_length with "[$HGC ]"); [done..|].
      iIntros "[HGC _]". wp_pures.
      wp_apply (wp_length with "[$HGC ]"); [done..|].
      iIntros "[HGC _]". wp_pures.
      wp_apply (wp_Malloc); [done..|].
      change (Z.to_nat 1) with 1; cbn.
      iIntros (ℓi) "(Hℓi&_)". rewrite !loc_add_0. wp_pure _.
      wp_apply (wp_store with "Hℓi").
      iIntros "Hℓi". wp_pure _.
      wp_apply (wp_Malloc); [done..|].
      change (Z.to_nat 1) with 1; cbn.
      iIntros (ℓr) "(Hℓr&_)". rewrite !loc_add_0. wp_pure _.
      wp_apply (wp_store with "Hℓr").
      iIntros "Hℓr". wp_pures.
      wp_apply (wp_load with "Hℓi").
      iIntros "Hℓi". wp_pures.
      wp_apply (wp_load with "Hℓi").
      iIntros "Hℓi". wp_pures.
      wp_apply (wp_readfield with "[$HGC ]"); [try done..|] => //=.
      iIntros (??) "(HGC&_&%&%)". simplify_eq.
      wp_apply (wp_load with "Hℓi").
      iIntros "Hℓi". wp_pures.
      wp_apply (wp_readfield with "[$HGC ]"); [try done..|] => //=.
      iIntros (??) "(HGC&_&%&%)". simplify_eq.
      wp_bind (FunCall _ _).
      iApply ("IH" with "[] [] [] HGC Hfc Hτx' Hτy' Htok"); [try done..|].
      iIntros "!>" (?) "HGC Hfc Htok". iIntros (?). wp_pures.
      wp_apply (wp_val2int with "HGC"); [done..|].
      iIntros "HGC". case_bool_decide.
      + wp_pures.
        wp_apply (wp_load with "Hℓi").
        iIntros "Hℓi". wp_pures.
        wp_apply (wp_store with "Hℓi").
        iIntros "Hℓi". wp_pures.
        wp_apply (wp_load with "Hℓi").
        iIntros "Hℓi". wp_pures.
        wp_apply (wp_load with "Hℓr").
        iIntros "Hℓr". wp_pures.
        wp_apply (wp_free with "Hℓi"). iIntros "_". wp_pures.
        wp_apply (wp_free with "Hℓr"). iIntros "_". wp_pures.
        wp_apply (wp_int2val with "HGC"); [done..|].
        iIntros (w) "[HGC %]". iApply ("Return" with "HGC Hfc Htok").
        iPureIntro. repeat case_match; case_bool_decide; naive_solver.
      + wp_pures.
        wp_apply (wp_store with "Hℓr").
        iIntros "Hℓr". wp_pures.
        wp_apply (wp_store with "Hℓi").
        iIntros "Hℓi". wp_pures.
        wp_apply (wp_load with "Hℓi").
        iIntros "Hℓi". wp_pures.
        wp_apply (wp_load with "Hℓr").
        iIntros "Hℓr". wp_pures.
        wp_apply (wp_free with "Hℓi"). iIntros "_". wp_pures.
        wp_apply (wp_free with "Hℓr"). iIntros "_". wp_pures.
        wp_apply (wp_int2val with "HGC"); [done..|].
        iIntros (w) "[HGC %]". iApply ("Return" with "HGC Hfc Htok").
        iPureIntro. repeat case_match; case_bool_decide; naive_solver.
  Qed.

End C_specs.
