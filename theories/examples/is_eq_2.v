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
  Fixpoint is_valid_type (τ : type) : Prop :=
    match τ with
    | TUnit | TNat | TBool => True
    | TProd τ1 τ2 | TSum τ1 τ2 => is_valid_type τ1 ∧ is_valid_type τ2
    | TArray τ1 => is_valid_type τ1
    | TArrow _ _ | TRec _ | TVar _ | TForall _ | TExist _ => False
    end.


  Notation "⟦ τ ⟧  x" := (logrel.interp x τ) (at level 10).
  Notation na_tok := (na_own logrel.logrel_nais ⊤).

  Definition is_eq_spec_ML : protocol ML_lang.val Σ :=
    λ s vv Φ,
    (∃ x y τ Δ p,
      "->" ∷ ⌜s = "is_eq"⌝
    ∗ "->" ∷ ⌜vv = [ x; y ]⌝
    ∗ "%Hτ" ∷ ⌜is_valid_type τ⌝
    ∗ "Hτx" ∷ ⟦ τ ⟧ p Δ x
    ∗ "Hτy" ∷ ⟦ τ ⟧ p Δ y
    ∗ "Htok" ∷ na_tok
    ∗ "Hcont" ∷ (∀ (b:bool), na_tok -∗ Φ (ML_lang.LitV b)))%I.

  Lemma is_eq_correct Ψ :
    prims_proto Ψ ||- is_eq_prog :: wrap_proto is_eq_spec_ML.
  Proof.
    iIntros (s ws Φ) "H". iNamed "H". iNamed "Hproto".
    iSplit; first done. iIntros (Φ'') "HΦ".
    unfold progwp.
    destruct lvs as [|lvx [|lvy [|??]]]; try done.
    all: cbn; iDestruct "Hsim" as "(Hx&Hsim)"; try done.
    all: cbn; iDestruct "Hsim" as "(Hy&?)"; try done.
    destruct ws as [|wx [|wy [|??]]]; decompose_Forall.
    iDestruct "Hx" as "-#Hx". iDestruct "Hy" as "-#Hy".
    iAssert (▷ ∀ b wret, GC θ ∅ -∗ na_tok -∗
       ⌜repr_lval θ (Lint (bool_to_Z b)) wret⌝ -∗
       Φ'' wret)%I with "[Cont Hcont HΦ]" as "Cont". {
      iIntros "!>" (??) "??". iIntros (?).
      iApply "HΦ". iApply ("Cont" with "[$] [-] [] [//]").
      { by iApply "Hcont". } done.
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
      wp_apply (wp_val2int with "HGC"); [done..|].
      iIntros "HGC". wp_pures => /=.
      wp_apply (wp_int2val with "HGC"); [done..|].
      iIntros (w) "[HGC %]".
      by iApply ("Cont" $! true with "HGC Htok").
    - (* TNat *)
      iDestruct "Hτx" as %[? ->].
      iDestruct "Hτy" as %[? ->].
      iDestruct "Hx" as %->.
      iDestruct "Hy" as %->.
      wp_apply (wp_isblock with "HGC"); [done..|].
      iIntros "HGC". wp_pures.
      wp_apply (wp_val2int with "HGC"); [done..|].
      iIntros "HGC".
      wp_apply (wp_val2int with "HGC"); [done..|].
      iIntros "HGC". wp_pures => /=.
      wp_apply (wp_int2val with "HGC"); [done..|].
      iIntros (w) "[HGC %]". iApply ("Cont" $! (bool_decide (x0 = x)) with "HGC Htok").
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
      wp_apply (wp_val2int with "HGC"); [done..|].
      iIntros "HGC". wp_pures => /=.
      wp_apply (wp_int2val with "HGC"); [done..|].
      iIntros (w) "[HGC %]". iApply ("Cont" $! (bool_decide (x0 = x)) with "HGC Htok").
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
      iApply ("IH" with "[] [] [] HGC Hτx1 Hτy1 Htok"); [done..|].
      iIntros "!>" (??) "HGC Htok". iIntros (?). wp_pures.
      wp_apply (wp_val2int with "HGC"); [done..|].
      iIntros "HGC". destruct b. 2: {
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
        iIntros (w) "[HGC %]". iApply ("Cont" $! false with "HGC Htok").
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
      iApply ("IH" with "[] [] [] HGC Hτx2 Hτy2 Htok"); [done..|].
      iIntros "!>" (b ?) "HGC Htok". iIntros (?). wp_pures.
      wp_apply (wp_val2int with "HGC"); [done..|].
      iIntros "HGC". destruct b. 2: {
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
        iIntros (w) "[HGC %]". iApply ("Cont" $! false with "HGC Htok").
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
      iIntros (w) "[HGC %]". iApply ("Cont" $! true with "HGC Htok").
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
        iIntros (w) "[HGC %]". iApply ("Cont" $! false with "HGC Htok").
        iPureIntro. repeat case_match; naive_solver.
      }
      wp_pures.
      iAssert (∃ τ, ⌜is_valid_type τ⌝ ∗ (⟦ τ ⟧ p) Δ wx' ∗ (⟦ τ ⟧ p) Δ wy')%I
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
      iApply ("IH" with "[] [] [] HGC Hτx' Hτy' Htok"); [try done..|].
      iIntros "!>" (b ?) "HGC Htok". iIntros (?). wp_pures.
      wp_apply (wp_val2int with "HGC"); [done..|].
      iIntros "HGC". destruct b.
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
        iIntros (w) "[HGC %]". iApply ("Cont" $! true with "HGC Htok").
        iPureIntro. repeat case_match; naive_solver.
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
        iIntros (w) "[HGC %]". iApply ("Cont" $! false with "HGC Htok").
        iPureIntro. repeat case_match; naive_solver.
    - cbn in Hτ. assert (∀ (γ : nat), ((∅ ∪ {[γ]}) ∖ {[γ]}) = (∅:gset nat)) as Hscrub by set_solver.
      iDestruct "Hτx" as "(%γINVx&%ℓx&->&#Hinvx1&#Hinvx2)".
      iDestruct "Hτy" as "(%γINVy&%ℓy&->&#Hinvy1&#Hinvy2)".
      iDestruct "Hx" as "(%γx&%fgnx&->&#Hfgnx)".
      iDestruct "Hy" as "(%γy&%fgny&->&#Hfgny)".
      wp_apply (wp_isblock with "HGC"); [done..|].
      iIntros "HGC". wp_pures.
      iMod (na_inv_acc_open_timeless with "Hinvx1 Htok") as "[(%vvx&Hvsx&HγLx) (Htok & Hclose1)]"; [done..|].
      iPoseProof (pgm_elem_to_pers with "Hvsx") as "#Hxlen".
      iMod (ml_to_mut with "[$HGC $Hvsx]") as "(%lvvx&%γx2&%fgnx2&HGC&Hgamx&#Hsimx&#Hvalsx)".
      iAssert (γx ↦head Hvblock TagDefault (length vvx))%I as "#Hxhead".
      { iPoseProof (lloc_own_pub_inj_2 with "Hfgnx Hsimx") as "%Heq".
        specialize (Heq (ltac:(eauto))). subst γx2.
        iPoseProof (lloc_own_pub_inj_1 with "Hfgnx Hsimx") as "%Heq".
        specialize (Heq (ltac:(eauto))) as [HL HR].
        iDestruct "Hgamx" as "(HH1&_)".
        iPoseProof (pgm_elem_to_pers with "HH1") as "HH2".
        iPoseProof (GC_confront_length_head with "HGC HH2 Hxlen Hsimx") as "%HHH".
        cbn in HHH. rewrite -HHH. iApply "HH2". }
      iMod (mut_to_ml_store with "[$HGC $Hgamx $Hvalsx]") as "(HGC&%fgnx3&%lx3&Hvsx&Hsimx2)".
      iAssert (⌜ℓx = lx3⌝)%I as "%Heq".
      { iPoseProof (lloc_own_pub_inj_2 with "Hfgnx Hsimx") as "%Heq".
        specialize (Heq (ltac:(eauto))). subst γx2.
        iPoseProof (lloc_own_pub_inj_1 with "Hfgnx Hsimx2") as "%Heq".
        specialize (Heq (ltac:(eauto))) as [HL HR]. subst. done. }
      subst lx3.
      iPoseProof (GC_confront_MLloc with "HGC Hvsx Hsimx") as "(HGC&Hvsx)". erewrite Hscrub.
      iClear "Hsimx Hsimx2 Hvalsx". clear fgnx2 fgnx3 γx2.
      iMod ("Hclose1" with "[$Htok HγLx Hvsx]") as "Htok".
      { iNext. iExists _. iFrame. }

      iMod (na_inv_acc_open_timeless with "Hinvy1 Htok") as "[(%vvy&Hvsy&HγLy) (Htok & Hclose2)]"; [done..|].
      iPoseProof (pgm_elem_to_pers with "Hvsy") as "#Hylen".
      iMod (ml_to_mut with "[$HGC $Hvsy]") as "(%lvvy&%γy2&%fgny2&HGC&Hgamy&#Hsimy&#Hvalsy)".
      iAssert (γy ↦head Hvblock TagDefault (length vvy))%I as "#Hyhead".
      { iPoseProof (lloc_own_pub_inj_2 with "Hfgny Hsimy") as "%Heq".
        specialize (Heq (ltac:(eauto))). subst γy2.
        iPoseProof (lloc_own_pub_inj_1 with "Hfgny Hsimy") as "%Heq".
        specialize (Heq (ltac:(eauto))) as [HL HR].
        iDestruct "Hgamy" as "(HH1&_)".
        iPoseProof (pgm_elem_to_pers with "HH1") as "HH2".
        iPoseProof (GC_confront_length_head with "HGC HH2 Hylen Hsimy") as "%HHH".
        cbn in HHH. rewrite -HHH. iApply "HH2". }
      iMod (mut_to_ml_store with "[$HGC $Hgamy $Hvalsy]") as "(HGC&%fgny3&%ly3&Hvsy&Hsimy2)".
      iAssert (⌜ℓy = ly3⌝)%I as "%Heq".
      { iPoseProof (lloc_own_pub_inj_2 with "Hfgny Hsimy") as "%Heq".
        specialize (Heq (ltac:(eauto))). subst γy2.
        iPoseProof (lloc_own_pub_inj_1 with "Hfgny Hsimy2") as "%Heq".
        specialize (Heq (ltac:(eauto))) as [HL HR]. subst. done. }
      subst ly3.
      iPoseProof (GC_confront_MLloc with "HGC Hvsy Hsimy") as "(HGC&Hvsy)". erewrite Hscrub.
      iClear "Hsimy Hsimy2 Hvalsy". clear fgny2 fgny3 γy2.
      iMod ("Hclose2" with "[$Htok HγLy Hvsy]") as "Htok".
      { iNext. iExists _. iFrame. }

      wp_apply (wp_read_tag_header with "[$HGC ]"); [done..|].
      iIntros "HGC".
      wp_apply (wp_read_tag_header with "[$HGC ]"); [done..|].
      iIntros "HGC". do 3 wp_pure _.

      wp_apply (wp_length_header with "[$HGC ]"); [done..|].
      iIntros "HGC". wp_pure _.
      wp_apply (wp_length_header with "[$HGC ]"); [done..|].
      iIntros "HGC". do 2 wp_pure _.
      case_bool_decide; last first.
      { wp_pures.
        wp_apply (wp_int2val with "HGC"); [done..|].
        iIntros (w) "[HGC %]". iApply ("Cont" $! false with "HGC Htok").
        iPureIntro. repeat case_bool_decide; naive_solver. }
      wp_pures.

      wp_apply (wp_Malloc); [done..|].
      change (Z.to_nat 1) with 1; cbn.
      iIntros (ℓi) "(Hℓi&_)". rewrite !loc_add_0. wp_pure _.
      wp_apply (wp_store with "Hℓi").
      iIntros "Hℓi". wp_pure _.
      wp_apply (wp_Malloc); [done..|].
      change (Z.to_nat 1) with 1; cbn.
      iIntros (ℓr) "(Hℓr&_)". rewrite !loc_add_0. wp_pure _.
      wp_apply (wp_store with "Hℓr").
      iIntros "Hℓr". wp_pure _.

      assert (∃ (i:Z), (0 ≤ i)%Z ∧ i = 0%Z) as (i&Hipos&Hi). 1: eexists; split; last done; lia.
      rewrite - {1} Hi. clear Hi.
      assert (∃ (b:bool), C_intf.LitV b = C_intf.LitV true) as (b&Hb). 1: by eexists.
      rewrite - {1} Hb. clear Hb.
      revert H3.
      generalize (length vvx). intros xlen.
      generalize (length vvy). intros ylen Heq%Nat2Z.inj'. subst ylen.
      clear vvx vvy lvvx lvvy.

      iLöb as "Hloop" forall (i b Hipos).

      wp_pures.
      wp_apply (wp_load with "Hℓi").
      iIntros "Hℓi". wp_pures.
      case_bool_decide; last first.
      { wp_pures.
        wp_apply (wp_load with "Hℓr").
        iIntros "Hℓr". wp_pures.
        wp_apply (wp_free with "Hℓi"). iIntros "_". wp_pures.
        wp_apply (wp_free with "Hℓr"). iIntros "_". wp_pures.
        wp_apply (wp_int2val with "HGC"); [done..|].
        iIntros (w) "[HGC %]". iApply ("Cont" $! b with "HGC Htok").
        iPureIntro. repeat case_bool_decide; naive_solver. }

      wp_pures.
      wp_apply (wp_load with "Hℓi").
      iIntros "Hℓi".

      iMod (na_inv_acc_open_timeless with "Hinvx1 Htok") as "[(%vvx&Hvsx&HγLx) (Htok & Hclose1)]"; [done..|].
      iMod (na_inv_acc_open with "Hinvx2 Htok") as "Hinv2O"; [try done..|]. 1: solve_ndisj.
      iPoseProof (pgm_elem_pers_agree with "Hvsx Hxlen") as "%Hxlen". cbn in Hxlen.
      iMod (ml_to_mut with "[$HGC $Hvsx]") as "(%lvvx&%γx2&%fgnx2&HGC&Hgamx&#Hsimx&#Hvalsx)".
      iPoseProof (lloc_own_pub_inj_2 with "Hfgnx Hsimx") as "%Heq".
      specialize (Heq (ltac:(eauto))). subst γx2.
      iPoseProof (big_sepL2_length with "Hvalsx") as "%Hlensx".
      wp_apply (wp_readfield with "[$HGC $Hgamx]"); [try done..| ].
      1: rewrite -Hlensx Hxlen; lia.
      iIntros (lvxi wxi) "(HGC&Hgamx&%Hluxi&%Hreprxi)".
      iDestruct "Hinv2O" as "[(%vvx2&Hvstyp&HγRx) (Htok & Hclose2)]".
      iPoseProof (ghost_var.ghost_var_agree with "HγLx HγRx") as "%Heq". subst vvx2.
      destruct (vvx !! (Z.to_nat i)) as [vxi|] eqn:Hvxi; last first.
      { exfalso. apply lookup_ge_None in Hvxi. rewrite Hlensx in Hvxi. apply lookup_lt_Some in Hluxi. lia. }
      iPoseProof (big_sepL_lookup with "Hvstyp") as "#Hvxityp". 1: exact Hvxi.
      iPoseProof (big_sepL2_lookup with "Hvalsx") as "#Hsimlvx". 1: exact Hvxi. 1: done.
      iMod (mut_to_ml_store with "[$HGC $Hgamx $Hvalsx]") as "(HGC&%fgnx3&%lx3&Hvsx&Hsimx2)".
      iAssert (⌜ℓx = lx3⌝)%I as "%Heq".
      { iPoseProof (lloc_own_pub_inj_1 with "Hfgnx Hsimx2") as "%Heq".
        specialize (Heq (ltac:(eauto))) as [HL HR]. subst. done. }
      subst lx3.
      iPoseProof (GC_confront_MLloc with "HGC Hvsx Hsimx") as "(HGC&Hvsx)". erewrite Hscrub.
      iClear "Hsimx Hsimx2 Hvalsx". clear fgnx2 fgnx3.
      iMod ("Hclose2" with "[$Htok HγRx Hvstyp]") as "Htok". 1: iNext; iExists _; iFrame.
      iMod ("Hclose1" with "[$Htok HγLx Hvsx]") as "Htok". 1: iNext; iExists _; iFrame.

      wp_apply (wp_load with "Hℓi").
      iIntros "Hℓi".

      iMod (na_inv_acc_open_timeless with "Hinvy1 Htok") as "[(%vvy&Hvsy&HγLy) (Htok & Hclose1)]"; [done..|].
      iMod (na_inv_acc_open with "Hinvy2 Htok") as "Hinv2O"; [try done..|]. 1: solve_ndisj.
      iPoseProof (pgm_elem_pers_agree with "Hvsy Hylen") as "%Hylen". cbn in Hylen.
      iMod (ml_to_mut with "[$HGC $Hvsy]") as "(%lvvy&%γy2&%fgny2&HGC&Hgamy&#Hsimy&#Hvalsy)".
      iPoseProof (lloc_own_pub_inj_2 with "Hfgny Hsimy") as "%Heq".
      specialize (Heq (ltac:(eauto))). subst γy2.
      iPoseProof (big_sepL2_length with "Hvalsy") as "%Hlensy".
      wp_apply (wp_readfield with "[$HGC $Hgamy]"); [try done..| ].
      1: rewrite -Hlensy Hylen; lia.
      iIntros (lvyi wyi) "(HGC&Hgamy&%Hluyi&%Hrepryi)".
      iDestruct "Hinv2O" as "[(%vvy2&Hvstyp&HγRy) (Htok & Hclose2)]".
      iPoseProof (ghost_var.ghost_var_agree with "HγLy HγRy") as "%Heq". subst vvy2.
      destruct (vvy !! (Z.to_nat i)) as [vyi|] eqn:Hvyi; last first.
      { exfalso. apply lookup_ge_None in Hvyi. rewrite Hlensy in Hvyi. apply lookup_lt_Some in Hluyi. lia. }
      iPoseProof (big_sepL_lookup with "Hvstyp") as "#Hvyityp". 1: exact Hvyi.
      iPoseProof (big_sepL2_lookup with "Hvalsy") as "#Hsimlvy". 1: exact Hvyi. 1: done.
      iMod (mut_to_ml_store with "[$HGC $Hgamy $Hvalsy]") as "(HGC&%fgny3&%ly3&Hvsy&Hsimy2)".
      iAssert (⌜ℓy = ly3⌝)%I as "%Heq".
      { iPoseProof (lloc_own_pub_inj_1 with "Hfgny Hsimy2") as "%Heq".
        specialize (Heq (ltac:(eauto))) as [HL HR]. subst. done. }
      subst ly3.
      iPoseProof (GC_confront_MLloc with "HGC Hvsy Hsimy") as "(HGC&Hvsy)". erewrite Hscrub.
      iClear "Hsimy Hsimy2 Hvalsy". clear fgny2 fgny3.
      iMod ("Hclose2" with "[$Htok HγRy Hvstyp]") as "Htok". 1: iNext; iExists _; iFrame.
      iMod ("Hclose1" with "[$Htok HγLy Hvsy]") as "Htok". 1: iNext; iExists _; iFrame.

      wp_bind (FunCall _ _).
      iApply ("IH" with "[] [] [] HGC Hvxityp Hvyityp Htok"); [try done..|].
      iIntros "!>" (bn wret) "HGC Htok %Hreprret".
      wp_pure _.
      wp_apply (wp_val2int with "HGC"); [done..|].
      iIntros "HGC". destruct bn; last first.
      + wp_pures.
        wp_apply (wp_store with "Hℓr").
        iIntros "Hℓr". wp_pures.
        wp_apply (wp_store with "Hℓi").
        iIntros "Hℓi". wp_pures.
        wp_apply (wp_load with "Hℓi").
        iIntros "Hℓi". wp_pures.
        case_bool_decide; try lia. wp_pures.
        wp_apply (wp_load with "Hℓr").
        iIntros "Hℓr". wp_pures.
        wp_apply (wp_free with "Hℓi"). iIntros "_". wp_pures.
        wp_apply (wp_free with "Hℓr"). iIntros "_". wp_pures.
        wp_apply (wp_int2val with "HGC"); [done..|].
        iIntros (w) "[HGC %]". iApply ("Cont" $! false with "HGC Htok").
        iPureIntro. repeat case_bool_decide; naive_solver.
      + wp_pures.
        wp_apply (wp_load with "Hℓi").
        iIntros "Hℓi". wp_pures.
        wp_apply (wp_store with "Hℓi").
        iIntros "Hℓi". wp_pure _.
        iApply ("Hloop" with "[] Cont Htok HGC Hℓi Hℓr").
        iPureIntro. lia.
  Qed.

End C_specs.