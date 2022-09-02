From iris.algebra Require Import auth.
From iris.base_logic.lib Require Import mono_nat.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre adequacy.
From melocoton.ml_toy_lang Require Import proofmode notation.
From iris.prelude Require Import options.

Class heapGpreS Σ := HeapGpreS {
  heapGpreS_iris :> invGpreS Σ;
  heapGpreS_heap :> gen_heapGpreS loc (option val) Σ;
  heapGpreS_inv_heap :> inv_heapGpreS loc (option val) Σ;
  heapGpreS_proph :> proph_mapGpreS proph_id (val * val) Σ;
  heapGS_step_cnt :> mono_natG Σ;
}.

Definition heapΣ : gFunctors :=
  #[invΣ; gen_heapΣ loc (option val); inv_heapΣ loc (option val);
    proph_mapΣ proph_id (val * val); mono_natΣ].
Global Instance subG_heapGpreS {Σ} : subG heapΣ Σ → heapGpreS Σ.
Proof. solve_inG. Qed.

(* TODO: The [wp_adequacy] lemma is insufficient for a state interpretation
with a non-constant step index function. We thus use the more general
[wp_strong_adequacy] lemma. The proof below replicates part of the proof of
[wp_adequacy], and it hence would make sense to see if we can prove a version
of [wp_adequacy] for a non-constant step version. *)
Definition heap_adequacy Σ {p:ml_program} `{!heapGpreS Σ} s e σ φ :
  (∀ `{!heapGS Σ}, ⊢ inv_heap_inv -∗ WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hwp.
  apply adequate_alt; intros t2 σ2 [n [κs ?]]%erased_steps_nsteps.
  eapply (wp_strong_adequacy Σ _); [|done].
  iIntros (Hinv).
  iMod (gen_heap_init σ.(heap)) as (?) "[Hh _]".
  iMod (inv_heap_init loc (option val)) as (?) ">Hi".
  iMod (proph_map_init nil ∅) as (?) "Hp".
  iMod (mono_nat_own_alloc) as (γ) "[Hsteps _]".
  iDestruct (Hwp (HeapGS _ _ _ _ _ _ _ _) with "Hi") as "Hwp".
  iModIntro.
  iExists (λ σ ns κs nt, (gen_heap_interp σ.(heap) ∗
                          mono_nat_auth_own γ 1 ns))%I.
  iExists [(λ v, ⌜φ v⌝%I)], (λ _, True)%I, _ => /=.
  iFrame.
  iIntros (es' t2' -> ? ?) " _ H _".
  iApply fupd_mask_intro_discard; [done|]. iSplit; [|done].
  iDestruct (big_sepL2_cons_inv_r with "H") as (e' ? ->) "[Hwp H]".
  iDestruct (big_sepL2_nil_inv_r with "H") as %->.
  iIntros (v2 t2'' [= -> <-]). by rewrite to_of_val.
Qed.
