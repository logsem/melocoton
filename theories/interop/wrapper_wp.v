From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.language Require Import language weakestpre.
From melocoton.mlanguage Require Import weakestpre.
From melocoton.interop Require Import wrappersem wrapperstate.
From iris.base_logic.lib Require Export ghost_map.
From iris.algebra.lib Require Import excl_auth gset_bij gmap_view.
From iris.algebra Require Import ofe.
From iris.proofmode Require Import proofmode.
From melocoton.c_toy_lang Require Import lang melocoton.lang_instantiation melocoton.primitive_laws.
From melocoton.ml_toy_lang Require Import lang melocoton.lang_instantiation  melocoton.primitive_laws.
From melocoton.interop Require Import linking_wp basics.
Import Wrap.




Section Embed_logic.

Context {hlc : has_lc}.
Context {Σ : gFunctors}.
Context {HeapML : heapGS_ML_gen hlc Σ}.
Context {HeapC : heapGS_C_gen hlc Σ}.

Notation MLval := ML_lang.val.
Notation Cval := C_lang.val.

Implicit Types P : iProp Σ.

Context `{@ghost_mapG Σ lloc block Nat.eq_dec nat_countable}.
Context `{inG Σ (excl_authUR (gsetUR loc))}.
Context `{@ghost_mapG Σ loc lval loc_eq_decision loc_countable}.
Context `{inG Σ (excl_authR (leibnizO addr_map))}.
Context `{inG Σ (viewR (@gset_bij_view_rel loc loc_eq_decision loc_countable lloc Nat.eq_dec nat_countable))}.

Context {γζmut γζimm γζfresh : gname}.
Context {γroots_set : gname}.
Context {γroots_map : gname}.
Context {γθ : gname}.
Context {γχ : gname}.

Definition has_mutability (ζ : lstore) (i' : ismut) := forall l i t v, ζ !! l = Some (i,t,v) -> i = i'.
Definition is_fresh_lstore (χ : lloc_map) (ζ : lstore) : iProp Σ := 
 ⌜∀ (g1 g2 : lloc) (b:block) (l:loc), ζ !! g1 = Some b → χ !! l = Some g2 → g1 ≠ g2⌝.
Definition is_mut_lstore (χ : lloc_map) (σ : store) (ζ : lstore) : iProp Σ := 
   ⌜dom χ = dom σ⌝
 ∗ [∗ map] l ↦ ovl ∈ σ, ∃ (g:lloc) (b:block), ⌜χ !! l = Some g⌝ ∗ ⌜ζ !! g = Some b⌝ ∗ match ovl with
      None => True (* Blocks owned by C *)
    | Some vl => True (* TODO: ⌜b ~ vl⌝ *) end (* Blocks in σ, i.e. references *).

Definition gen_lstore_interp (ζ : lstore) (Pmut Pimm Pfresh : lstore → iProp Σ) : iProp Σ := 
  ∃ ζfresh ζmut ζimm, ⌜ζ = ζfresh ∪ ζmut ∪ ζimm⌝
         ∗ ghost_map_auth γζmut 1 ζmut ∗ ⌜has_mutability ζimm Mut⌝ ∗ Pmut ζmut
         ∗ ghost_map_auth γζimm 1 ζimm ∗ ⌜has_mutability ζimm Immut⌝ ∗ Pimm ζimm
         ∗ ghost_map_auth γζfresh 1 ζfresh ∗ ⌜has_mutability ζimm Mut⌝ ∗ Pfresh ζfresh
         ∗ ⌜dom ζfresh ## dom ζmut ∧ dom ζfresh ## dom ζimm ∧ dom ζmut ## dom ζimm⌝.

Definition C_lstore_interp (ζ : lstore) (χ : lloc_map) (σvirt : store) : iProp Σ := 
    gen_lstore_interp ζ
      (is_mut_lstore χ σvirt)
      (fun _ => ⌜True⌝)%I
      (is_fresh_lstore χ).

Definition GC (θ : addr_map) : iProp Σ := 
   own γθ (@excl_auth_frag (leibnizO _) θ)
   ∗ ∃ (roots : gset addr) (rootsmap : gmap loc lval),
       own γroots_set (excl_auth_frag roots)
     ∗ ghost_map_auth γroots_map 1 rootsmap
     ∗ ⌜dom rootsmap = roots⌝
     ∗ ⌜roots_are_live θ rootsmap⌝
     ∗ ([∗ map] a ↦ v ∈ rootsmap, (∃ w, a ↦C w)).

Definition C_store_interp (ζ : lstore) (χ : lloc_map) (θ : addr_map) (roots : gset addr) : iProp Σ := ∃ σvirt χvirt,
    C_lstore_interp ζ (χ ∪ χvirt) σvirt
  ∗ own γroots_set (excl_auth_auth roots)
  ∗ (∃ n, state_interp σvirt n)
  ∗ (own γχ (gset_bij_auth (DfracOwn 1) (map_to_set pair (χ ∪ χvirt))))
  ∗ ⌜GC_correct ζ θ⌝.

Definition ML_lstore_interp (ζ : lstore) (χ : lloc_map) : iProp Σ := 
    gen_lstore_interp ζ
      (fun ζmut => ⌜ζmut = ∅⌝%I)
      (fun _ => ⌜True⌝)%I
      (is_fresh_lstore χ).

Definition GC_token_remnant (roots : gset addr) : iProp Σ :=
   own γθ (@excl_auth_frag (leibnizO _) (∅ : addr_map))
 ∗ own γroots_set (excl_auth_frag roots)
 ∗ ghost_map_auth γroots_map 1 (∅ : gmap loc lval)
 ∗ ([∗ set] a ∈ roots, (a O↦ None)). (* Is deallocated in C *)


Definition ML_store_interp (ζ : lstore) (χ : lloc_map) (roots : roots_map) (memC : memory) : iProp Σ := 
    ML_lstore_interp ζ χ
  ∗ own γroots_set (excl_auth_auth (dom roots)) ∗ GC_token_remnant (dom roots)
  ∗ (∃ n, state_interp memC n)
  ∗ (own γχ (gset_bij_auth (DfracOwn 1) (map_to_set pair χ))).

Definition wrap_state_interp (σ : Wrap.state) : iProp Σ := match σ with
  Wrap.CState ρc mem => (∃ n, state_interp mem n) ∗ C_store_interp (ζC ρc) (χC ρc) (θC ρc) (rootsC ρc)
| Wrap.MLState ρml σ => (∃ n, state_interp σ n) ∗ ML_store_interp (ζML ρml) (χML ρml) (rootsML ρml) (privmemML ρml)
end.

(* Old stuff, please ignore

Global Program Instance wrapGS :
  mlanguage.weakestpre.mlangGS hlc _ Σ wrap_lang
:= {
  state_interp := wrap_state_interp;
  at_boundary := False%I;
}.

Global Program Instance wrap_linkableGS :
  linkableGS (wrap_lang) (λ σ, ⌜ True ⌝%I)%I
:= {
  private_state_interp := (λ _, True)%I;
}.
Next Obligation. simpl. intros *. inversion 1. iIntros "?". by iFrame. Qed.
Next Obligation.
  simpl. intros ? []. iIntros "? _". iModIntro. iExists _. by iFrame.
Qed.
Next Obligation. simpl. Print Wrap.split_state. iIntros (σ) "_ Hσ". iPureIntro. exists σ, (). constructor. Qed.

Local Canonical Structure embed_mlang : mlanguage val := lang_to_mlang Λ.

Definition penv_to_mlang (pe : language.weakestpre.prog_environ Λ Σ) :
  mlanguage.weakestpre.prog_environ (lang_to_mlang Λ) Σ
:=
  {| penv_prog := pe.(language.weakestpre.penv_prog);
     penv_proto := pe.(language.weakestpre.penv_proto) |}.

Lemma wp_embed (e : Λ.(language.expr)) pe E Φ :
  ⊢ WP e @ pe; E {{ Φ }} -∗ WP e @ (penv_to_mlang pe); E {{ Φ }}.
Proof using.
  iStartProof. iLöb as "IH" forall (e). destruct pe as [p T].
  rewrite {1} @language.weakestpre.wp_unfold /language.weakestpre.wp_pre. simpl.
  rewrite {1} wp_unfold /mlanguage.weakestpre.wp_pre.
  iIntros "H" (σ) "(%n & Hσ)". iMod ("H" $! σ n with "Hσ") as "[(%x & %H1 & Hσ & H)|[(%s' & %vv & %K' & %H1 & %H2 & H3)|(%Hred & H3)]]".
  - iLeft. iModIntro. iExists x. iFrame. iSplitR; first done. iExists n. iFrame.
  - iRight. iLeft. iMod "H3" as "(%Ξ & Hσ & HT & Hr)". iExists s', vv, K'. iModIntro.
    iSplitR; first done. iSplitR; first done. iSplitR; first done. iSplitL "Hσ"; first by iExists n.
    iExists Ξ. iFrame. iNext. iIntros (v) "[Hv _]". iApply "IH". by iApply "Hr".
  - iRight. iRight. iModIntro. iSplitR.
    { iPureIntro. destruct Hred as (e' & σ' & H'). eexists (fun '(e2,σ2) => e2 = e' ∧ σ2 = σ'). inversion H'; subst. econstructor. eexists; split; first done.
      econstructor; first done. intros ? ? ( <- & <- ); done. }
    iIntros (X Hstep). inversion Hstep as (K & e' & -> & Hx). inversion Hx; subst.
    unshelve iMod ("H3" $! σ2 _ (Prim_step _ K _ _ _ _ _ _ _ _ _ H3)) as "H3". 1-2:done.
    do 2 iModIntro. iMod "H3" as "(Hσ & Hwp)". iModIntro. iExists _, _. iSplitR; first (iPureIntro; apply H5; repeat split).
    iSplitL "Hσ"; first by iExists _. iApply "IH". iApply "Hwp".
Qed.

*)

End Embed_logic.
