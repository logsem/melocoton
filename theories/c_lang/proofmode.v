From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From melocoton.c_lang Require Export lang lang_instantiation tactics primitive_laws derived_laws class_instances.
From melocoton.c_lang Require Import notation.
From iris.prelude Require Import options.
Import uPred.

Lemma tac_wp_expr_eval `{!heapGS_C Σ, !invGS_gen hlc Σ} Δ s E Φ e e' :
  (∀ (e'':=e'), e = e'') →
  envs_entails Δ (WP e' @ s; E {{ Φ }}) → envs_entails Δ (WP e @ s; E {{ Φ }}).
Proof. by intros ->. Qed.



Ltac solve_lookup_fixed := let rec go := match goal with
  [ |- context[ @lookup _ _ (@gmap _ ?eqdec _ _) _ ?needle (insert ?key ?val ?rem)]] =>
    (unify key needle; rewrite (@lookup_insert _ _ _ _ _ _ _ _ _ _ _ _ rem key val)) ||
    (rewrite (@lookup_insert_ne _ _ _ _ _ _ _ _ _ _ _ _ rem key needle val); [congruence|go])
| [ |- context[ @lookup _ _ (@gmap _ ?eqdec _ _) _ ?needle (delete ?key ?rem)]] => 
      (unify key needle; rewrite (@lookup_delete _ _ _ _ _ _ _ _ _ _ _ _ rem key)) ||
      (rewrite (@lookup_delete_ne _ _ _ _ _ _ _ _ _ _ _ _ rem key needle); [go|congruence])
| [ |- context[ @lookup _ _ (@gmap _ ?eqdec _ _) _ ?needle (singletonM ?key ?val)]] =>
    (unify key needle; rewrite (@lookup_singleton _ _ _ _ _ _ _ _ _ _ _ _ key val)) ||
    (rewrite (@lookup_singleton_ne _ _ _ _ _ _ _ _ _ _ _ _ key needle val); congruence)
| [ |- context[ @lookup _ _ (@gmap _ ?eqdec _ _) _ ?needle ∅]] => 
    rewrite (@lookup_empty _ _  _ _ _ _ _ _ _ _ _ _ needle) end in repeat (progress (unfold subst; try go; simpl)).

Tactic Notation "wp_expr_eval" tactic3(t) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    notypeclasses refine (tac_wp_expr_eval _ _ _ _ e _ _ _);
      [let x := fresh in intros x; t; unfold x; notypeclasses refine eq_refl|]
  | _ => fail "wp_expr_eval: not a 'wp'"
  end.
Ltac wp_expr_simpl := wp_expr_eval solve_lookup_fixed.

Lemma tac_wp_pure `{!heapGS_C Σ, !invGS_gen hlc Σ} Δ Δ' s E K e1 e2 φ n Φ :
  PureExec φ n (penv_prog s) e1 e2 →
  φ →
  MaybeIntoLaterNEnvs n Δ Δ' →
  envs_entails Δ' (WP (fill K e2) @ s; E {{ Φ }}) →
  envs_entails Δ (WP (fill K e1) @ s; E {{ Φ }}).
 Proof.
  rewrite envs_entails_unseal=> ??? HΔ'. rewrite into_laterN_env_sound /=.
  (* We want [pure_exec_fill] to be available to TC search locally. *)
  pose proof @pure_exec_fill.
  rewrite HΔ' -lifting.wp_pure_step_later //.
 Qed.


Lemma tac_wp_value_nofupd `{!heapGS_C Σ, !invGS_gen hlc Σ} Δ s E Φ v :
  envs_entails Δ (Φ v) → envs_entails Δ (WP (Val v) @ s; E {{ Φ }}).
Proof. rewrite envs_entails_unseal=> ->. by apply wp_value. Qed.

Lemma tac_wp_value `{!heapGS_C Σ, !invGS_gen hlc Σ} Δ s E (Φ : val → iPropI Σ) v :
  envs_entails Δ (|={E}=> Φ v) → envs_entails Δ (WP (Val v) @ s; E {{ Φ }}).
Proof. rewrite envs_entails_unseal=> ->. by rewrite wp_value_fupd'. Qed.

(** Simplify the goal if it is [WP] of a value.
  If the postcondition already allows a fupd, do not add a second one.
  But otherwise, *do* add a fupd. This ensures that all the lemmas applied
  here are bidirectional, so we never will make a goal unprovable. *)
Ltac wp_value_head :=
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E (Val _) (λ _, fupd ?E _ _)) =>
      eapply tac_wp_value_nofupd
  | |- envs_entails _ (wp ?s ?E (Val _) (λ _, wp _ ?E _ _)) =>
      eapply tac_wp_value_nofupd
  | |- envs_entails _ (wp ?s ?E (Val _) _) =>
      eapply tac_wp_value
  end.

Ltac wp_finish :=
  wp_expr_simpl;      (* simplify occurences of subst/fill *)
  try wp_value_head;  (* in case we have reached a value, get rid of the WP *)
  pm_prettify.        (* prettify ▷s caused by [MaybeIntoLaterNEnvs] and
                         λs caused by wp_value *)

Ltac solve_vals_compare_safe :=
  (* The first branch is for when we have [vals_compare_safe] in the context.
     The other two branches are for when either one of the branches reduces to
     [True] or we have it in the context. *)
  fast_done || (left; fast_done) || (right; fast_done).

(** The argument [efoc] can be used to specify the construct that should be
reduced. For example, you can write [wp_pure (EIf _ _ _)], which will search
for an [EIf _ _ _] in the expression, and reduce it.

The use of [open_constr] in this tactic is essential. It will convert all holes
(i.e. [_]s) into evars, that later get unified when an occurences is found
(see [unify e' efoc] in the code below). *)
Tactic Notation "wp_pure" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      unify e' efoc;
      eapply (tac_wp_pure _ _ _ _ K e');
      [iSolveTC                       (* PureExec *)
      |try solve_vals_compare_safe; try eauto (* The pure condition for PureExec --
            handles trivial goals, including [vals_compare_safe] *)
      |iSolveTC                       (* IntoLaters *)
      |wp_finish                      (* new goal *)
      ])
    || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a redex"
  | _ => fail "wp_pure: not a 'wp'"
  end.

(* TODO: do this in one go, without [repeat]. *)
Ltac wp_pures :=
  iStartProof;
  first [ (* The `;[]` makes sure that no side-condition magically spawns. *)
          progress repeat (wp_pure _; [])
        | wp_finish (* In case wp_pure never ran, make sure we do the usual cleanup. *)
        ].

Tactic Notation "wp_if" := wp_pure (If _ _ _).
(* Tactic Notation "wp_if_false" := wp_pure (If (LitV (LitInt 0)) _ _). *)
Tactic Notation "wp_unop" := wp_pure (UnOp _ _).
Tactic Notation "wp_binop" := wp_pure (BinOp _ _ _).
Tactic Notation "wp_op" := wp_unop || wp_binop.
Tactic Notation "wp_let" := wp_pure (Let _ _ _).
Tactic Notation "wp_seq" := wp_let.
Tactic Notation "wp_while" := wp_pure (While _ _).
Tactic Notation "wp_call_direct" := wp_pure (FunCall _ _).


Lemma tac_wp_call `{!heapGS_C Σ, !invGS_gen hlc Σ} Δ s E Φ fn vv e1 :
  (e1 = of_class _ (ExprCall fn vv)) →
  envs_entails Δ (WPCall fn with vv @ s; E {{ Φ }}) →
  envs_entails Δ (WP e1 @ s; E {{ Φ }}).
Proof.
  intros ->.
  rewrite envs_entails_unseal=> Hyp. iIntros "H".
  iApply (wp_call s fn vv E Φ). by iApply Hyp. 
Qed.

Tactic Notation "wp_call" :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      unify K (@nil ectx_item);
      eapply (tac_wp_call _ _ _ _ _ _ e');
      [reflexivity                    (* equality *)
      |pm_prettify                    (* new goal *)
      ])
    || fail "wp_pure:" e "is not a call! Use wp_bind first!"
  | _ => fail "wp_pure: not a 'wp'"
  end.

Tactic Notation "wp_extern" :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' => match e' with FunCall (Val (& ?s)) (map Val ?vv) =>
      iApply (@wp_extern _ C_lang _ _ _ _ K _ s vv); [iPureIntro; try by (vm_compute; reflexivity) | ] end)
    || fail "wp_extern: expression not a call"
  | _ => fail "wp_extern: not a 'wp'"
  end.



Lemma tac_wp_bind `{!heapGS_C Σ, !invGS_gen hlc Σ} K Δ s E Φ e f :
  f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
  envs_entails Δ (WP e @ s; E {{ v, WP f (Val v) @ s; E {{ Φ }} }})%I →
  envs_entails Δ (WP fill K e @ s; E {{ Φ }}).
Proof. rewrite envs_entails_unseal=> -> ->. by apply: wp_bind. Qed.

Ltac wp_bind_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => eapply (tac_wp_bind K); [simpl; reflexivity|reduction.pm_prettify]
  end.

Tactic Notation "wp_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first [ reshape_expr e ltac:(fun K e' => unify e' efoc; wp_bind_core K)
          | fail 1 "wp_bind: cannot find" efoc "in" e ]
  | _ => fail "wp_bind: not a 'wp'"
  end.

(** Heap tactics *)
Section heap.
Context `{!heapGS_C Σ, !invGS_gen hlc Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types Δ : envs (uPredI (iResUR Σ)).
Implicit Types v : val.
Implicit Types z : Z.


Lemma tac_wp_Malloc Δ Δ' s E j K n Φ :
  (0 < n)%Z →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  (∀ l,
    match envs_app false (Esnoc Enil j (array l (DfracOwn 1) (replicate (Z.to_nat n) None))) Δ' with
    | Some Δ'' =>
       envs_entails Δ'' (WP fill K (Val $ LitV $ LitLoc l) @ s; E {{ Φ }})
    | None => False
    end) →
  envs_entails Δ (WP fill K (Malloc (Val $ LitV $ LitInt n)) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ? ? HΔ.
  rewrite -wp_bind. eapply wand_apply; first exact: wp_Malloc.
  rewrite left_id into_laterN_env_sound; apply later_mono, forall_intro=> l.
  specialize (HΔ l).
  destruct (envs_app _ _ _) as [Δ''|] eqn:HΔ'; [ | contradiction ].
  rewrite envs_app_sound //; simpl.
  apply wand_intro_l. by rewrite (sep_elim_l (l ↦C∗ _)%I) right_id wand_elim_r.
Qed.

Lemma tac_wp_free Δ Δ' s E i K l (v:option val) Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l I↦C v)%I →
  (let Δ'' := envs_delete false i false Δ' in
   envs_entails Δ'' (WP fill K (Val $ LitV LitUnit) @ s; E {{ Φ }})) →
  envs_entails Δ (WP fill K (Free (LitV l) (Val (LitV (LitInt 1)))) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ? Hlk Hfin.
  rewrite -wp_bind. eapply wand_apply; first apply wp_free.
  rewrite into_laterN_env_sound -later_sep envs_lookup_split //; simpl.
  rewrite -Hfin wand_elim_r (envs_lookup_sound' _ _ _ _ _ Hlk).
  apply later_mono, sep_mono_r, wand_intro_r. rewrite right_id //.
Qed.


Lemma tac_wp_freeN Δ Δ' s E i K l (v:list $ option val) z Φ :
  z = Z.of_nat (length v) →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦C∗ v)%I →
  (let Δ'' := envs_delete false i false Δ' in
   envs_entails Δ'' (WP fill K (Val $ LitV LitUnit) @ s; E {{ Φ }})) →
  envs_entails Δ (WP fill K (Free (LitV l) (Val (LitV (LitInt z)))) @ s; E {{ Φ }}).
Proof.
  intros ->.
  rewrite envs_entails_unseal=> ? Hlk Hfin.
  rewrite -wp_bind. eapply wand_apply; first apply wp_free_array.
  rewrite into_laterN_env_sound -later_sep envs_lookup_split //; simpl.
  rewrite -Hfin wand_elim_r (envs_lookup_sound' _ _ _ _ _ Hlk).
  apply later_mono, sep_mono_r, wand_intro_r. rewrite right_id //.
Qed.

Lemma tac_wp_load Δ Δ' s E i K b l q v Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (b, l ↦C{q} v)%I →
  envs_entails Δ' (WP fill K (Val v) @ s; E {{ Φ }}) →
  envs_entails Δ (WP fill K (Load (LitV l)) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ?? Hi.
  rewrite -wp_bind. eapply wand_apply; first exact: wp_load.
  rewrite into_laterN_env_sound -later_sep envs_lookup_split //; simpl.
  apply later_mono.
  destruct b; simpl.
  * iIntros "[#$ He]". iIntros "_". iApply Hi. iApply "He". iFrame "#".
  * by apply sep_mono_r, wand_mono.
Qed.

Lemma tac_wp_store Δ Δ' s E i K l (v:option val) v' Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l I↦C v)%I →
  match envs_simple_replace i false (Esnoc Enil i (l ↦C v')) Δ' with
  | Some Δ'' => envs_entails Δ'' (WP fill K (Val $ LitV LitUnit) @ s; E {{ Φ }})
  | None => False
  end →
  envs_entails Δ (WP fill K (Store (LitV l) (Val v')) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ???.
  destruct (envs_simple_replace _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ].
  rewrite -wp_bind. eapply wand_apply; first by eapply wp_store.
  rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply later_mono, sep_mono_r, wand_mono.
Qed.

End heap.

(** The tactic [wp_apply_core lem tac_suc tac_fail] evaluates [lem] to a
hypothesis [H] that can be applied, and then runs [wp_bind_core K; tac_suc H]
for every possible evaluation context [K].

- The tactic [tac_suc] should do [iApplyHyp H] to actually apply the hypothesis,
  but can perform other operations in addition (see [wp_apply] and [awp_apply]
  below).
- The tactic [tac_fail cont] is called when [tac_suc H] fails for all evaluation
  contexts [K], and can perform further operations before invoking [cont] to
  try again.

TC resolution of [lem] premises happens *after* [tac_suc H] got executed. *)
Ltac wp_apply_core lem tac_suc tac_fail := first
  [iPoseProofCore lem as false (fun H =>
     lazymatch goal with
     | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
       reshape_expr e ltac:(fun K e' =>
         wp_bind_core K; tac_suc H)
     | _ => fail 1 "wp_apply: not a 'wp'"
     end)
  |tac_fail ltac:(fun _ => wp_apply_core lem tac_suc tac_fail)
  |let P := type of lem in
   fail "wp_apply: cannot apply" lem ":" P ].

Tactic Notation "wp_apply" open_constr(lem) :=
  wp_apply_core lem ltac:(fun H => iApplyHyp H; try iNext; try wp_expr_simpl)
                    ltac:(fun cont => fail).
Tactic Notation "wp_smart_apply" open_constr(lem) :=
  wp_apply_core lem ltac:(fun H => iApplyHyp H; try iNext; try wp_expr_simpl)
                    ltac:(fun cont => wp_pure _; []; cont ()).

Tactic Notation "wp_alloc" ident(l) "as" constr(H) :=
  let Htmp := iFresh in
  let finish _ :=
    first [intros l | fail 1 "wp_alloc:" l "not fresh"];
    pm_reduce;
    lazymatch goal with
    | |- False => fail 1 "wp_alloc:" H "not fresh"
    | _ => iDestructHyp Htmp as H; wp_finish
    end in
  wp_pures;
  (** The code always allocates arrays *)
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    let process_array _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_wp_Malloc _ _ _ _ Htmp K))
          |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
        [idtac|iSolveTC
         |finish ()]
    in (process_array ())
  | _ => fail "wp_alloc: not a 'wp'"
  end.

Tactic Notation "wp_alloc" ident(l) :=
  wp_alloc l as "?".

Tactic Notation "wp_free" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l I↦C{_} _)%I) => l end in
    iAssumptionCore || fail "wp_free: cannot find" l "I↦ ?" in
  let solve_array_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦C∗{_} _)%I) => l end in
    iAssumptionCore || fail "wp_free: cannot find" l "↦∗ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_free _ _ _ _ _ K));
        [iSolveTC
        |solve_mapsto ()
        |pm_reduce; wp_finish]
      |reshape_expr e ltac:(fun K e' => eapply (tac_wp_freeN _ _ _ _ _ K));
        [idtac
        |iSolveTC
        |solve_array_mapsto ()
        |pm_reduce; wp_finish]; [try done|idtac]
      |fail 1 "wp_free: cannot find 'Free' in" e]
  | _ => fail "wp_free: not a 'wp'"
  end.

Tactic Notation "wp_load" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦C{_} _)%I) => l end in
    iAssumptionCore || fail "wp_load: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_load _ _ _ _ _ K))
      |fail 1 "wp_load: cannot find 'Load' in" e];
    [iSolveTC
    |solve_mapsto ()
    |wp_finish]
  | _ => fail "wp_load: not a 'wp'"
  end.

Tactic Notation "wp_store" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l I↦C{_} _)%I) => l end in
    iAssumptionCore || fail "wp_store: cannot find" l "I↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_store _ _ _ _ _ K))
      |fail 1 "wp_store: cannot find 'Store' in" e];
    [iSolveTC
    |solve_mapsto ()
    |pm_reduce; first [wp_seq|wp_finish]]
  | _ => fail "wp_store: not a 'wp'"
  end.
