From iris.proofmode Require Import base.
From transfinite.base_logic.lib Require Import fancy_updates.
From melocoton Require Export language_commons.
From melocoton.language Require Import language.
From iris.prelude Require Import options.

Record prog_environ `{!indexT} {val} (Λ : language val) Σ := Penv {
  penv_prog : gmap string Λ.(func);
  penv_proto : string -d> list val -d> ((outcome val) -d> iPropO Σ) -d> iPropO Σ;
}.
Global Arguments Penv {_ _ _ _} _ _.
Global Arguments penv_prog {_ _ _ _} _.
Global Arguments penv_proto {_ _ _ _} _.

Notation "⟨ p , Ψ ⟩" := (Penv p Ψ : prog_environ _ _).
