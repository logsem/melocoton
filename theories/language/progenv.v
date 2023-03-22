From iris.proofmode Require Import base.
From iris.base_logic.lib Require Import fancy_updates.
From melocoton.language Require Export language.
From iris.prelude Require Import options.

Record prog_environ {val} (Λ : language val) Σ := Penv {
  penv_prog : gmap string Λ.(func);
  penv_proto : string -d> list val -d> (val -d> iPropO Σ) -d> iPropO Σ;
}.
Global Arguments Penv {_ _ _} _ _.
Global Arguments penv_prog {_ _ _} _.
Global Arguments penv_proto {_ _ _} _.

Notation "⟨ p , T ⟩" := (Penv p T : prog_environ _ _).
