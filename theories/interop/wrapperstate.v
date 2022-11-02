From stdpp Require Import base gmap.
(* see basics.v for the definitions of logical values, logical store, etc. *)
From melocoton.interop Require Import basics.

(* This defines the wrapper private state. Like the whole wrapper state (see
   `state` in wrappersem.v), it can be either:

   - a `wrapstateML` at a boundary when interacting with another ML-like
     component;
   - a `wrapstateC` when doing internal steps (ie executing wrapped C code).
*)

Section wrapperstate.

Record wrapstateC : Type := WrapstateC {
  χC : lloc_map;
  ζC : lstore;
  θC : addr_map;
  rootsC : gset addr;
  privσC : store;

  χC_injective : ∀ ℓ1 ℓ2 γ,
    χC !! ℓ1 = Some γ → χC !! ℓ2 = Some γ → ℓ1 = ℓ2;
  θC_injective : ∀ γ1 γ2 a,
    θC !! γ1 = Some a → θC !! γ2 = Some a → γ1 = γ2;
  dom_θC_in_ζC :
    dom θC ⊆ dom ζC;
  codom_χC_is_mut : ∀ ℓ γ,
    χC !! ℓ = Some γ → ∃ tg vs, ζC !! γ = Some (Mut, tg, vs);
  (* TODO: ... *)
}.

Record wrapstateML : Type := WrapstateML {
  χML : lloc_map;
  ζML : lstore;
  rootsML : roots_map;
  privmemML : memory;

  χML_injective : ∀ ℓ1 ℓ2 γ,
    χML !! ℓ1 = Some γ → χML !! ℓ2 = Some γ → ℓ1 = ℓ2;
  codom_χML_is_mut : ∀ ℓ γ,
    χML !! ℓ = Some γ → ∃ tg vs, ζML !! γ = Some (Mut, tg, vs);
  (* TODO: ... *)
}.

End wrapperstate.
