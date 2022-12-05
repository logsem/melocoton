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
  (* ML location → logical location *)
  χC : lloc_map;
  (* logical (block-level) store *)
  ζC : lstore;
  (* logical location → C address.
     Changes when the GC runs and moves/deallocates blocks. *)
  θC : addr_map;
  (* addresses in C memory that are registered as roots *)
  rootsC : gset addr;

  χC_injective : ∀ ℓ1 ℓ2 γ,
    χC !! ℓ1 = Some γ → χC !! ℓ2 = Some γ → ℓ1 = ℓ2;
  θC_injective : ∀ γ1 γ2 a,
    θC !! γ1 = Some a → θC !! γ2 = Some a → γ1 = γ2;
  dom_θC_in_ζC :
    dom θC ⊆ dom ζC;
  (* TODO: ... *)
}.

Record wrapstateML : Type := WrapstateML {
  (* ML location → logical locations *)
  χML : lloc_map;
  (* logical (block level) store *)
  ζML : lstore;
  (* C address → logical location tracked by the root registered at this
     address. *)
  rootsML : roots_map;
  (* the remaining piece of C store not accessible from ML *)
  privmemML : memory;

  χML_injective : ∀ ℓ1 ℓ2 γ,
    χML !! ℓ1 = Some γ → χML !! ℓ2 = Some γ → ℓ1 = ℓ2;
  (* TODO: ... *)
}.

End wrapperstate.
