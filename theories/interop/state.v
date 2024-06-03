From stdpp Require Import base gmap.
(* see basics.v for the definitions of logical values, logical store, etc. *)
From melocoton.interop Require Import basics.

(** This defines the wrapper private state. Like the whole wrapper state (see
   `state` in lang.v), it can be either:
   - a `wrapstateML` when doing internal steps (i.e. executing wrapped ML code);
   - a `wrapstateC` when at a boundary interacting with a C-like component;
*)

Section wrapperstate.

Record wrapstateC : Type := WrapstateC {
  (** logical location → ML location *)
  χC : lloc_map;
  (** logical (block-level) store *)
  ζC : lstore;
  (** logical location → C address.
     Changes when the GC runs and moves/deallocates blocks. *)
  θC : addr_map;
  (** addresses in C memory that are registered as roots *)
  rootsC : list $ gset addr;
}.

Record wrapstateML : Type := WrapstateML {
  (** logical location → ML location *)
  χML : lloc_map;
  (** logical (block level) store *)
  ζML : lstore;
  (** C address → logical location tracked by the root registered at this
     address. *)
  rootsML : list $ roots_map;
  (** the remaining piece of C store not accessible from ML code *)
  privmemML : memory;
}.

End wrapperstate.
