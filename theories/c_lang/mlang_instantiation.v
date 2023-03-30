From stdpp Require Export binders strings.
From stdpp Require Import gmap.
From iris.algebra Require Export ofe.
From iris.heap_lang Require Export locations.
From iris.prelude Require Import options.
From melocoton.mlanguage Require Export mlanguage.
From melocoton.c_interface Require Export resources.
From melocoton.c_lang Require Export lang metatheory primitive_laws.
From melocoton.c_lang Require Import lang_instantiation.
From melocoton.lang_to_mlang Require Import lang weakestpre.
From melocoton.mlanguage Require Import weakestpre.


Canonical Structure C_mlang := (lang_to_mlang C_lang).

Global Instance C_mlang_linkable `{SI: indexT} `{Σ: gFunctors} `{!heapG_C Σ}
: linkableG (lang_to_mlang C_lang) public_state_interp.
Proof.
  apply lang_to_mlang_linkableG.
Defined.