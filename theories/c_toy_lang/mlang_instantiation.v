From stdpp Require Export binders strings.
From stdpp Require Import gmap.
From iris.algebra Require Export ofe.
From iris.heap_lang Require Export locations.
From iris.prelude Require Import options.
From melocoton.mlanguage Require Export mlanguage.
From melocoton.c_toy_lang Require Export lang metatheory.
From melocoton.c_toy_lang Require Import lang_instantiation.
From melocoton.lang_to_mlang Require Import lang.

Canonical Structure C_mlang := (lang_to_mlang C_lang).


