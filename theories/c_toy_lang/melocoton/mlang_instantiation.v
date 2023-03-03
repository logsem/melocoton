From stdpp Require Export binders strings.
From stdpp Require Import gmap.
From iris.algebra Require Export ofe.
From iris.heap_lang Require Export locations.
From iris.prelude Require Import options.
From melocoton.mlanguage Require Export mlanguage.
From melocoton.c_toy_lang Require Export lang metatheory.
From melocoton.c_toy_lang.melocoton Require Import lang_instantiation.
From melocoton.interop Require Import lang_to_mlang.

Canonical Structure C_mlang := (lang_to_mlang C_lang).


