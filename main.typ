#import "@preview/fletcher:0.5.7" as fletcher: diagram, node, edge
#let gr = "gr"
#let Path = $sans("Path")$
#let PathP = $sans("PathP")$
#show math.frac: it => [#it.num #sym.slash #it.denom]

= Introduction

This is a report on progress towards a formalized construction of spectral sequences within a flavor of cubical type theory.

== The Serre Spectral Sequence

Spectral sequences, due to Jean Leray @leray_anneau_1946, are a data structure in algebraic topology used for computing homology groups.
The _Serre_ spectral sequence, due to Jean-Pierre Serre @serre_homologie_1951, is one of the earliest such examples.
Given a Serre fibration,

$ F arrow.r.hook X arrow.r B $

such that $B$ is path-connected, the Serre spectral sequence relates the (co)homology group of the total space $X$ to the (co)homology groups of the fiber $F$ and base space $B$.
TODO: Why is this desired?

=== Disclaimers

As is often in mathematics, analogous constructions exist in different contexts.
Here we will specify which specific flavor of the Serre spectral sequence is being analyzed.

- We will be working with _cohomology_ groups.
- Our spectral sequences will be _first-quadrant_ spectral sequences. That is, $E^*_(p,q) = 0$ for $p, q < 0$.
- 

=== Constructing the Serre spectral sequence

Let us briefly review the construction of a Serre spectral sequence.

We begin with a Serre fibration, which looks like this:

$ F arrow.r X arrow.r^pi B $

where $B$ is 

// We begin with some space $X$, that can be filtered into a sequence of subspaces:

// $ dots subset X_(p-1) subset X_p subset X_(p+1) subset dots $

// such that $X = union.big_p X_p$. Although this is not a requirement, for convenience we will assume that it is bounded at 0:

// $ ({0} = X_0) subset X_1 subset X_2 subset X_3 subset dots $

// // Every filtered object has an associated graded object, defined by taking the direct sum of quotients of successive filtrations:

// // $ gr X = plus.circle.big_p X_p / X_(p-1) $

// Due to the subobject relationship, we can arrange each $X_(p-1)$ and $X_p$ into the following short exact sequence (TODO: Proof):

// #figure(diagram(spacing: 5mm, $0 edge("->") & X_(p-1) edge("->") & X_p edge("->") & X_p/X_(p-1) edge("->") & 0$))

// Somehow we get to the long exact sequence of cohomology groups:

// #figure(diagram(spacing: 5mm, $
//   dots edge("->") &
//   H^(n-1) (X_(p-1)) edge("->", delta) &
//   H^n (X_(p-1)) edge("->", i) &
//   H^n (X_p) edge("->", j) &
//   H^n (X_p,X_(p-1)) edge("->") &
//   H^(n+1) (X_(p-1)) edge("->") &
//   dots
// $))

// We call $delta$ the "connecting homomorphism."
  
== Cubical type theory

Cubical type theory @cohen_cubical_2016 is an extension of Martin-Löf Type Theory @martin-lof_intuitionistic_1975 that adds a $[0, 1]$-interval-based path type for representing propositional equalities rather than the inductive definition originally formulated by Martin-Löf.

The intuition is that given two points $x, y$ of type $A$, the interval type $Path_A (x, y)$ can be thought of as the type of proofs that $x$ and $y$ should be identified.
Given some $p : Path_A (x , y)$, we think of $p(0) = x$ and $p(1) = y$ as definitional equalities.
This gives us a way to reason algebraically about paths.
For example, we can think of the inverse of a path as a new path defined as $p^(-1)(i) = p(not i)$.

In particular, this interval-based path type gives us a way to directly compare elements of different types without transport.
Suppose we had a path $A : Path_cal(U) (A_0, A_1)$. We could express the propositional equality between $x : A_0$ and $y : A_1$ using a single dependent path $PathP_(i mapsto A(i)) (x, y)$.

The results in this paper have been developed in a proof assistant, Agda @agda_developers_agda_2025, which implements a flavor of cubical type theory with computational univalence and higher inductive types @vezzosi_cubical_2021.
The results use the following flags:

- `--safe`, ensuring any features that may make Agda prove false are absent (i.e, `postulate`)
- `--cubical`, enabling the cubical features.

= Type theory

#bibliography("zotero.bib")