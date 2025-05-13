#import "./style.typ": *
#import "@preview/fletcher:0.5.7" as fletcher: diagram, node, edge
#let gr = "gr"
#let Path = $sans("Path")$
#let PathP = $sans("PathP")$
#set heading(numbering: "1.1.1.")

#show: doc => template(
  title: [my thesis],
  doc,
)

This is a report on progress towards a formalized construction of spectral sequences within a flavor of cubical type theory.

= Type theory

Type theory is an alternative foundation to set theory for doing constructive mathematics.
One particularly popular flavor of type theory used by proof assistants is _dependent_ type theory (or Martin-Löf type theory (MLTT), due to @martin-lof_intuitionistic_1975), which allows types to depend on values.
A common example of this is a type $sans("Vec")$ (read "Vector"), that is similar to a list, except its length is _part_ of its type.
This allows us to write length-aware functions like:

$ sans("append") : sans("Vec")(m) -> sans("Vec")(n) -> sans("Vec")(m+n) $

Using this concept, we can define an identity type parameterized by two terms $x, y : A$ representing their equality.
Such a type is often written $sans("Id")_A (x, y)$, or $x op(=)_A y$, or even just $x = y$, when their type $A$ is obvious.

Homotopy type theory (HoTT) @hottbook extends this type theory with the *univalence axiom*, which unifies the notion of equivalence and identity:

$ (A tilde.eq B) tilde.eq (A = B) $

This equivalence is introduced to MLTT as an _axiom_, and it allows us to recover nice properties such as function extensionality that otherwise cannot be proven with just MLTT.

Additionally, HoTT introduces _higher inductive types_, which generalize ordinary inductive types but allow for construction of identity types (path constructors) as well as ordinary terms (also called point constructors).


Cubical type theory @cohen_cubical_2016 is an extension of MLTT, a dependent type theory, that adds an interval-based path type for representing propositional equality, as opposed to the inductive identity type originally proposed by Martin-Löf.
The intuition is to have a type $I$ with a DeMorgan structure (operations $and$, $or$, $not$) that can be composed to represent faces of $n$-dimensional cubes.
The vertices of these cubes would be various terms to be identified.


== Mechanization

The construction presented here is based on work by @FvDFormalizationHigherInductive2018.
Our results are mechanized using Cubical Agda @vezzosi_cubical_2021.

= Algebra

== Direct sum and grading

When working with spectral sequences, it is convenient to introduce the notion of *graded modules*.
For a ring $R$, a graded $R$-module $M$ is a module that can be decomposed into a direct sum of modules $M_(1..n)$ such that

$ M = plus.circle.big_(n in NN) M_n $

A member of one of the graded pieces $M_i$ is called a _homogeneous_ element.
A good example of structure with grading is the set of polynomials.
Each polynomial, like $x^2 + 2x + 1$ can be decomposed into a single term with a single degree term, like just $x^2$.

#figure(table(
  columns: (auto, auto, auto, auto),
  align: center,
  stroke: (x, y) => if y == 5 { (top: (dash: "solid")) } else if x == 0 { (right: (dash: "solid")) } else if x > 1 { (left: (dash: "dotted")) },
  [$dots.v$], [], [], [],
  [$M_3$], [], [], [],
  [$M_2$], [$x^2$], [ ], [ ],
  [$M_1$], [ ], [$2x$], [ ],
  [$M_0$], [ ], [ ], [1],
  [$M$], [$x^2$], [$2x$], [1],
  // header-separator: full,
))

Just like in polynomials, the individual graded pieces are designated by their *degree*, which is an element of some group $G$.

Formally, graded modules are equipped with a structure:

$ R_m dot M_n subset.eq M_(m+n) $

A principled way to represent such a structure in HoTT is by using a higher inductive type, such as in @lamiaux_computing_2023.

However, for purposes of constructing a spectral sequence, we merely need the grading to uniformly manipulate pieces of this map.
We will alternately define graded modules by _entirely ignoring_ the total module aspect as well as the structure requirement.

#definition[Graded module][
  For a ring $R$ and an abelian group $G$, a *$G$-graded $R$-module* is defined as a function:

  $ defEq(GradedModule_R, arro(carrier(G), LeftModule_R)) $
]

== Degrees and homomorphisms

Modules also have homomorphisms, but the grading nature makes it slightly more complicated.
From a high level, a homomorphism must also be a family of functions between individual graded pieces.
We can have the functions be _degree-preserving_ -- meaning the functions in the family have the same degree in the domain and codomain:

$ isTyp(f_n, arro(A_n, B_n)) $

However, we can have homomorphisms with degree shifts.
We say a homomorphism has *degree* $k$, if the functions in the homomorphism shift the degrees of the codomain by $k$:

$ isTyp(f_n, arro(A_n, B_(n+k))) $

The degree of $f$ is denoted $deg(f)$.

One problem that crops up when defining homomorphisms the "obvious" way is that when computing a composition of two homomorphisms $defEq(h, g compose f)$, we would like to get a homomorphism of degree $deg(f) + deg(g)$.
This means functions in $h$ must be of type $arro(A_n, A_(n + (deg(f) + deg(g))))$.
However, in order to compose $g$ with $f$, we must use $isTyp(g_(n + deg(f)), arro(A_(n + deg(f)), A_((n + deg(f)) + deg(g))))$.
As you can see, the codomain has two slightly different degrees.
In HoTT, we can resolve this by transporting along the path given by the associativity of addition of groups.
However, this transport will be present everywhere compositions are used.

We follow the trick given by @FvDFormalizationHigherInductive2018 to avoid transports in homomorphism composition.

#definition[Graded module homomorphism][
  For graded modules $A$ and $B$, a graded module homomorphism is a triple $(d, p, f)$ with the following data:

  - $isTyp(d, G tilde.eq G)$.
  - $isTyp(p, (i : G) -> propEq(d(i), i + d(0)))$.
  - $isTyp(f, (i, j : G) -> (p : propEq(d(i), j)) -> LeftModuleHom(A_i, B_j))$.
]

  
= Spectral sequences

Spectral sequences, due to @leray_anneau_1946, are a tool in algebraic topology for computing (co)homology groups.
This is useful is due to (co)homology groups being potentially difficult to compute directly, so it is commonly easier to _approximate_ it by taking filtrations of the space, and making observations about pieces of the (co)homology groups.

The Serre spectral sequence is one of the earliest spectral sequences.
Given a Serre fibration $F -> X ->^pi B$, a Serre spectral sequence relates the (co)homology groups of the total space $X$ with the (co)homology groups of the fiber $F$ and the base space $B$.
Classically, this is constructed using singular (co)homology.
However, the construction of singular (co)homology in HoTT is challenging, due to simplicial sets not being primitively supported.

In this work, we will work with a _generalized_ cohomology. This is due to @eilenberg_axiomatic_1945, which introduced axioms that cohomology theories must satisfy.
It was shown in @brown_cohomology_1962 @adams_variant_1971 that a generalized cohomology theory $cal(E)$ is "representable" by a spectrum $Y_n$. Classically, we would write this as:

$ cal(E)^n (X) tilde.eq [X, Y_n] $

In homotopy type theory, we can use truncations to represent homotopy classes, so we are left with the following definition for *cohomology*:

$ cal(E)^n (X) :equiv norm(X -> Y_n)_0 $

= Homotopy Theory

== Exact sequences



== Spectra

In stable homotopy theory, it is customary to work with spectra in place of spaces.
This has some nice properties, including that the suspension functor $Sigma$ and the loop space functor $Omega$ are inverses of each other.

#figure(diagram(spacing: 6mm,
  edge(".."),
  node((rel: (1, 0)), $Y_(-1)$), edge(".."),
  node((rel: (1, 0)), $Y_(-2)$), edge(".."),
  node((rel: (1, 0)), $Y_0$), edge(".."),
  node((rel: (1, 0)), $Y_1$), edge(".."),
  node((rel: (1, 0)), $Y_2$), edge(".."),
))

#definition("Spectrum")[
  A *spectrum* $X$ is defined as a sequence of pointed topological spaces:

  $ isTyp(X, arro(ZZ, typ_*)) $
  
  along with structure maps between adjacent pairs of spaces:

  $ arro(X_n, Omega X_(n+1)) $
]

The indexing type is written here as $ZZ$, but in reality it can be any infinitely increasing structure.
@FvDFormalizationHigherInductive2018 uses an abstract `succ_str` to represent the indexing type.

#definition[$Omega$-spectrum][
  An *$Omega$-spectrum* $X$ is a spectrum such that the structure maps are weak equivalences.

  $ X_n tilde.eq Omega X_(n+1) $
]

#definition[Homotopy group of a spectrum][]

== Eilenberg-MacLane spaces and their spectra

There is a construction known as the Eilenberg-MacLane space, which forms an $Omega$-spectrum.
Using the representability theorem due to @brown_cohomology_1962, this spectrum exactly represents ordinary cohomology.
Additionally, prior work by @LFEilenbergMacLaneSpacesHomotopy2014 brought Eilenberg-MacLane spaces to HoTT.
Thus, these spaces are incredibly convenient to work with when 
constructing spectral sequences.

#definition[$K(G, 1)$][For some group $G$, let $K(G, 1)$ be a type defined by the higher inductive type found in $section$3.1 of @LFEilenbergMacLaneSpacesHomotopy2014.]

#definition[$K(G, n)$][#TODO[write]]

#property[For all $n, m in NN$ such that $m != n$, $pi_n (K(G, m))$ is isomorphic to the trivial group.]

