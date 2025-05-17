#import "./style.typ": *
#import "@preview/fletcher:0.5.7" as fletcher: diagram, node, edge, shapes
#let gr = "gr"
#let Path = $sans("Path")$
#let PathP = $sans("PathP")$
#set heading(numbering: "1.1.1.")

#show: doc => template(
  title: [my thesis],
  doc,
)

This is a report on progress towards a formalized construction of spectral sequences within cubical Agda.

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

An important operation on cubical path types is _homogeneous composition_.

#figure(diagram(spacing: 15mm, node-inset: 4pt,
  node((0, 0), $x$, name: "x1"),
  node((0, -1), $x$, name: "x2"),
  node((1, 0), $y$, name: "y"),
  node((1, -1), $z$, name: "z"),
  edge(<x2>, <z>, "..>"),
  edge(<x1>, <x2>, "->", $refl$, label-side: left),
  edge(<x1>, <y>, "->", $p$, label-side: right),
  edge(<y>, <z>, "->", $q$, label-side: right),
))

== Mechanization

Agda @agda_developers_agda_2025 is a dependently typed programming language and proof assistant developed at the Chalmers University of Technology.

The construction presented here is based on work by @FvDFormalizationHigherInductive2018.
Our results are mechanized using Cubical Agda @vezzosi_cubical_2021.
Much of the formalization also uses an existing library of work by others, collectively available at https://github.com/agda/cubical/.

The work accompanying this paper can be found at https://git.mzhang.io/michael/msthesis.
Here is a link to some of the main theorems that have been proven:

#table(stroke: none, columns: (auto, 1fr),
  table.header([*Theorem*], [*Link*]),
  [@derivedCouple], [#link("https://git.mzhang.io/michael/msthesis/src/branch/main/src/ExactCouple/Derived.agda")[`ExactCouple.Derived.derivedCouple`]],
)

In addition, much of the theory of graded modules had to be developed for cubical Agda.

== Higher inductive types

== Homotopy levels

Homotopy levels, also known as $n$-types, describe the amount of "interesting" homotopical information exists in a type.
For this topic, I find it best to begin with an example.

#example[
  Suppose a type $A$ has two distinct elements $x, y$. Then, suppose there exist two distinct paths between those types $p, q$. Then, suppose there are distinct paths between those paths $r, s$. Finally, all paths in $propEq(r, s)$ are equal; $propEq(r, s)$ is contractible, and as a consequence, all higher paths are also contractible.
  Then, $A$ is said to have a homotopy level of 3.
]

Here is a table of some common homotopy levels:

#table(stroke: none, columns: (auto, auto, 1fr),
  table.header([*Level*], [*Name*], [*Description*]),
  [0], [_contractible type_ <hLevelContr>], [This type is equivalent to the unit type.],
  [1], [_mere proposition_ <hLevelMereProp>], [Cannot distinguish elements apart.],
  [2], [_set_ <hLevelSet>], [Cannot distinguish paths between elements apart.],
  [3], [_groupoid_], [Cannot distinguish 2-paths apart.],
)

#property[If a type $A$ has homotopy level $n$, then paths in $A$ will have homotopy level $n-1$.]

Truncations can be used to artificially reduce the homotopy level of a type.
A truncation can be thought of as a higher inductive type that adds path constructors for all paths above a particular dimension.

Why would we want to reduce the homotopy level of a type?
One big reason would be to avoid having to solve coherence between higher paths.
For example, consider the type representing "the image of $isTyp(f,arro(A,B))$":

$ isTyp(sans("Image"), sum_(y:B) (norm(sum_(x:A) (propEq(f(x),b)))_1)) $

If we wanted to compare elements of this type, identity is functorial over products, so we would need to compare $y_1$ and $y_2$, which we may have techniques for.
However, comparing the equality term $propEq(f(x),b)$ may be extremely difficult, or even impossible if we allow an infinite hierarchy of path types.
In this case (and many such cases in mathematics), we only care _that_ an element $y$ is in the image, not which particular $x$ it was mapped from.
Truncating paths to a certain homotopy level, for example, mere propositions, allows us to make this comparison.

One useful property of truncations is that we don't fully lose the information that was truncated.
For example, we can map out of a mere proposition to produce another mere proposition.
In a sense, as long as we are not "leaking" more information, we can perform computations on the underlying data.

In fact, we can take this one step further, with the following theorem due to @kraus_general_2015:

#theorem[
  Given a function $isTyp(f, arro(A, B))$ such that:

  - $B$ is a set (homotopy level 2)
  - $f$ is _weakly constant_ (in other words, for all $isTyp(x\, y, A)$, $propEq(f(x), f(y))$)

  There exists a function $isTyp(f', arro(norm(A)_1, B))$ such that $f' = |\_|_1 compose f$
] <propSetElim>

== Cubical paths

= Algebra

== Algebra in Agda

Doing algebra in a formal proof assistant is a bit more verbose and often more ugly than doing algebra on pen and paper.
Some of this pain can be alleviated using tactic-based proof assistants, where an interactive interface displays the current goal and certain tactics are used to simplify the goal.
However, this often leads to cryptic-looking proofs, and is often intractable to read without having access to the theorem prover.
Using Agda's mix-fix notation, the cubical library in @the_agda_community_cubical_2024 creates a powerful "equational reasoning" syntax that combines the interactivity with a more readable notation akin to two-column proofs.

For example, consider this lemma:

#text(size: 10pt)[```
lemma : invEq d 0g ≡ - d .fst 0g
lemma =
  invEq d 0g                                ≡⟨ sym (+IdL _) ⟩ 
  0g + invEq d 0g                           ≡⟨ cong (_+ invEq d 0g) (sym (+InvL (d .fst 0g))) ⟩ 
  (- d .fst 0g + d .fst 0g) + invEq d 0g    ≡⟨ sym (+Assoc _ _ _) ⟩
  - d .fst 0g + (d .fst 0g + invEq d 0g)    ≡⟨ cong ((- d .fst 0g) +_) (+Comm _ _) ⟩
  - d .fst 0g + (invEq d 0g + d .fst 0g)    ≡⟨ cong ((- d .fst 0g) +_) (sym (pd (invEq d 0g))) ⟩
  - d .fst 0g + d .fst (invEq d 0g)         ≡⟨ cong ((- d .fst 0g) +_) (secEq d 0g) ⟩
  - d .fst 0g + 0g                          ≡⟨ +IdR (- d .fst 0g) ⟩
  - d .fst 0g                               ∎
```]

The left side is a restatement of the _type_ of the expression, while the right side is the proof term that shows why the term to its left is equal to the term on the next line.
Under the hood, the `_≡⟨_⟩` is stitching together all the proof terms on the right side using path concatenation.

The way we define algebraic structures in type theory is through records, which contain not only the underlying types of the structures but also all the operations and their properties.
This is akin to requiring all the properties to be proven in order to even show that the structure is well-defined.

For example, consider the monoid. It could be defined this way:

#text(size: 10pt)[```
record Monoid : Type (ℓ-suc ℓ) where
  field
    A : Type ℓ                                        -- underlying type
    _·_ : A → A → A                                   -- op
    e : A                                             -- identity
    ·IdL : (x : A) → e · x ≡ x                        -- left identity
    ·IdR : (x : A) → x · e ≡ x                        -- right identity
    ·Assoc : (x y z : A) → x · (y · z) ≡ (x · y) · z  -- associativity
    is-set : isSet A                                  -- UIP
```]

In practice, we would want to separate the definition of the "essence" of the structure from its properties, since when working with #link(<hLevelSet>)[sets], most properties will be #link(<hLevelMereProp>)[mere propositions].
For example, the `·IdL` is a #link(<hLevelMereProp>)[mere proposition] because its underlying type $A$ is a set, which means all paths in $A$ are mere propositions.
In the @the_agda_community_cubical_2024 library, the properties are separated into a record called `IsMonoid`, and there is a corresponding `isPropIsMonoid`.

== Abelian groups and modules

#definition[Abelian group][
  An abelian group $G$ consists of a set $G$, equipped with an identity element $0$, inverse function $-$, and a commutative binary operation, $(+)$ satisfying the following axioms:
  
  - associativity $propEq(a + (b + c), (a + b) + c)$
  - left- and right- identity $propEq(0 + a, a)$ and $propEq(a + 0, a)$
  - inverse $propEq(a + (- a), 0)$ and $propEq((- a) + a, 0)$
  - commutativity $propEq(a + b, b + a)$
]

As is customary in algebra, we will represent the group and the underlying _carrier_ set with the same notation.
The $0$ element of a group $G$ may be denoted $0_G$ when it benefits to know which group is being discussed.

The binary operation is abstracted but since it behaves so much like addition in most contexts, we will use the plus $+$ operator to represent it.
Likewise, we may use $op(+)_G$ to explicitly declare the group being used. 

#definition[Group homomorphism][
  A group homomorphism $f$ between abelian groups $A$ and $B$ is a function between the carrier sets $A$ and $B$, with the property that it preserves the group operation:

  $ propEq(f(a+b), f(a)+f(b)) $
]

#corollary[For a homomorphism $f$ between $A$ and $B$, $propEq(f(0_A), 0_B)$.]

#corollary[For a homomorphism $f$ between $A$ and $B$, $propEq(f(-a), -f(a)).$]

#definition[Module][
  For some ring $R$, a _left_ $R$-module $M$ consists of an abelian group as well as a scalar multiplication operation $(dot)$ and multiplicative identity $1$ satisfying additional axioms:

  - associativity $propEq((r dot s) dot x, r dot (s dot x))$
  - distributivity $propEq((r + s) dot x, r dot x + s dot x)$ and $propEq(r dot (x + y), r dot x + r dot y)$
  - left identity $propEq(1 dot x, x)$

  Note that operations such as $r dot s$ and $r + s$ between elements of the ring $R$ use the ring's multiplication and addition operators rather than the group's.
]

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
Given the two-dimensional nature of spectral sequences, we will frequently work with a *bidegree*, which is simply a product of two separate degrees.

Formally, graded modules are equipped with a structure:

$ R_m dot M_n subset.eq M_(m+n) $

A principled way to represent such a structure in HoTT is by using a higher inductive type, such as in @lamiaux_computing_2023.
This approach creates a constructor for zero, each homogeneous element, an inductively defined constructor which represents addition, and paths representing the basic properties such as associativity and identity.

However, for purposes of constructing a spectral sequence, we merely need the grading to uniformly manipulate pieces of this map.
Attempts at using this higher inductive type approach lead to proving many properties of direct sums that ended up not being useful for the goals in this paper, although they may be useful in general.
For example, although there is no meaning in adding values of different homotopy groups together, this operation must still be defined and properties such as associativity proved for it.

We will alternately define graded modules by _entirely ignoring_ the total module aspect as well as the structure requirement.

#definition[Graded module][
  For a ring $R$ and an abelian group $G$, a *$G$-graded $R$-module* is defined as a function:

  $ defEq(GradedModule_R, arro(G, LeftModule_R)) $
]

== Degrees and homomorphisms

Modules also have homomorphisms, but the grading nature makes it slightly more complicated.
From a high level, a homomorphism must also be a family of functions between individual graded pieces.
We can have the functions be _degree-preserving_ -- meaning the functions in the family have the same degree in the domain and codomain:

$ isTyp(f_n, arro(A_n, B_n)) $

#figure(diagram(
  spacing: (0mm, 20mm), node-outset: 2mm,
  {
    node((-1, 0), $...$)
    for i in range(6) { node((i, 0), $A_#i$, width: 16mm, shape: shapes.rect, stroke: black) }
    node((6, 0), $...$)
    node((-1, 1), $...$)
    for i in range(6) { node((i, 1), $B_#i$, width: 16mm, shape: shapes.rect, stroke: black) }
    node((6, 1), $...$)
    for i in range(6) { edge((i, 0), (i, 1), "->", $f_#i$, label-anchor: "center", label-sep: 0mm, label-fill: true)}
  }
))

However, we can have homomorphisms with degree shifts.
We say a homomorphism has *degree* $k$, if the functions in the homomorphism shift the degrees of the codomain by $k$:

$ isTyp(f_n, arro(A_n, B_(n+k))) $

#figure(diagram(
  spacing: (0mm, 20mm), node-outset: 2mm,
  {
    node((-1, 0), $...$)
    for i in range(6) { node((i, 0), $A_#i$, name: "A" + str(i), width: 16mm, shape: shapes.rect, stroke: black) }
    node((6, 0), $...$)
    node((-1, 1), $...$)
    for i in range(6) { node((i, 1), $B_#i$, name: "B" + str(i), width: 16mm, shape: shapes.rect, stroke: black) }
    node((6, 1), $...$)
    for i in range(4) {
      let a = label("A" + str(i) + ".south")
      edge(label("A" + str(i) + ".south"), label("B" + str(i+2) + ".north"), "->", $f_#i$, label-anchor: "center", label-sep: 0mm, label-fill: true)}
  }
))

The degree of $f$ is denoted $deg(f)$.

One problem that crops up when defining homomorphisms the "obvious" way is that when computing a composition of two homomorphisms $defEq(h, g compose f)$, we would like to get a homomorphism of degree $deg(f) + deg(g)$.
This means functions in $h$ must be of type $arro(A_n, A_(n + (deg(f) + deg(g))))$.
However, in order to compose $g$ with $f$, we must use the degree-$(n+deg(f))$ piece of $g$, giving us $isTyp((g_(n + deg(f)) compose f_n), arro(A_n, A_((n + deg(f)) + deg(g))))$.
As you can see, the codomain has two slightly different degrees.
In HoTT, we can resolve this by transporting along the path given by the associativity of addition of groups.
However, this transport will be present everywhere compositions are used.

We follow the trick given by @FvDFormalizationHigherInductive2018 to avoid excessive transports in homomorphism composition.

#definition[Graded module homomorphism][
  For graded modules $A$ and $B$, a graded module homomorphism is a triple $(d, p, f)$ with the following data:

  - $isTyp(d, G tilde.eq G)$.
  - $isTyp(p, (i : G) -> propEq(d(i), i + d(0)))$.
  - $isTyp(f, (i, j : G) -> (p : propEq(d(i), j)) -> LeftModuleHom(A_i, B_j))$.
]

= Homotopy Theory

== Homotopy groups

#definition[Homotopy group][The $n$th homotopy group of a pointed space $A$ is defined as

$ defEq(pi_n (A), norm(Omega^n (A))_0) $]

#property[For all $n > 1$, $pi_n (X)$ is an abelian group.] <homotopyGroup>

== Exactness and exact sequences

#definition[Exactness][Given pointed types $A, B, C$ and pointed functions $isTyp(f, arro(A, B))$ and $isTyp(g, arro(B, C))$, we say $f$ and $g$ are *exact* if $propEq(imOf(f), kerOf(g))$.]

#figure(canvas({
  import cetz.draw: *
  let midsize = 0.5
  circle((3, 0), radius: (1, 2))
  content((rel: (0, 2.5)))[$C$]

  merge-path(fill: rgb("#ffeeeecc"), stroke: none, {
    circle((-3, 0), radius: (1, 2))
    circle((-3, -2), radius: 0)
    circle((0, -midsize * 2), radius: 0)
    circle((0, 0), radius: (midsize, midsize * 2))
  })
  line((-3, 2), (0, midsize * 2), stroke: rgb("#999999"))
  line((-3, -2), (0, -midsize * 2), stroke: rgb("#999999"))
  content((-1.5, 0))[$f$]

  circle((-3, 0), radius: (1, 2))
  content((rel: (0, 2.5)))[$A$]

  circle((3, 0), radius: 0.08, fill: black)
  content((rel: (0.5, 0)))[$0_C$]

  circle((0, 0), radius: (1, 2))
  content((rel: (0, 2.5)))[$B$]

  line((0, midsize * 2), (3, 0), stroke: rgb("#999999"))
  line((0, -midsize * 2), (3, 0), stroke: rgb("#999999"))
  merge-path(close: true, stroke: none, fill: rgb("#eeffee99"), {
    line((0, midsize * 2), (3, 0))
    line((3, 0), (0, -midsize * 2))
  })
  content((1.5, 0))[$g$]

  circle((0, 0), radius: (midsize, midsize * 2), stroke: rgb("#999"), fill: rgb("#ffeeff"))
  content(
    (rel: (0, 1.3)),
    frame: "rect",
    stroke: none,
    fill: rgb("#ffffffee"),
    padding: .1,
    text(fill: rgb("#999"), size: .8em, $sans("Im")(f) = sans("Ker")(g)$)
  )
}), caption: $sans("Im")(f) = sans("Ker")(g)$)

As a direct consequence, the composition $g compose f$ always results in the trivial map that maps everything to $0$.
This definition of exactness also specializes to groups and modules, since those are simply pointed types with more structure.

A series of functions where every pair of consecutive functions are exact is called an _exact sequence_.
Exact sequences give us a way to concisely represent certain properties of functions.
As an example, consider this exact sequence:

#figure(diagram(spacing: 8mm,
  node($0$), edge("->"),
  node((rel: (1, 0)), $A$), edge("->", $f$),
  node((rel: (1, 0)), $B$), edge("->"),
  node((rel: (1, 0)), $0$)
))

The exactness at $A$ tells us that the kernel of $f$ is _only_ $0_A$.
This corresponds to the fact that $f$ is *injective*.
The exactness at $B$ tells us that the image of $f$ is all of $B$.
This corresponds to the fact that $f$ is *surjective*.
These two facts combined tell us that $f$ is an *isomorphism*.

An exact sequence is considered _long_ if it spans infinitely in one or both directions.
For example, the long exact sequence of homotopy groups relates the $n$th homotopy groups derived from a pointed function $f$:

#figure(diagram(spacing: 12mm, label-sep: 1mm,
  node($pi_1 (B)$), edge("<-"),
  node((rel: (-1, 0)), $pi_1 (A)$), edge("<-"),
  node((rel: (-1, 0)), $pi_1 (F)$), edge("<-", $delta$),
  node((rel: (2, -1)), $pi_2 (B)$), edge("<-"),
  node((rel: (-1, 0)), $pi_2 (A)$), edge("<-"),
  node((rel: (-1, 0)), $pi_2 (F)$), edge("<-", $delta$),
  node((rel: (2, -1)), $pi_3 (B)$), edge("<-"),
  node((rel: (-1, 0)), $pi_3 (A)$), edge("<-"),
  node((rel: (-1, 0)), $pi_3 (F)$), edge("<.."),
  node((rel: (2, -1)), $dots$),
))

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

== Eilenberg-MacLane spectra

There is a construction known as the Eilenberg-MacLane space, which forms an $Omega$-spectrum.
Using the representability theorem due to @brown_cohomology_1962, this spectrum exactly represents ordinary cohomology.
Additionally, prior work by @LFEilenbergMacLaneSpacesHomotopy2014 brought Eilenberg-MacLane spaces to HoTT.
Thus, these spaces are incredibly convenient to work with when constructing spectral sequences within type theory.
In this section we will summarize the definition and the properties of Eilenberg-MacLane spaces without proof.

#definition[$K(G, 1)$][For some group $G$, let $K(G, 1)$ be a type defined by the higher inductive type found in $section$3.1 of @LFEilenbergMacLaneSpacesHomotopy2014.]

#definition[$K(G, n)$][#TODO[write]]

#property[For all $n, m in NN$ such that $m != n$, $pi_n (K(G, m))$ is isomorphic to the trivial group.]

#definition[Eilenberg-MacLane spectrum][For any abelian group $G$, the Eilenberg-MacLane spaces $K(G, n)$ form a spectrum $H A$, such that for all $isTyp(n, ZZ)$:

$ defEq((H A)_n, cases(K(G, n) &"if" n >= 0, 1 &"if" n < 0)) $

where $1$ denotes the trivial pointed space consisting of a single element.
The structure maps are defined as: #TODO[finish]
] <EMSpectrum>


== Cohomology

Cohomology, like #link(<homotopyGroup>)[homotopy groups] and homology, are a way to "measure" the holes in a topological space.
However, homotopy groups are notoriously difficult to compute.
For example, as of writing, we only know the homotopy groups of spheres up to dimension 90.
Tools like homology and cohomology give us an approximation of this information.

The properties of various cohomologies have been distilled into axioms, known as the Eilenberg-Steenrod axioms, due to @eilenberg_axiomatic_1945.
Furthermore, it was shown in @brown_cohomology_1962 @adams_variant_1971 that any generalized cohomology theory that satisfies these axioms is "representable" by a spectrum.

= Spectral sequences

// Spectral sequences, due to @leray_anneau_1946, are a tool in algebraic topology for computing (co)homology groups.
// This is useful is due to (co)homology groups being potentially difficult to compute directly, so it is commonly easier to _approximate_ it by taking filtrations of the space, and making observations about pieces of the (co)homology groups.

// The Serre spectral sequence is one of the earliest spectral sequences.
// Given a Serre fibration $F -> X ->^pi B$, a Serre spectral sequence relates the (co)homology groups of the total space $X$ with the (co)homology groups of the fiber $F$ and the base space $B$.
// Classically, this is constructed using singular (co)homology.
// However, the construction of singular (co)homology in HoTT is challenging, due to simplicial sets not being primitively supported.

// In this work, we will work with a _generalized_ cohomology. This is due to @eilenberg_axiomatic_1945, which introduced axioms that cohomology theories must satisfy.
// It was shown in @brown_cohomology_1962 @adams_variant_1971 that a generalized cohomology theory $cal(E)$ is "representable" by a spectrum $Y_n$. Classically, we would write this as:

// $ cal(E)^n (X) tilde.eq [X, Y_n] $

// In homotopy type theory, we can use truncations to represent homotopy classes, so we are left with the following definition for *cohomology*:

// $ cal(E)^n (X) :equiv norm(X -> Y_n)_0 $

Let us begin with a high level discussion of spectral sequences.
At its core, a spectral sequence is a bookkeeping tool for long exact sequences of (co)homology groups.

...

#definition[Cohomological spectral sequence][
  A cohomological spectral sequence is a pair $(E, d)$.
  
  $E$ is a sequence of pages, indexed by $isTyp(r, NN)$, starting at 2.
  Each page contains an infinite 2-dimensional grid of abelian groups, indexed by $isTyp((p, q), ZZ^2)$, denoted $E^(p, q)_r$.

  $d$ are maps between the abelian groups in $E$.
  For page $r$, $d_r$ maps from $E^(p,q)_r$ to $E^(p+r,q-r+1)_r$. These maps are differentials, meaning consecutive $d_r$ compose to $0$.
] <spectralSequence>

#let stop_before(start, end, shorten, ..args) = {
  import draw: *
  // Extract x and y coordinates
  let (x1, y1) = start
  let (x2, y2) = end
  let m = (y2 - y1) / (x2 - x1)
  let ang = calc.atan2(x2 - x1, y2 - y1)
  let sx = shorten * calc.cos(ang)
  let sy = shorten * calc.sin(ang)
  line((x1 + sx, y1 + sy), (x2 - sx, y2 - sy), ..args)
}

#figure({
  table(
    columns: (auto, auto),
    stroke: none,
    canvas({
      import draw: *
      set-style(stroke: 0.4pt)
      grid((0, 0), (6.5, 4.5), step: 1, stroke: gray + 0.2pt)
      line((-0.5, 0), (6.5, 0), mark: (end: "stealth"))
      line((0, -0.5), (0, 4.5), mark: (end: "stealth"))
      for x in (1, 2, 3, 4, 5, 6) {
        for y in (1, 2, 3, 4) {
          circle((x, y), fill: black, radius: 0.08)
          if x < 6 {
            stop_before((x, y), (x+1, y), 0.15,
              mark: (end: "straight"),
              stroke: (paint: rgb("#ff9999"), thickness: 0.6pt)
            )
          }
        }
      }
    }),
    canvas({
      import draw: *
      set-style(stroke: 0.4pt)
      grid((0, 0), (6.5, 4.5), step: 1, stroke: gray + 0.2pt)
      line((-0.5, 0), (6.5, 0), mark: (end: "stealth"))
      line((0, -0.5), (0, 4.5), mark: (end: "stealth"))
      for x in (1, 2, 3, 4, 5, 6) {
        for y in (1, 2, 3, 4) {
          circle((x, y), fill: black, radius: 0.08)
          if x < 5 {
            stop_before((x, y), (x+2, y - 1), 0.15,
              mark: (end: "straight"),
              stroke: (paint: rgb("#ff9999"), thickness: 0.6pt)
            )
          }
        }
      }
    })
  )
}, kind: "image", supplement: [Figure], caption: [Pages $E_(1, 2)$ of a cohomological spectral sequence]) <spectralSequenceFigure>

Although these pages are infinite, we typically operate solely in the first quadrant, such that all other groups are definitionally trivial.

== Exact couples

Exact couples, due to @massey_exact_1952, are a convenient way to "wrap" up the data of a spectral sequence such that its grading can be treated uniformly.
They arise naturally from the classical construction of the Serre spectral sequence, as described in @hatcher_spectral_2004.

We want to represent spectral sequence data this way because it provides extra information that we can use to determine the $d$s of future pages, that the spectral sequence structure doesn't carry by itself.
In this section, we will describe how to iterate an exact couple, and how to use an exact couple to construct a spectral sequence.

Notice that due to the graded nature of the modules, when iterating the exact couples, the degrees of our homomorphisms will slowly shift.
This is what gives us the shifts in @spectralSequenceFigure.

#definition[Exact couple][
  An exact couple $(D, E, i, j, k)$ consists of two graded modules $D, E$ as well as morphisms
  #figure(table(
    stroke: none, columns: (auto, auto, auto),
    column-gutter: 2em,
    [$isTyp(i, arro(D, D))$],
    [$isTyp(j, arro(D, E))$],
    [$isTyp(k, arro(E, D))$],
  ))
  such that they are exact as in the following non-commuting diagram:

  #figure(diagram(cell-size: 5mm, 
    node((0, 0), $D$, name: <D1>),
    edge(label-side: left, "->", $i$),
    node((2, 0), $D$, name: <D2>),
    edge(label-side: left, "->", $j$),
    node((1, 1), $E$, name: <E>),
    edge(label-side: left, <E>, <D1>, $k$, "->"),
  ), caption: "Exact couple")
]

#theorem[Derived couple][
  Given an exact couple $(D, E, i, j, k)$, we can get a _derived_ exact couple $(D', E', i', j', k')$ that contains exactly the homological data required for future pages of the spectral sequence.
] <derivedCouple>
#prf[
  This process is almost entirely an exercise in diagram chasing.
  In HoTT, we will also have the added burden of wrapping and unwrapping all of our data properly through truncations and quotients.

  First, we have $defEq(D', imOf(i))$.

  First, define $defEq(d, j compose k)$. Notice that this goes around the triangle in a strange way, not following the arrows.
]

== Convergence

== Atiyah-Hirzebruch Spectral Sequence


== Serre Spectral Sequence

= Discussion

- Category theory?
- Thoughts on Agda
  - as a proof assistant
  - for learning math
  
#TODO[in the type theory section, talk about the pattern of Carrier, Structure where the structure is typically a prop]
