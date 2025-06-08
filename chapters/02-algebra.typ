#import "../style.typ": *
#import "@preview/fletcher:0.5.7" as fletcher: diagram, node, edge, shapes

#show: doc => chapter(doc)

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

Next, defining algebraic structures in type theory is done through records, which contain not only the underlying types of the structures but also all the operations and their properties.
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

In practice, it is more customary to separate the definition of the "essence" of the structure from its properties, since when working with #link(<hLevelSet>)[sets], most properties will be #link(<hLevelMereProp>)[mere propositions].
For example, the `·IdL` is a #link(<hLevelMereProp>)[mere proposition] because its underlying type $A$ is a set, which means all paths in $A$ are mere propositions.
In the @the_agda_community_cubical_2024 library, the properties are separated into a record called `IsMonoid`, and there is a corresponding `isPropIsMonoid`.

== Abelian groups and modules

#definition[Abelian group][
  An abelian group $G$ consists of a set $G$, equipped with an identity element $0$, inverse function $-$, and a commutative binary operation, $(+)$ satisfying the following axioms:
  
  - associativity $propEq(a + (b + c), (a + b) + c)$
  - left- and right- identity $propEq(0 + a, a)$ and $propEq(a + 0, a)$
  - inverse $propEq(a + (- a), 0)$ and $propEq((- a) + a, 0)$
  - commutativity $propEq(a + b, b + a)$
] <abelianGroup>

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

== Subgroups and quotients

#definition[Subgroup][A *subgroup* $H$ of a group $G$ is itself a group whose underlying subset $carrier(H)$ is a subset of the underlying set $carrier(G)$, such that the group and inverse operations remain closed in the subset.]

Following the earlier examples of storing properties in records, we can encode the definition of a subgroup in cubical Agda as:

```
record isSubgroup (H : ℙ G) : Type ℓ where
  field
    id-closed  : (1g ∈ H)
    op-closed  : {x y : G} → x ∈ H → y ∈ H → x · y ∈ H
    inv-closed : {x : G} → x ∈ H → inv x ∈ H
```

where `(H : ℙ G)` indicates that `H` is an element of the power set of $carrier(G)$.
The power set is defined as a kind of proposition over the underlying elements.
For example, if $G$ is the group of all natural numbers $NN$, and $H$ is the subset comprising of natural numbers satisfying the proposition $sans("isEven")$, then an element $h$ of $H$ could be the pair $(2, p)$ where $p$ is an element of $sans("isEven")(2)$.

== Images and kernels

A couple examples of subgroups we will encounter quite often are _images_ and _kernels_.

The image of a homomorphism (or more generally, any function) is the set of all elements of the codomain that are mapped by the homomorphism.
The only way to provide a witness of this fact is to provide the corresponding member of the domain.
For some homomorphism $isTyp(f, A -> B)$, we may want to define $sans("isInIm")(f,a)$, then, as $sum_(isTyp(a,A)) propEq(f(a),b)$.
However, this leads us to a problem: if there happened to be different proofs of $propEq(f(a),b)$, we would have different elements of the image, leading to potentially _more_ elements in the image than the codomain.
In fact, we don't even want to know which elements $a$ of the domain map to $b$, since there may be multiple such $a$'s.
Thus the best way to define the image is by propositionally truncating the proof.

#definition[Image][Let $f$ be a homomorphism from $A$ to $B$. Let $a$ be any element from $A$, and $b$ from $B$. Then, the proposition $sans("isInIm")$ is defined as:

$ defEq(sans("isInIm")(f,b), norm(sum_(isTyp(a,A)) propEq(f(a),b))_1) $

The image subtype of $B$ is:

$ defEq(sans("Im")(f), sum_(isTyp(b,B)) sans("isInIm")(f,b)) $] <image>

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

A principled way to represent such a structure in HoTT is by using a higher inductive type, as in @lamiaux_computing_2023[section 3.1].
This approach creates a constructor for zero, each homogeneous element, an inductively defined constructor which represents addition, and paths representing the basic properties such as associativity and identity.

However, for purposes of constructing a spectral sequence, we merely need the grading as a "group holder," to uniformly manipulate pieces of this map.
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

A straightforward way of defining this would be as a pair of some degree shift $d$ and a family of functions $(isTyp(i, G)) -> sans("AbGroupHom")(A_i, B_(i + d))$.

One problem that crops up when defining homomorphisms the "obvious" way is that when computing a composition of two homomorphisms $defEq(h, g compose f)$, we would like to get a homomorphism of degree $deg(f) + deg(g)$.
This means functions in $h$ must be of type $arro(A_n, A_(n + (deg(f) + deg(g))))$.
However, in order to compose $g$ with $f$, we must use the degree-$(n+deg(f))$ piece of $g$, giving us $isTyp((g_(n + deg(f)) compose f_n), arro(A_n, A_((n + deg(f)) + deg(g))))$.
As you can see, the codomain has two slightly different degrees.

In HoTT, this equality is unfortunately not definitional. We do _assume_ associativity as a #link(<abelianGroup>)[group axiom], however, we do not have the ability to uniformly refer to elements of the codomain.
An element $m$ cannot simultaneously occur in type $A_((a + b) + c)$ and $A_(a + (b + c))$.
Given that this is such a fundamental layer, these type discrepancies will poison every operation we would like to do involving composition.

@FvDFormalizationHigherInductive2018 utilizes a clever trick to avoid excessive transports in homomorphism composition.
By making graded functions _defined_ by the "endpoints" and propositionally proving their relationship to the degree shift $d$, we can eliminate many (but not all) transports dealing with codomain degree confusion.

#definition[Graded module homomorphism][
  For graded modules $A$ and $B$, a graded module homomorphism is a triple $(d, p, f)$ with the following data:

  - $isTyp(d, G tilde.eq G)$.
  - $isTyp(p, (i : G) -> propEq(d(i), i + d(0)))$.
  - $isTyp(f, (i, j : G) -> (p : propEq(d(i), j)) -> LeftModuleHom(A_i, B_j))$.
]

Note that $d$ is a _type_ equivalence rather than a group equivalence.
The group equivalence would require the underlying function to respect the group operation, which a degree shift such as $lambda x . x + d$ would not: $(x + y) + d eq.not (x + d) + (y + d)$.
But we only need this equivalence for relating indexes, so their group property is not desired.

For example, using this definition makes composition simpler: $g compose f$ is a three-way composition of parts:

- the degree can be composed by transitivity of equivalences
- $p$ can be proven for all $i$ using some simple algebra
- composing $f_i$ with $g_(i + deg(f))$ is a straightforward composition of group homomorphisms, since the grading lines up properly: given some $isTyp(i\, j, G)$ and a proof $isTyp(p, propEq((i + deg(f)) + deg(g), j))$, we can compose the functions
  
  $
   isTyp(f(i, i + d, refl), arro(A_i, B_(i + deg(f)))) \
   isTyp(g(i + deg(f), j, p), arro(A_(i + deg(f)), B_j)) $

Although this method makes compositions easier, transports are not eliminated entirely.
For instance, in defining the graded quotient map $A -> A / S$, we encounter a non-definitional identity between $d$ and $d + 0$.
This had to be resolved via composition with essentially a "transporting" homomorphism from $A_d$ to $A_(d + 0)$.
For cases like this, it became easier to manage by writing computation rules that provided the path between the high-level objects of interest directly, hiding the transports.
For example:

#text(size: 10pt)[```
mkGAGHom' : (d : Id ≃ Id) 
  → (pd : (i : Id) → d .fst i ≡ (i + d .fst 0g)) 
  → ((i : Id) → AbGroupHom (A i) (B (d .fst i))) 
  → GAGHom A B
mkGAGHom' d pd fn = mkGAGHom d pd (λ {i} {j} p → compGroupHom (fn i) (transportHom (cong B p)))

mkGAGHom'-compute : (d : Id ≃ Id) 
  → (pd : (i : Id) → d .fst i ≡ (i + d .fst 0g)) 
  → (fn : (i : Id) → AbGroupHom (A i) (B (d .fst i))) 
  → (id : Id) → (m : ⟨ A id ⟩)
  → ((mkGAGHom' d pd fn →, id) .fst m) ≡ (fn id .fst m)
mkGAGHom'-compute d pd fn id m i = transportRefl (transportRefl (fn id .fst m) i) i
```]

To make managing grading slightly easier, we use functions `f →, i` and `f ←, j`, which represent functions 'starting at' index $i$ and functions 'landing in' index $j$, respectively.
More precisely, these functions have the following types:

$
  isTyp((f -> i), sans("GroupHom")(A_i, B_(i + deg(f)))) \
  isTyp((f <- i), sans("GroupHom")(A_(i - deg(f)), B_i)) \
$