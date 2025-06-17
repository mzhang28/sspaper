#import "../style.typ": *
#import "@preview/fletcher:0.5.7" as fletcher: diagram, node, edge, shapes

#show: doc => chapter(doc)

= Type theory

Type theory is an alternative foundation to set theory for doing constructive mathematics.
One particularly popular flavor of type theory used by proof assistants is _dependent_ type theory (or Martin-Löf type theory (MLTT), due to @martin-lof_intuitionistic_1975), which allows types to depend on values.
A common example of this is a type $sans("Vec")$ (read "Vector"), that is similar to a list, except its length is _part_ of its type.
This allows us to write length-aware functions like:

$ sans("append") : sans("Vec")(m) -> sans("Vec")(n) -> sans("Vec")(m+n) $

Using this concept, we can define an identity type parameterized by two terms $x, y : A$ representing their equality.
Such a type is often written $sans("Id")_A (x, y)$, or $x op(=)_A y$, or even just $x = y$, when their type $A$ is obvious.
This reflects the idea of "propositions as types", also known as the Curry-Howard correspondence.

Due to its more computational nature, dependent type theory lends itself to computer automation, which has led to it being used as a foundational theory upon which many theorem provers and proof assistants are built.

Homotopy type theory (HoTT) @hottbook extends this type theory by interpreting identity as paths in a topological space, which allows the existence of paths between paths, or "higher"-dimensional paths.
Unlike proof-irrelevant systems, this allows multiple non-identical elements of the same identity type.
Homotopy type theory gives us the language to codify the existence of paths with different underlying behavior with the *univalence axiom*, which unifies the notion of equivalence and identity:

$ (A tilde.eq B) tilde.eq (A = B) $

A classic example is that the set of booleans is equivalent to itself in two different ways, identity and negation.
Transporting a boolean element along their corresponding paths will result in opposite values.
Univalence also allows us to recover nice properties such as function extensionality that otherwise cannot be proven with just MLTT.

In the original version of HoTT formulated in @hottbook, univalence is introduced as an _axiom_, as it cannot be proven

Additionally, HoTT introduces _higher inductive types_, which generalize ordinary inductive types but allow for construction of identity types (path constructors) as well as ordinary terms (also called point constructors).

Cubical type theory @cohen_cubical_2016 is an extension of MLTT, a dependent type theory, that adds an interval-based path type for representing propositional equality, as opposed to the inductive identity type originally proposed by Martin-Löf.
The intuition is to have a type $I$ with a DeMorgan structure (operations $and$, $or$, $not$) that can be composed to represent faces of $n$-dimensional cubes.
The vertices of these cubes would be various terms to be identified.
We discuss cubical type theory more in @cubicalPaths.

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

== Higher inductive types <higherInductiveType>

One prominent feature of homotopy type theory is *higher inductive types* (HITs), where the word "higher" refers to "higher-dimensional paths".
Ordinary inductive types are comprised of _point_ constructors, which construct elements in the type, while higher inductive types also include _path_ constructors, which construct non-trivial higher-dimensional paths in the type.

For example, one of the major benefits of higher inductive types is that it creates a principled definition of quotients.
Compared to other ways of defining quotients, HIT quotients have nice computational properties while also avoiding the "setoid hell" of coherences, as well as being "effective" -- being able to recover the original equivalence relation.

Another benefit is that certain topological spaces are expressible synthetically.
For example, a circle, which comprises of a base point and a loop, can be directly expressed as a constructor $base$ and a path constructor $loop$.

$ isTyp(base, S^1) \
isTyp(loop, propEq(base, base)) $

For an ordinary inductive type, we must handle each constructor in order to write a valid eliminator for the overall type.
Higher inductive types are the same, except for the path constructors we must provide paths in the type being mapped to, and prove its coherence.
For example, for the circle, if we wanted to write a function $f$ to eliminate any circle to a type $C$, we would have to provide:

- $isTyp(c_base, C)$ for the $base$ case
- $isTyp(c_loop, propEq(c_base, c_base))$ for the $loop$ case
- a proof that $propEq(ap_f(loop), c_loop)$



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

  There exists a function $isTyp(f', arro(norm(A)_1, B))$ such that $f' = |-|_1 compose f$
] <propSetElim>

== Cubical paths <cubicalPaths>

Cubical type theory @cohen_cubical_2016 uses an alternative definition for the equality type.
Rather than an inductive path type with a single constructor

#TODO[J rule]

#TODO[canonicity]

== Mechanization

Agda @agda_developers_agda_2025 is a dependently typed programming language and proof assistant developed at the Chalmers University of Technology.

The construction presented here is based on work by @FvDFormalizationHigherInductive2018.
Our results are mechanized using Cubical Agda @vezzosi_cubical_2021.
Much of the formalization also uses an existing library of work by others, collectively available at https://github.com/agda/cubical/.

The work accompanying this paper can be found at https://git.mzhang.io/michael/msthesis.
Here is a link to some of the main theorems that have been proven:

// #table(stroke: none, columns: (auto, 1fr),
//   table.header([*Theorem*], [*Link*]),
//   [@derivedCouple], [#link("https://git.mzhang.io/michael/msthesis/src/branch/main/src/ExactCouple/Derived.agda")[`ExactCouple.Derived.derivedCouple`]],
// )

In addition, much of the theory of graded modules had to be developed for cubical Agda.