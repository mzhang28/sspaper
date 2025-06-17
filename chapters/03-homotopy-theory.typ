#import "../style.typ": *
#import "@preview/fletcher:0.5.7" as fletcher: diagram, node, edge, shapes

#show: doc => chapter(doc)

= Homotopy Theory

The primary goal of algebraic topology is to distinguish spaces by using algebraic invariants to measure holes.

== Homotopy groups

One of the fundamental ways to classify spaces is by measuring its holes using homotopy groups.

#definition[Homotopy group][The $n$th homotopy group of a pointed space $A$ is defined as

$ defEq(pi_n (A), norm(Omega^n (A))_0) $] <homotopyGroup>

#property[For all $n > 1$, $pi_n (X)$ is an abelian group.]


== Exactness and exact sequences

#definition[Exactness][Given pointed types $A, B, C$ and pointed functions $isTyp(f, arro(A, B))$ and $isTyp(g, arro(B, C))$, we say $f$ and $g$ are *exact* if the #link(<image>)[image] $imOf(f)$ is equivalent to the kernel $kerOf(g)$.]

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

In the formalization, we represent this equivalence as a pair of functions, as shown below, since the conversion functions are the only parts that are important to our formalization.
It can be shown that having these two functions are sufficient for proving the entire equivalence, due to the fact that $C$ is a #link(<hLevelSet>)[set] and images are propositionally truncated.

```
im∈ker : isInIm f b → isInKer g b
ker∈im : isInKer g b → isInIm f b
```

// As a direct consequence, the composition $g compose f$ always results in the trivial map that maps everything to $0$. 
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
For example, the long exact sequence of #link(<homotopyGroup>)[homotopy groups] relates the $n$th homotopy groups derived from a pointed function $f$:

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

The *Freudenthal Suspension Theorem*, first published in @freudenthal_uber_1937, revealed that spaces exhibit a "stabilization" at higher homotopy groups past a particular threshold.
However, it's inconvenient to talk about these stable homotopy groups since they only occurred for high $k$, and we would have to carry the stabilization condition around.
It would be much easier to _define_ an object around the stable groups.

Thus, *spectra* were introduced to represent this "stable" information.
The first account of spectra comes from @lima_duality_1958 and the first formalization into homotopy type theory is due to @FvDFormalizationHigherInductive2018.
At a high level, a spectrum is a family of pointed spaces, related by structure maps, that extend in both directions infinitely.
As a result of this stabilization, the loop space functor $Omega$ and the suspension functor $Sigma$ are automatically inverses of each other.

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

  $ isTyp(sigma, arro(Sigma X_n, X_(n+1))) $
]

The indexing type is written here as $ZZ$, but in reality it can be any infinitely increasing structure.
@FvDFormalizationHigherInductive2018 uses an abstract `succ_str` to represent the indexing type.

#definition[$Omega$-spectrum][
  An *$Omega$-spectrum* $X$ is a spectrum such that the _adjoint_ of the structure maps are weak equivalences.

  $ X_n tilde.eq Omega X_(n+1) $
]

#definition[Homotopy group of a spectrum][]

== Eilenberg-MacLane space and spectra

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

Homology and cohomology are #TODO[high-level intuition for cohomology]

#TODO[cohomology cup product ring structure]

The properties of various cohomologies have been distilled into axioms, known as the Eilenberg-Steenrod axioms, due to @eilenberg_axiomatic_1945.
Furthermore, it was shown in @brown_cohomology_1962 @adams_variant_1971 that any cohomology theory that satisfies these axioms (a "generalized" cohomology theory) is representable by a spectrum.

#theorem[Representability][
#TODO[restate the theorem here]
]

@brown_cohomology_1962 additionally shows that "ordinary" singular cohomology is representable by the #link(<EMSpectrum>)[Eilenberg-MacLane spectrum].
Due to the difficulty #TODO[cite] of constructing singular cohomology directly in HoTT, we treat the Eilenberg-MacLane spectrum representation _as_ the definition of cohomology we will use for further constructions.