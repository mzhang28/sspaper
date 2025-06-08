#import "../style.typ": *
#import "@preview/fletcher:0.5.7" as fletcher: diagram, node, edge, shapes

#show: doc => chapter(doc)

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
There are many different kinds of spectral sequences, 

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

It is convenient to represent spectral sequence data this way because it provides extra information that we can use to determine the $d$s of future pages, that the spectral sequence structure doesn't carry by itself.
To get from an exact couple to a spectral sequence, we can simply "forget" some components of our exact couple.
Note that while all exact couples give rise to a spectral sequence, not all spectral sequences are necessarily derived from an exact couple.
In this section, we will describe how to iterate an exact couple, and how to use an exact couple to construct a spectral sequence.

// TODO: Figure out where to put this sentence
// Notice that due to the graded nature of the modules, when iterating the exact couples, the degrees of our homomorphisms will slowly shift.
// This is what gives us the shifts in @spectralSequenceFigure.

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

Let's first motivate exact couples as a crucial step in the construction of our spectral sequence.
In the classical construction of the Serre spectral sequence, this structure may arise when you notice that the homology groups of filtrations of a space (for example, $n$-cells of a CW complex) fit into a pattern.

#text(size: 0.8em)[
#figure(diagram(spacing: (4mm, 6mm), {
  let h = 0
  let sub(x, s, n) = if n == 0 { $#x _#s$ } else if n > 0 { $#x _(#s + #n)$ } else { $#x _(#s - #(- n))$ }
  let isH(x, y) = (calc.floor((x - 2 * y) / 3) == h)
  let x0 = -2
  let y0 = -1
  let w = 5
  let h = 3
  for x in range(x0, x0 + w) {
    for y in range(y0, y0 + h) {
      let nIdx = - calc.floor(x / 2)
      let pIdx = nIdx + y
      let colorOf(t) = if t { black } else { gray }
 
      if calc.rem(x, 2) == 0 {
        node((x, y), text(fill: colorOf(isH(x, y)))[$sub(H, n, #nIdx) (sub(X, p, #pIdx))$])
      } else {
        node((x, y), text(fill: colorOf(isH(x, y)))[$sub(H, n, #nIdx) (sub(X, p, #pIdx), sub(X, p, #(pIdx - 1)))$])
      }

      let mkArrow(x1, y1, x2, y2) = {
        let name = if calc.rem(x1, 2) == 0 { if y1 == y2 { $j$ } else { $i$ } } else { $k$ }
        let col = colorOf(isH(x1, y1) and isH(x2, y2))
        edge((x1, y1), (x2, y2), "->", stroke: col, text(fill: col, size: 0.8em, name))
      }
      
      mkArrow(x, y, x + 1, y)
      if x == x0 { mkArrow(x - 1, y, x, y) }

      if calc.rem(x, 2) == 0 {
        mkArrow(x, y, x, y + 1)
        if y == y0 { mkArrow(x, y - 1, x, y) }
      }
    }
  }
}), caption: [Long exact sequence staircase diagram])  <lesStaircase>
]

Each highlighted staircase sequence shown in @lesStaircase is a long exact sequence of homology groups.
The even columns have the cohomology 

The insight here is that the groups in even columns have the same "shape" of $H_n (X_p)$ for some $n$ and $p$, while all the odd-columns have the same "shape" of $H_n (X_p, X_(p-1))$ for some $n$ and $p$.
Graded groups give us exactly the tools necessary to deal with morphisms in this kind of diagram. 
We can wrap the even and odd columns into a 2 different graded groups $D$ and $E$ that are each indexed by a pair $(n,p)$, and the morphisms between them are simply graded group homomorphisms with the degree shifts required by the staircase diagram above.

Taking these $E$'s along with the connecting morphism $defEq(d, j compose k)$ gives us the first page of our spectral sequence.

#text(size: 0.8em)[
#figure(diagram(spacing: 4mm, {
  let h = 0
  let sub(x, s, n) = if n == 0 { $#x _#s$ } else if n > 0 { $#x _(#s + #n)$ } else { $#x _(#s - #(- n))$ }
  let isH(x, y) = calc.rem(calc.abs(x), 2) == 1
  let x0 = -2
  let y0 = -1
  let w = 5
  let h = 3
  for x in range(x0, x0 + w) {
    for y in range(y0, y0 + h) {
      let nIdx = - calc.floor(x / 2)
      let pIdx = nIdx + y
      let colorOf(t) = if t { black } else { rgb("#ddd") }

      let debug = $#calc.floor((x - 2 * y) / 3) \ $
 
      if calc.rem(x, 2) == 0 {
        node((x, y), text(fill: colorOf(isH(x, y)))[$sub(H, n, #nIdx) (sub(X, p, #pIdx))$])
      } else {
        node((x, y), text(fill: colorOf(isH(x, y)))[$sub(H, n, #nIdx) (sub(X, p, #pIdx), sub(X, p, #(pIdx - 1)))$])
      }
      
      edge((x, y), (x + 1, y), "->", stroke: colorOf(isH(x, y) and isH(x + 1, y)))
      if x == x0 { edge((x - 1, y), (x, y), "->", stroke: colorOf(isH(x, y) and isH(x - 1, y))) }

      if calc.rem(x, 2) == 0 {
        edge((x, y), (x, y + 1), "->", stroke: colorOf(isH(x, y) and isH(x, y + 1)))
        if y == y0 { edge((x, y - 1), (x, y), "->", stroke: colorOf(isH(x, y) and isH(x, y - 1))) }
      } else {
        edge((x, y), (x + 2, y), bend: 5deg, stroke: black, "->", $d$)
        if calc.abs(x - x0) <= 1 {
        edge((x - 2, y), (x, y), bend: 5deg, stroke: black, "->", $d$)
        }
      }
    }
  }
}), caption: [First page of the spectral sequence])
]

Typically, we are only interested in page 2 on of the spectral sequence. #TODO[finish]

Note that although convenient, exact couples are not the _only_ source of spectral sequences; even the Serre spectral sequence can be constructed directly from a filtered object.

#theorem[Derived couple][
  Given an exact couple $(D, E, i, j, k)$, we can get a _derived_ exact couple $(D', E', i', j', k')$ that contains exactly the homological data required for future pages of the spectral sequence.
] <derivedCouple>
#prf[
  This process involves a proof technique called diagram chasing.
  In HoTT, we will also have the added burden of wrapping and unwrapping all of our data properly through truncations and quotients.

  First, we have $defEq(D', imOf(i))$.

  Before we define , define $defEq(d, j compose k)$. Notice that this goes around the triangle in a strange way, not following the arrows.
]

== Convergence



== Atiyah-Hirzebruch Spectral Sequence


== Serre Spectral Sequence