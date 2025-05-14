#import "@preview/cetz:0.3.1" as cetz: canvas, draw
#import "@preview/ctheorems:1.1.3": *

#let template(title: "", bib: "zotero.bib", content) = {
  set text(
    // font: "New Computer Modern Math",
    // font: "Helvetica Neue",
    // font: "Inter",
    font: "DM Sans",
    size: 12pt,
  )
  set page(
    "us-letter",
    margin: 1in,
    numbering: "1 of 1",
    // footer: [
    //   // #align(center, counter(page).display("1"))
    // ],
  )
  set par(
    // leading: 1em,
    // spacing: 2.4em,
    // first-line-indent: 1.8em,
    justify: true,
  )
  set heading(
    numbering: "1.1",
  )

  show: thmrules
  // show link: body => underline(text(fill: rgb("#009900"), body))
  show link: body => text(fill: rgb("#000099"), body)
  set cite(style: "citation.csl")
  show cite: set text(fill: rgb("#060")) 
  show math.frac: it => [#it.num #sym.slash #it.denom]

  // show heading: set block(above: 1.4em, below: 1em)

  align(center)[
    #heading(outlined: false, numbering: none, text(size: 2em)[#title])
  ]

  // outline(title: [Table of Contents], indent: true, depth: 3)
  // outline(title: [Table of Figures], indent: true, depth: 3, target: figure)

  // Must be after the title page
  show heading.where(level: 1, numbering: "1.1"): it => {
    // pagebreak()
    block(
      above: 1.5em,
      below: 1.0em,
      text(size: 1.5em)[#it.body]
    )
  }

  content

  pagebreak()

  heading(outlined: false, numbering: none)[References]
  bibliography(bib, title: none)
}

#let TODO(c) = [#text(fill: red)[*TODO:* #c]]
#let old(c) = [#text(fill: gray)[#c]]
#let agdaCubicalLink(s) = link("https://github.com/agda/cubical/blob/2f085f5675066c0e1708752587ae788c036ade87/" + s.split(".").join("/") + ".agda", raw(s))
#let codeLink(s) = link("https://git.mzhang.io/michael/type-theory/src/branch/master/src/ThesisWork/" + s.split(".").join("/") + ".agda", raw(s))

// ctheorems
#let theorem = thmbox("thm", "Theorem", inset: (left: 0em, right: 0em))
#let definition = thmbox("thm", "Definition", inset: (left: 0em, right: 0em))
#let property = thmbox("thm", "Property", inset: (left: 0em, right: 0em))
#let lemma = thmbox("thm", "Lemma", inset: (left: 0em, right: 0em))
#let example = thmbox("thm", "Example", inset: (left: 0em, right: 0em))
#let notation = thmbox("thm", "Notation", inset: (left: 0em, right: 0em))
#let axiom = thmbox("thm", "Axiom", inset: (left: 0em, right: 0em))
#let remark = thmbox("thm", "Remark", inset: (left: 0em, right: 0em))
#let corollary = thmbox("thm", "Corollary", inset: (left: 0em, right: 0em))
#let prf = thmproof("thm", "Proof")
// #let theorem = thmbox("theorem", "Theorem", fill: rgb("#eeffee"))
// #let corollary = thmplain(
//   "corollary",
//   "Corollary",
//   base: "theorem",
//   titlefmt: strong
// )
// #let definition = thmbox("definition", "Definition")
// #let axiom = thmplain("axiom", "Axiom")
// #let example = thmplain("example", "Example").with(numbering: none)
#let proof = thmproof("proof", "Proof")

#let point(pos, paint: black, ..args) = cetz.draw.circle(pos, radius: 0.08, fill: paint, stroke: paint, ..args)

// Notation
#let emptyType = $bot$
#let lam(x, a) = $lambda #x op(.) #a$
#let arro(..a) = $#a.pos().join($op(arrow)$)$
#let judgCtx(a) = $#a sans("ctx")$
#let isTyp(a, b) = $#a op(:) #b$
#let judgTyp(G, a, A) = $#G tack.r isTyp(#a, #A)$
#let propEqSym = $equiv$
#let propEq(..args) = $#args.pos().join(propEqSym)$
#let propEqTy(a, b, A) = $#a op(#propEqSym)_(#A) #b$
#let refl = $sans("refl")$
#let idfun = $sans("id")$
#let eqv(..args) = $#args.pos().join($tilde.eq$)$
#let defEqSym = $:equiv$
#let defEq(a, b) = $#a #defEqSym #b$
#let judgEqTyp(G, a, b, A) = $#G tack.r isTyp(#a equiv #b, #A)$
#let imSym = $sans("Im")$
#let imOf(f) = $#imSym\(#f)$
#let kerOf(f) = $sans("Ker")(#f)$
#let ind = $sans("ind")$
#let ap = $sans("ap")$
#let apd = $sans("apd")$
#let ua = $sans("ua")$
#let uaEqv = $sans("uaEqv")$
#let isEquiv = $sans("isEquiv")$
#let typ = $sans("Type")$
#let abst(n, b) = $(#n) arrow.r.double #b$
#let typ0 = $typ_0$
#let pcat(..a) = $#a.pos().join($op(dot)$)$

#let BoolVec = $sans("BoolVec")$
#let Vec = $sans("Vec")$

#let unitType = $bb(1)$
#let tt = $sans("tt")$

#let boolType = $sans("Bool")$
#let bTrue = $sans("true")$
#let bFalse = $sans("false")$
#let neg = $sans("neg")$
#let negOf(A) = $not #A$
#let seg = $sans("seg")$

#let S1 = link(<circle>)[$S^1$]
#let base = $sans("base")$
#let loop = $sans("loop")$

#let AbGroup = $sans("AbGroup")$
#let hom(a, b) = $#a arrow.r.double #b$
#let homComp(a, b) = $#a op(circle.small) #b$

#let truncBy(n, content) = $norm(#content)_#n$
#let Prop = $sans("Prop")$
#let Set = $sans("Set")$
#let pair(..a) = $angle.l #a.pos().join($,$) angle.r$
#let carrier(a) = $angle.l #a angle.r$
#let squash(a) = $|#a|$
#let propsquash(a) = $|#a|_1$

#let GradedModule = $sans("GradedModule")$
#let LeftModule = $sans("LeftModule")$
#let LeftModuleHom = $sans("LeftModuleHom")$
#let deg = $sans("deg")$