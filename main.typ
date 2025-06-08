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

#include "./chapters/01-type-theory.typ"

#include "./chapters/02-algebra.typ"

#include "./chapters/03-homotopy-theory.typ"

#include "./chapters/04-spectral-sequences.typ"

= Discussion

- Category theory?
- Thoughts on Agda
  - as a proof assistant
  - for learning math

