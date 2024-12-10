module analysis

open prog as p

abstract sig LatticeElement {
  oneLe: set LatticeElement,
  leq: set LatticeElement
}

fact {
  leq = ^oneLe + LatticeElement <: iden
}
