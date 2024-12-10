open analysis
open prog

one sig Top, Bot extends LatticeElement {}
sig Val extends LatticeElement {
  v: Int
}

fact {
  oneLe = Val -> Top + Bot -> Val

  all i: Int | one vv: Val | vv.v = i
}

sig AnalysisResult {
  resultBefore: seq (Var -> one LatticeElement),
  afterLast: Var -> one LatticeElement
}

run {} for 10 but exactly 16 Val, exactly 1 AnalysisResult
