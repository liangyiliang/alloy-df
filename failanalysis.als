open analysis
open prog

one sig Top, NoFail, CanFail, Bot extends LatticeElement {}

fact {
  oneLe = Bot -> NoFail + Bot -> CanFail + NoFail -> Top + CanFail -> Top
}

fun Join [s1, s2: LatticeElement]: LatticeElement {
  { res: LatticeElement |
    s1 = s2 implies res = s1
    else s1 = Bot implies res = s2
    else s2 = Bot implies res = s1
    else res = Top
  }
}

fun FlowThrough [si: LatticeElement, s: Stmt] : LatticeElement {
  { newSigma: LatticeElement |
    s in Fail implies newSigma = CanFail else newSigma = si
  }
}

// Distributivity

pred Distributive {
  all s1, s2: LatticeElement |
  all s: Stmt |
  let f_s1_U_s2 = FlowThrough[Join[s1, s2], s] |
  let f_s1_U_f_s2 = Join[FlowThrough[s1, s], FlowThrough[s2, s]] |
  f_s1_U_s2 = f_s1_U_f_s2
}

check Distributive {
  Distributive
} for 20

// Dataflow Analysis

sig AnalysisResult {
  resultBefore: seq LatticeElement,
  afterLast: one LatticeElement
}

pred GoodResult [p: Program, r: AnalysisResult, entry: LatticeElement] {
  one entry
  one r
  one p

  #r.resultBefore = #p.stmts

  entry -> (0.(r.resultBefore)) in leq

  all i: p.stmts.inds {
  let rBeforeThis = i.(r.resultBefore) {
  all incomingIndex: IncomingEdges[p, i] {
  let rBeforeIncoming = incomingIndex.(r.resultBefore) {
  let sigmaAfterFlow = FlowThrough [rBeforeIncoming, incomingIndex.(p.stmts)] {
    sigmaAfterFlow -> rBeforeThis in leq
  }}}}}

  r.afterLast = FlowThrough [r.resultBefore.last, p.stmts.last]
}

// Running an analysis

pred SimpleAnalysisWithoutFail {
  // Program looks like:
  // 0: Goto 1
  // 1: Goto 2
  // 2: If <something> Then Goto 0
  some p: Program {
    some st0: Goto, st1: Goto, st2: IfGoto | {
      p.stmts = 0 -> st0 + 1 -> st1 + 2 -> st2
      st0.target = 1
      st1.target = 2
      st2.target = 0
    }
    WellFormedProgram[p]
    some initSigma: NoFail |
    some r: AnalysisResult | {
      GoodResult[p, r, initSigma]
      // Not Possible
      some bad : r.resultBefore.elems | bad = CanFail
    }
  }
}

run SimpleAnalysisWithoutFail for 10 but exactly 1 Program, exactly 1 AnalysisResult


pred SimpleAnalysisWithFail {
  // Program looks like:
  // 0: Fail
  // 1: Goto 2
  // 2: If <something> Then Goto 1
  some p: Program {
    some st0: Fail, st1: Goto, st2: IfGoto | {
      p.stmts = 0 -> st0 + 1 -> st1 + 2 -> st2
      st1.target = 2
      st2.target = 1
    }
    WellFormedProgram[p]
    some initSigma: NoFail |
    some r: AnalysisResult | {
      GoodResult[p, r, initSigma]
      // Possible
      // r.resultBefore = 0 -> NoFail + 1 -> CanFail + 2 -> CanFail

      // Not Possible
      r.resultBefore = 0 -> NoFail + 1 -> NoFail + 2 -> CanFail
    }
  }
}

run SimpleAnalysisWithFail for 10 but exactly 1 Program, exactly 1 AnalysisResult
