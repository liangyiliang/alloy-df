// Definition of programs
sig Var {}

sig Program {
  stmts: seq Stmt
}

abstract sig Stmt {}

sig AssignNumber extends Stmt {
  lhs: one Var,
  rhs: one Int
}

sig AssignVar extends Stmt {
  lhs: one Var,
  rhs: one Var
}

sig AssignOp extends Stmt {
  lhs: one Var,
  op1: one Var,
  op2: one Var,
  op: one ("add" + "sub" + "mul" + "div")
}

sig Goto extends Stmt {
  target: one seq/Int
}

sig IfGoto extends Stmt {
  vv: one Var,
  op: one ("le" + "eq"),
  target: one seq/Int
}

sig Fail extends Stmt {}

// Definition of CFG

fun GotoTarget [s: Stmt] : set seq/Int {
  { t: seq/Int |
    (s in Goto implies t = s.(Goto<:target)) and
    (s in IfGoto implies t = s.(IfGoto<:target)) and
    (s not in (Goto + IfGoto) implies t = none)
  }
}

fun OutgoingEdges [p: Program, i: seq/Int]: seq/Int {
  let s = i.(p.stmts) |
  GotoTarget[s] + { t: seq/Int |
    (s in Goto implies t = none) and
    (s not in Goto implies t = add[i, 1])
  }
}

fun IncomingEdges [p: Program, i: seq/Int]: seq/Int {
  { inc: seq/Int |
    i in OutgoingEdges[p, inc]
  }
}

pred WellFormedProgram [p: Program] {
  all s : univ.(p.stmts) | GotoTarget[s] in p.stmts.inds
}

run OneWellFormedProgram {
  one p: Program | {
    WellFormedProgram [p]
    #(p.stmts) > 2
  }
} for 4 seq

run OneSimpleProgram {
  // one simple program:
  // 0: v := 1
  // 1: if v eq0 then goto 0
  some p: Program |
  some s0: AssignNumber, s1: IfGoto, v: Var | {
    p.stmts = 0 -> s0 + 1 -> s1
    s0.lhs = v
    s0.rhs = 1
    s1.vv = v
    s1.op = "eq"
    s1.target = 0
    
    WellFormedProgram[p]
  }
}

// Definition of Lattice and Ingredients of Dataflow Analysis

abstract sig LatticeElement {
  oneLe: set LatticeElement,
  leq: set LatticeElement
}

one sig Top, NoFail, CanFail, Bot extends LatticeElement {}

fact {
  oneLe = Bot -> NoFail + Bot -> CanFail + NoFail -> Top + CanFail -> Top
  leq = ^oneLe + LatticeElement <: iden
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
    some initSigma: Top |
    some r: AnalysisResult | {
      GoodResult[p, r, initSigma]
      // If we add this statement, it is no longer possible
      // some bad : r.resultBefore.elems | bad = CanFail
    }
  }
}

run SimpleAnalysisWithoutFail for 5 but exactly 1 Program, exactly 1 AnalysisResult


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
    some initSigma: Top |
    some r: AnalysisResult | {
      GoodResult[p, r, initSigma]
      r.resultBefore = 0 -> Top + 1 -> CanFail + 2 -> CanFail
    }
  }
}

run SimpleAnalysisWithFail for 5 but exactly 1 Program, exactly 1 AnalysisResult
