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

run {} for 3 but exactly 16 Val

fun Alpha [n: Int]: Val {
  { vv: Val |
    vv.v = n
  }
}

fun Join [s1, s2: LatticeElement]: LatticeElement {
  { res: LatticeElement |
    s1 = s2 implies res = s1
    else s1 = Bot implies res = s2
    else s2 = Bot implies res = s1
    else res = Top
  }
}

fun LiftedJoin [s1: Var -> one LatticeElement, s2: Var -> one LatticeElement]: Var -> one LatticeElement {
  { v: Var, res: LatticeElement |
    let e1 = v.s1, e2 = v.s2 | res = Join[e1, e2]
  }
}

fun FlowThroughAssignNumber [si: Var -> one LatticeElement, v: Var, n: Int]: Var -> one LatticeElement {
  { vv: Var, res: LatticeElement |
    vv = v implies res = Alpha[n]
    else res = vv.si
  }
}

fun FlowThroughAssignVar [si: Var -> one LatticeElement, v1: Var, v2: Var]: Var -> one LatticeElement {
  { vv: Var, res: LatticeElement |
    vv = v1 implies res = v2.si
    else res = vv.si
  }
}

fun FlowOpVal [l1: one Val, l2: one Val, op: one ("add" + "sub" + "mul" + "div")]: one Val {
  { vv: Val |
    op = "add" implies vv.v = add[l1.v, l2.v]
    else op = "sub" implies vv.v = sub[l1.v, l2.v]
    else op = "mul" implies vv.v = mul[l1.v, l2.v]
    else vv.v = div[l1.v, l2.v]
  }
}

fun FlowOp [l1: one LatticeElement, l2: one LatticeElement, op: one ("add" + "sub" + "mul" + "div")]: one LatticeElement {
  { ll: LatticeElement |
    (l1 = Bot or l2 = Bot) implies ll = Bot
    else (l1 = Top or l2 = Top) implies ll = Top
    else ll = FlowOpVal[l1, l2, op]
  }
}

fun FlowThroughAssignOp [
  si: Var -> one LatticeElement, 
  v1: Var, v2: Var, v3: Var, op: one ("add" + "sub" + "mul" + "div")
]: Var -> one LatticeElement {
  { vv: Var, res: LatticeElement |
    vv = v1 implies res = FlowOp [v2.si, v3.si, op]
    else res = vv.si
  }
}

fun FlowThrough [si: Var -> one LatticeElement, s: Stmt]: Var -> one LatticeElement {
  { v: Var, res: LatticeElement |
    s in AssignNumber implies (v -> res) in FlowThroughAssignNumber [si, s.(AssignNumber<:lhs), s.(AssignNumber<:rhs)]
    else s in AssignVar implies (v -> res) in FlowThroughAssignVar [si, s.(AssignVar<:lhs), s.(AssignVar<:rhs)]
    else s in AssignOp implies (v -> res) in FlowThroughAssignOp [si, s.(AssignOp<:lhs), s.(AssignOp<:op1), s.(AssignOp<:op2), s.(AssignOp<:op)]
    else (v -> res) in si
  }
}

check FlowFunctionPreservesVars {
  all s1, s2: Var -> one LatticeElement |
  all s: Stmt |
  s2 = FlowThrough[s1, s] implies s1.univ = s2.univ
} for 10 but exactly 16 Val expect 0

pred GoodSigma [s: Var -> one LatticeElement] {
  all v: Var | some v.s
}

pred Distributive {
  all s1, s2: Var -> one LatticeElement |
  all s: Stmt |
  GoodSigma[s1] and GoodSigma[s2] implies
  let f_s1_U_s2 = FlowThrough[LiftedJoin[s1, s2], s] |
  let f_s1_U_f_s2 = LiftedJoin[FlowThrough[s1, s], FlowThrough[s2, s]] |
  f_s1_U_s2 = f_s1_U_f_s2
}

check Distributive {
  Distributive
} for 10 but exactly 3 Var, exactly 16 Val expect 1

sig AnalysisResult {
  resultBefore: seq/Int -> (Var -> LatticeElement),
  afterLast: Var -> LatticeElement
}

pred LiftedLeq [s1, s2: Var -> one LatticeElement] {
  all v: Var {
    one v.s1 and one v.s2
    v.s1 -> v.s2 in leq
  }
}

pred GoodResult [p: Program, r: AnalysisResult, entry: Var -> one LatticeElement] {
  one r
  one p

  #r.resultBefore.univ.univ = #p.stmts

  LiftedLeq[entry, 0.(r.resultBefore)]

  all i: p.stmts.inds {
  let rBeforeThis = i.(r.resultBefore) {
  all incomingIndex: IncomingEdges[p, i] {
  let rBeforeIncoming = incomingIndex.(r.resultBefore) {
  let sigmaAfterFlow = FlowThrough [rBeforeIncoming, incomingIndex.(p.stmts)] {
    LiftedLeq [sigmaAfterFlow, rBeforeThis]
  }}}}}

  let lastIndex = sub[#(r.resultBefore.univ.univ), 1] {
    r.afterLast = FlowThrough [lastIndex.(r.resultBefore), p.stmts.last]
  }
}


run TestProgram {
  some p: Program | {
  some disj v0, v1, v2: Var |
  some st0: AssignNumber, st1: AssignNumber, st2: AssignOp, st3: AssignVar {
    // Program looks like:
    // v0 = 2
    // v1 = 3
    // v2 = v0 + v1
    // v2 = v1
    p.stmts = 0 -> st0 + 1 -> st1 + 2 -> st2 + 3 -> st3
    st0.lhs = v0
    st0.rhs = 2
    st1.lhs = v1
    st1.rhs = 3
    st2.lhs = v2
    st2.op1 = v0
    st2.op2 = v1
    st2.op = "add"
    st3.lhs = v2
    st3.rhs = v1

    WellFormedProgram[p]

	some r: AnalysisResult, vv2: Val, vv3: Val, vv5: Val {
      vv2.v=2 and vv3.v=3 and vv5.v=5
      
      r.resultBefore = 0 -> v0 -> Top + 0 -> v1 -> Top + 0 -> v2 -> Top +
        1 -> v0 -> vv2 + 1 -> v1 -> Top + 1 -> v2 -> Top +
        2 -> v0 -> vv2 + 2 -> v1 -> vv3 + 2 -> v2 -> Top +
        3 -> v0 -> vv2 + 3 -> v1 -> vv3 + 3 -> v2 -> vv5
      r.afterLast = v0 -> vv2 + v1 -> vv3 + v2 -> vv3

      GoodResult[p, r, (v0 + v1 + v2) -> Top]
    }

  }}

} for 10 but exactly 4 Stmt, exactly 3 Var, exactly 1 Program, exactly 16 Val, exactly 1 AnalysisResult expect 1
