open analysis
open prog

one sig Top, Zero, NonZero, Bot extends LatticeElement {}

fact {
  oneLe = Zero -> Top + NonZero -> Top + Bot -> Zero + Bot -> NonZero
}

run ShowLattice {} for 0 but exactly 4 LatticeElement expect 1
fun Alpha [n: Int]: LatticeElement {
  { res: LatticeElement |
    zero[n] implies res = Zero
    else res = NonZero
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

fun LiftedJoin [s1: Var -> LatticeElement, s2: Var -> LatticeElement]: Var -> LatticeElement {
  { v: Var, res: LatticeElement |
    let e1 = v.s1, e2 = v.s2 | res = Join[e1, e2]
  }
}

fun FlowThroughAssignNumber [si: Var -> LatticeElement, v: Var, n: Int]: Var -> LatticeElement {
  { vv: Var, res: LatticeElement |
    vv = v implies res = Alpha[n]
    else res = vv.si
  }
}

fun FlowThroughAssignVar [si: Var -> LatticeElement, v1: Var, v2: Var]: Var -> LatticeElement {
  { vv: Var, res: LatticeElement |
    vv = v1 implies res = v2.si
    else res = vv.si
  }
}

fun FlowAdd [
  l1: LatticeElement,
  l2: LatticeElement,
]: one LatticeElement {
  { ll: LatticeElement |
    (l1 = Bot or l2 = Bot) implies ll = Bot
    else (l1 = Top or l2 = Top) implies ll = Top
    else (l1 = Zero and l2 = Zero) implies ll = Zero
    else (l1 = NonZero and l2 = NonZero) implies ll = Top
    else ll = NonZero
  }
}

fun FlowSub [
  l1: LatticeElement,
  l2: LatticeElement,
  v1: Var, v2: Var
]: one LatticeElement {
  { ll: LatticeElement |
    // special case for y = x - x
    v1 = v2 implies ll = Zero
    else (l1 = Bot or l2 = Bot) implies ll = Bot
    else (l1 = Top or l2 = Top) implies ll = Top
    else (l1 = Zero and l2 = Zero) implies ll = Zero
    else (l1 = NonZero and l2 = NonZero) implies ll = Top
    else ll = NonZero
  }
}

fun FlowMul [
  l1: LatticeElement,
  l2: LatticeElement,
]: one LatticeElement {
  { ll: LatticeElement |
    (l1 = Bot or l2 = Bot) implies ll = Bot
    else (l1 = Zero or l2 = Zero) implies ll = Zero
    else (l1 = Top or l2 = Top) implies ll = Top
    else ll = Top
  }
}

fun FlowDiv [
  l1: LatticeElement,
  l2: LatticeElement,
]: one LatticeElement {
  { ll: LatticeElement |
    (l1 = Bot or l2 = Bot) implies ll = Bot
    else (l1 = Top or l2 = Top) implies ll = Top
    else (l1 = Zero and l2 = NonZero) implies ll = Zero
    else ll = Top
  }
}

fun FlowOp [
  l1: one LatticeElement,
  l2: one LatticeElement,
  op: one ("add" + "sub" + "mul" + "div"),
  v1: one Var,
  v2: one Var ]: one LatticeElement {
  { ll: LatticeElement |
    (op = "add") implies ll = FlowAdd[l1, l2]
    else (op = "sub") implies ll = FlowSub[l1, l2, v1, v2]
    else (op = "mul") implies ll = FlowMul[l1, l2]
    else (op = "div") implies ll = FlowDiv[l1, l2]
  }
}

fun FlowThroughAssignOp [
  si: Var -> LatticeElement, 
  v1: Var, v2: Var, v3: Var, op: one ("add" + "sub" + "mul" + "div")]: Var -> one LatticeElement {
  { vv: Var, res: LatticeElement |
    vv = v1 implies res = FlowOp[v2.si, v3.si, op, v2, v3]
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

pred GoodSigma [s: Var -> LatticeElement] {
  all v: Var | one v.s
}

check FlowFunctionPreservesWellFormedness {
  all s1, s2: Var -> LatticeElement |
  all s: Stmt |
  GoodSigma[s1] and s2 = FlowThrough[s1, s] implies GoodSigma[s2] and s1.univ = s2.univ
} for 10 expect 0

pred Distributive {
  all s1, s2: Var -> LatticeElement |
  all s: Stmt |
  GoodSigma[s1] and GoodSigma[s2] implies
  let f_s1_U_s2 = FlowThrough[LiftedJoin[s1, s2], s] |
  let f_s1_U_f_s2 = LiftedJoin[FlowThrough[s1, s], FlowThrough[s2, s]] |
  f_s1_U_s2 = f_s1_U_f_s2
}

check Distributive {
  Distributive
} for 10 but exactly 3 Var, exactly 1 Stmt expect 1


pred LiftedLeq [s1, s2: Var -> LatticeElement] {
  all v: Var {
    one v.s1 and one v.s2
    v.s1 -> v.s2 in leq
  }
}

pred Monotone {
  all s1, s2: Var -> LatticeElement |
  all s: Stmt |
  GoodSigma[s1] and GoodSigma[s2] and LiftedLeq[s1, s2] implies
  LiftedLeq[FlowThrough[s1, s], FlowThrough[s2, s]]
}
check Monotone { Monotone } for 10
but exactly 10 Var, exactly 1 Stmt expect 0

sig AnalysisResult {
  resultBefore: seq/Int -> (Var -> LatticeElement),
  afterLast: Var -> LatticeElement
}

pred ValidResult [p: Program, r: AnalysisResult, entry: Var -> one LatticeElement] {
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
    LiftedLeq [FlowThrough [lastIndex.(r.resultBefore), p.stmts.last], r.afterLast]
  }
}

pred SimpleProg[p: Program, disj v0, v1, v2: Var] {
  some disj v0, v1, v2: Var |
  some st0: AssignNumber, st1: AssignNumber,
       st2: AssignOp, st3: AssignOp, st4: Goto {
    p.stmts = 0 -> st0 + 1 -> st1 + 2 -> st2 + 3 -> st3 + 4 -> st4
    st0.lhs = v0
    st0.rhs = 0
    st1.lhs = v1
    st1.rhs = 3
    st2.lhs = v2
    st2.op1 = v0
    st2.op2 = v1
    st2.op = "mul"
    st3.lhs = v1
    st3.op1 = v1
    st3.op2 = v1
    st3.op = "sub"
    st4.target = 2

    WellFormedProgram[p]
  }
}

run CheckGivenAnalysisResult {
  some p: Program, disj v0, v1, v2: Var {
    SimpleProg[p, v0, v1, v2]

    some r: AnalysisResult {
      r.resultBefore = 
        0 -> v0 -> Top + 0 -> v1 -> Top + 0 -> v2 -> Top +
        1 -> v0 -> Zero + 1 -> v1 -> Top + 1 -> v2 -> Top + 
        2 -> v0 -> Zero + 2 -> v1 -> Top + 2 -> v2 -> Top +
        3 -> v0 -> Zero + 3 -> v1 -> Top + 3 -> v2 -> Zero +
        4 -> v0 -> Zero + 4 -> v1 -> Zero + 4 -> v2 -> Zero

      r.afterLast = v0 -> Zero + v1 -> Zero + v2 -> Zero

      ValidResult[p, r, Var -> Top]
    }
  }
} for 10 but exactly 5 Stmt, exactly 3 Var, exactly 1 Program, exactly 1 AnalysisResult expect 1

run GenerateAnyResult {
  some p: Program, disj v0, v1, v2: Var {
    SimpleProg[p, v0, v1, v2]

    some r: AnalysisResult | ValidResult[p, r, Var -> Top]
  }
} for 10 but exactly 5 Stmt, exactly 3 Var, exactly 1 Program, exactly 1 AnalysisResult expect 1

run CheckPropertyOnResults {
  some p: Program, disj v0, v1, v2: Var {
    SimpleProg[p, v0, v1, v2]

    some r: AnalysisResult {
      ValidResult[p, r, Var -> Top]
      some i: seq/Int, v: Var | v.(i.(r.resultBefore)) = NonZero
    }
  }
} for 10 but exactly 5 Stmt, exactly 3 Var, exactly 1 Program, exactly 1 AnalysisResult expect 0
