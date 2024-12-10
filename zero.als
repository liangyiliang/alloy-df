open analysis
open prog

one sig Top, Zero, NonZero, Bot extends LatticeElement {}

fact {
  oneLe = Zero -> Top + NonZero -> Top + Bot -> Zero + Bot -> NonZero
}

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

fun FlowThroughAssignOp [
  si: Var -> one LatticeElement, 
  v1: Var, v2: Var, v3: Var, op: one ("add" + "sub" + "mul" + "div")]: Var -> one LatticeElement {
  { vv: Var, res: LatticeElement |
    // for now
    vv = v1 implies res = Top
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

pred Distributive {
  all s1, s2: Var -> one LatticeElement |
  all s: Stmt |
  let f_s1_U_s2 = FlowThrough[LiftedJoin[s1, s2], s] |
  let f_s1_U_f_s2 = LiftedJoin[FlowThrough[s1, s], FlowThrough[s2, s]] |
  f_s1_U_s2 = f_s1_U_f_s2
}

check Distributive {
  Distributive
} for 10
