module prog

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

sig Noop extends Stmt {}

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
