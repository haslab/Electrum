module examples/systems/javatypes

/*
 * Model of the Java type system. The TypeSoundness assertion
 * claims that if a Java program type checks successfully,
 * then a field will cannot be assigned an incorrect type.
 *
 * author: Daniel Jackson
 */

open util/graph[Type] as graph

abstract sig Type {
  xtends: set Type
  }
sig Interface extends Type {}
  { xtends in Interface }
sig Class extends Type {
  implements: set Interface,
  fields: set Field
  } { lone xtends && xtends in Class }
-- optional: best omitted to allow private etc
-- {xtends.@fields in fields}
sig Field {
  declType: Type
  }

fact {
  graph/dag[xtends]
  }

abstract sig Value {}
one sig Null extends Value {}
sig Object extends Value {
  type: Class,
  slot: Field lone -> lone Slot
  } {slot.Slot = type.fields}
sig Slot {}

abstract sig Statement {}
sig Assignment extends Statement {
  vari: Variable,
  expr: Expr
  }
sig Setter extends Statement {
  field: Field,
  lexpr, rexpr: Expr
  }

abstract sig Expr {
  type: Type,
  subexprs: set Expr
  } {subexprs = this + this.^@expr}
sig Variable extends Expr {
  declType: Type
  } {type = declType}
sig Constructor extends Expr {
  class: Class
  }
sig Getter extends Expr {
  field: Field,
  expr: Expr
  } {type = field.declType}

sig State {
  objects: set Object,
  reaches: Object -> Object,
  varis: set Variable,
  holds: (Slot + Variable) -> lone Value,
  val: Expr -> lone Value
  } {
  all o: Object | o.reaches = holds[o.slot[Field]] & Object
  holds.Value & Variable = varis
  objects = holds[varis].^reaches
  all e: Expr | let v = val[e] {
    e in Variable => v = holds[e]
    e in Getter => v = holds[(val[e.expr]).slot[e.field]]
    e in Constructor => v in Object and v.type = e.type }
  }

pred RuntimeTypesOK [s: State] {
  all o: s.objects, f: o.type.fields |
    let v = s.holds [o.slot [f]] | HasType [v, f.declType]
  all vari: s.varis |
    let v = s.holds [vari] | HasType [v, vari.declType]
  }

pred HasType [v: Value, t: Type] {
  v in Null or Subtype [v.type, t]
  }

pred Subtype [t, t1: Type] {
  t in Class =>
     (let supers = (t & Class).*(Class<:xtends) |
        t1 in (supers + supers.implements.*(Interface<:xtends)))
  t in Interface => t1 in (t & Interface).*(Interface<:xtends)
  }

pred TypeChecksSetter [stmt: Setter] {
  all g: Getter & stmt.(lexpr+rexpr).subexprs | g.field in g.expr.type.fields
  stmt.field in stmt.lexpr.type.fields
  Subtype [stmt.rexpr.type, stmt.field.declType]
  }

pred ExecuteSetter [s, s1: State, stmt: Setter] {
  stmt.(rexpr+lexpr).subexprs & Variable in s.varis
  s1.objects = s.objects and s1.varis = s.varis
  let rval = s.val [stmt.rexpr], lval = s.val [stmt.lexpr] {
    no lval & Null
    s1.holds = s.holds ++ (lval.slot[stmt.field] -> rval)
   }
  }

assert TypeSoundness {
  all s, s1: State, stmt: Setter |
    {RuntimeTypesOK[s]
    ExecuteSetter [s, s1, stmt]
    TypeChecksSetter[stmt]
    } => RuntimeTypesOK[s1]
  }

fact {all o, o1: Object | some o.slot[Field] & o1.slot[Field] => o = o1}
fact {all g: Getter | no g & g.^subexprs}

fact ScopeFact {
  #Assignment =< 1
  #Class =< 5
  #Interface =< 5
}

check TypeSoundness for 3 expect 0

check TypeSoundness for 2 State, 1 Assignment,
1 Statement, 5 Interface, 5 Class, 1 Null,
7 Object, 12 Expr, 3 Field, 3 Slot expect 0

// very slow
// check TypeSoundness for 2 State, 1 Statement,
// 10 Type, 8 Value, 12 Expr,
// 3 Field, 3 Slot expect 0
