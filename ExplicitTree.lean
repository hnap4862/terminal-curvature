import Std

/-! Direct tree computation for a mixed sign witness. The input uses physical trees
built by joining roots. The state stores four leading coefficients and their degree.
Only kernel reduction is used for the concrete certificate. -/
namespace ExplicitTree

inductive Tree where
  | point
  | join (left right : Tree)

/-- Join roots with an edge and keep the root of the left argument. -/
def attach (base child : Tree) : Nat → Tree
  | 0 => base
  | n+1 => .join (attach base child n) child

def edge := Tree.join .point .point

def branch (outgoing incoming : Nat) : Tree :=
  .join (attach .point edge outgoing) (attach .point edge incoming)

def star (s B f p : Nat) : Tree :=
  attach (.join .point (attach .point edge (p*f))) (branch (p*B) (2*p*B)) s

/-- Word +−, f = [0,2,6,9], B=9, scale 2, all roots attached to the common plus endpoint. -/
def witness : Tree := .join (.join (.join edge (star 1 9 2 2)) (star 2 9 6 2)) (star 3 9 9 2)

def vertices : Tree → Nat
| .point => 1
| .join a b => vertices a + vertices b

structure Top where
  degree : Nat
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  deriving DecidableEq

def one : Top := ⟨0,1,0,0,0⟩
def singleVertex : Top := ⟨1,1,0,0,0⟩

def addSmaller (x y : Top) : Top :=
  match x.degree-y.degree with
  | 0 => ⟨x.degree,x.a+y.a,x.b+y.b,x.c+y.c,x.d+y.d⟩
  | 1 => ⟨x.degree,x.a,x.b+y.a,x.c+y.b,x.d+y.c⟩
  | 2 => ⟨x.degree,x.a,x.b,x.c+y.a,x.d+y.b⟩
  | 3 => ⟨x.degree,x.a,x.b,x.c,x.d+y.a⟩
  | _ => x

def plus (x y : Top) := if y.degree ≤ x.degree then addSmaller x y else addSmaller y x

def times (x y : Top) : Top :=
  ⟨x.degree+y.degree, x.a*y.a, x.a*y.b+x.b*y.a,
   x.a*y.c+x.b*y.b+x.c*y.a, x.a*y.d+x.b*y.c+x.c*y.b+x.d*y.a⟩

/-- First component excludes the root, second includes it. -/
def conditioned : Tree → Top × Top
| .point => (one,singleVertex)
| .join a b =>
  let (a₀,a₁) := conditioned a
  let (b₀,b₁) := conditioned b
  (times a₀ (plus b₀ b₁),times a₁ b₀)

def tail (T : Tree) := let (a,b) := conditioned T; plus a b

set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

theorem mixed_witness : vertices witness = 736 ∧ (tail witness).degree = 368 ∧
    (tail witness).b*(tail witness).b < (tail witness).a*(tail witness).c ∧
    (tail witness).b*(tail witness).d < (tail witness).c*(tail witness).c := by decide

#print axioms mixed_witness
end ExplicitTree
