import Word
import Counting
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Equivalence of actual legal core assignments and the exact-budget relation `Run`. -/
namespace TerminalCurvature
namespace Assembly
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

structure Model where
  V : Type
  finite : Fintype V
  edge : V → V → Prop
  incomingFromSource : V → Bool
  wt : V → Nat × Nat
attribute [instance] Model.finite

/-- Contribution is outgoing, incoming, or both, according to the mark. -/
def payoff (w : Nat × Nat) : Mark → Nat
| .pos => w.2 | .neg => w.1 | .hole => w.1+w.2

def indicator (m k : Mark) := if m=k then 1 else 0

def number {I : Type} [Fintype I] (a : I → Mark) (k : Mark) : Nat := ∑ i, indicator (a i) k

def total {I : Type} [Fintype I] (w : I → Nat × Nat) (a : I → Mark) : Nat := ∑ i, payoff (w i) (a i)

def Realises (g : Model) (r e : Nat) : Prop := ∃ a : g.V → Mark,
  Legal g.edge a ∧ number a .hole=r ∧ total g.wt a=e

def empty : Model where
  V := Empty
  finite := inferInstance
  edge := fun _ _ => False
  incomingFromSource := Empty.elim
  wt := Empty.elim

def union (g h : Model) : Model where
  V := g.V ⊕ h.V
  finite := inferInstance
  edge := fun x y => match x,y with
    | .inl a,.inl b => g.edge a b | .inr a,.inr b => h.edge a b | _,_ => False
  incomingFromSource := Sum.elim g.incomingFromSource h.incomingFromSource
  wt := Sum.elim g.wt h.wt

def single (w : Nat) : Model where
  V := Unit
  finite := inferInstance
  edge := fun _ _ => False
  incomingFromSource := fun _ => true
  wt := fun _ => (w,w)

def star (s B b : Nat) : Model where
  V := Unit ⊕ Fin s
  finite := inferInstance
  edge := fun x y => match x,y with | .inr _,.inl _ => True | _,_ => False
  incomingFromSource := Sum.elim (fun _ => true) (fun _ => false)
  wt := Sum.elim (fun _ => (b,0)) (fun _ => (B,2*B))

def stars (B : Nat) (f : Nat → Nat) : List Nat → Model
| [] => empty
| s::ss => union (star s B (f s)) (stars B f ss)

def model : Device → Model
| .stars h B f => stars B f (List.range' 1 h)
| .balanced w c => union (single w) (model c)

private theorem union_legal {g h : Model} (a : (union g h).V → Mark) :
    Legal (union g h).edge a ↔ Legal g.edge (a ∘ Sum.inl) ∧ Legal h.edge (a ∘ Sum.inr) := by
  constructor
  · intro hh; exact ⟨fun i j e => hh (.inl i) (.inl j) e,fun i j e => hh (.inr i) (.inr j) e⟩
  · rintro ⟨hl,hr⟩ i j e
    cases i <;> cases j
    · exact hl _ _ e
    · contradiction
    · contradiction
    · exact hr _ _ e

private theorem union_number {g h : Model} (a : (union g h).V → Mark) (k : Mark) :
    number a k = number (a ∘ Sum.inl) k + number (a ∘ Sum.inr) k :=
  Fintype.sum_sum_type _

private theorem union_total {g h : Model} (a : (union g h).V → Mark) :
    total (union g h).wt a = total g.wt (a ∘ Sum.inl) + total h.wt (a ∘ Sum.inr) :=
  Fintype.sum_sum_type _

private theorem union_realises (g h : Model) (r e : Nat) : Realises (union g h) r e ↔
    ∃ a b u v, Realises g a u ∧ Realises h b v ∧ r=a+b ∧ e=u+v := by
  constructor
  · rintro ⟨x,hx,hz,he⟩; obtain ⟨hl,hr⟩ := (union_legal x).mp hx
    exact ⟨_,_,_,_,⟨_,hl,rfl,rfl⟩,⟨_,hr,rfl,rfl⟩,hz.symm.trans (union_number x .hole),he.symm.trans (union_total x)⟩
  · rintro ⟨a,b,u,v,⟨x,hx,rx,ex⟩,⟨y,hy,ry,ey⟩,rfl,rfl⟩
    refine ⟨Sum.elim x y,(union_legal _).mpr ⟨hx,hy⟩,?_,?_⟩
    · exact (union_number (g:=g) (h:=h) (Sum.elim x y) _).trans (congrArg₂ (·+·) rx ry)
    · exact (union_total (g:=g) (h:=h) (Sum.elim x y)).trans (congrArg₂ (·+·) ex ey)

private theorem empty_realises (r e : Nat) : Realises empty r e ↔ r=0 ∧ e=0 := by
  constructor
  · rintro ⟨x,_,hr,he⟩
    change (∑ i : Empty, indicator (x i) .hole) = r at hr
    change (∑ i : Empty, payoff _ (x i)) = e at he
    simp at hr he; omega
  · rintro ⟨rfl,rfl⟩
    exact ⟨Empty.elim,fun i => Empty.elim i,by change (∑ _ : Empty, _) = 0; simp,
      by change (∑ _ : Empty, _) = 0; simp⟩

private theorem single_realises (w r e : Nat) : Realises (single w) r e ↔
    (r=0 ∧ e=w) ∨ (r=1 ∧ e=2*w) := by
  constructor
  · rintro ⟨a,_,hr,he⟩
    change (∑ i : Unit, indicator (a i) .hole) = r at hr
    change (∑ i : Unit, payoff (w,w) (a i)) = e at he
    cases hm : a () <;> simp [hm,indicator,payoff] at hr he <;> omega
  · rintro (⟨hr,he⟩|⟨hr,he⟩) <;> subst r <;> subst e
    · exact ⟨fun _ => .pos,fun _ _ h => False.elim h,by change (∑ _ : Unit, _) = 0; simp [indicator],
        by change (∑ _ : Unit, _) = w; simp [payoff,single]⟩
    · exact ⟨fun _ => .hole,fun _ _ h => False.elim h,by change (∑ _ : Unit, _) = 1; simp [indicator],
        by change (∑ _ : Unit, _) = 2*w; simp [payoff,single]; omega⟩

private theorem counts_add {s : Nat} (a : Fin s → Mark) :
    number a .pos+number a .neg+number a .hole=s := by
  have h (i : Fin s) : indicator (a i) .pos+indicator (a i) .neg+indicator (a i) .hole=1 := by
    cases a i <;> decide
  simp only [number, ←Finset.sum_add_distrib, h]; simp

private theorem arm_score {s : Nat} (B : Nat) (a : Fin s → Mark) :
    (∑ i, payoff (B,2*B) (a i))=2*B*number a .pos+B*number a .neg+3*B*number a .hole := by
  simp only [number,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i hi; cases a i <;> simp [payoff,indicator] <;> omega

private theorem star_legal (s B b : Nat) (a : (star s B b).V → Mark) : Legal (star s B b).edge a ↔
    (a (.inl ())=.neg → ∀ i, a (.inr i) ≠ .pos) := by
  constructor
  · intro hh hm i hp; exact hh (.inr i) (.inl ()) trivial hp hm
  · intro hh i j e hp hn; cases i <;> cases j <;> try contradiction
    exact hh hn _ hp

/-- Arbitrary legal counts are realised on the labelled branches. -/
private theorem realise_counts {s : Nat} (x : StarState) (hv : Valid s x) :
    ∃ a : Fin s → Mark, number a .pos=x.plusCount ∧ number a .neg=x.minusCount ∧
      number a .hole=x.holes ∧ (x.mark=.neg → ∀ i, a i ≠ .pos) := by
  classical
  let I := Fin x.plusCount ⊕ (Fin x.minusCount ⊕ Fin x.holes)
  let g : I → Mark := Sum.elim (fun _ => .pos) (Sum.elim (fun _ => .neg) (fun _ => .hole))
  have eqc : Fintype.card (Fin s) = Fintype.card I := by
    simp [I]; have hh := hv.1; omega
  let e : Fin s ≃ I := Fintype.equivOfCardEq eqc
  have ct (k : Mark) : number (g ∘ e) k =
      x.plusCount*indicator .pos k + (x.minusCount*indicator .neg k + x.holes*indicator .hole k) := by
    change (∑ i, indicator (g (e i)) k) = _
    rw [e.sum_comp (fun j => indicator (g j) k)]
    simp [I,g,Fintype.sum_sum_type]
  refine ⟨g ∘ e, by simpa [indicator] using ct .pos, by simpa [indicator] using ct .neg,
    by simpa [indicator] using ct .hole,?_⟩
  intro hm i
  have hp := hv.2 hm
  change g (e i) ≠ .pos
  rcases e i with k|k
  · have h := k.isLt; omega
  · cases k <;> simp [g]

private theorem star_statistics (s B b : Nat) (a : (star s B b).V → Mark) :
    number a .hole = indicator (a (.inl ())) .hole+number (a ∘ Sum.inr) .hole ∧
    total (star s B b).wt a = payoff (b,0) (a (.inl ()))+
      (2*B*number (a ∘ Sum.inr) .pos+B*number (a ∘ Sum.inr) .neg+3*B*number (a ∘ Sum.inr) .hole) := by
  constructor
  · change (∑ i : Unit ⊕ Fin s, indicator (a i) .hole) = _
    rw [Fintype.sum_sum_type]; simp [number]
  · change (∑ i : Unit ⊕ Fin s, payoff ((star s B b).wt i) (a i)) = _
    rw [Fintype.sum_sum_type]; simp only [Fintype.sum_unique];
    exact congrArg (payoff (b,0) (a (.inl ()))+·) (arm_score B (a ∘ Sum.inr))

theorem star_realises (s B b r e : Nat) : Realises (star s B b) r e ↔
    ∃ x : StarState, Valid s x ∧ cost x=r ∧ score B b x=e := by
  constructor
  · rintro ⟨a,hleg,hr,he⟩
    let arm : Fin s → Mark := a ∘ Sum.inr
    let m := a (.inl ())
    have hstats := star_statistics s B b a
    have val : m=.neg → number arm .pos=0 := by
      intro hm
      have hl := (star_legal s B b a).mp hleg hm
      exact Finset.sum_eq_zero (fun i _ => by simp [arm,indicator,hl i])
    refine ⟨⟨m,number arm .pos,number arm .neg,number arm .hole⟩,⟨counts_add arm,val⟩,?_,?_⟩
    · have hh := hstats.1.symm.trans hr
      change indicator m .hole + number arm .hole = r at hh
      cases hm : m <;> simp [hm,indicator,cost] at hh ⊢ <;> omega
    · have hh := hstats.2.symm.trans he
      change payoff (b,0) m + (2*B*number arm .pos+B*number arm .neg+3*B*number arm .hole) = e at hh
      cases hm : m <;> simp [hm,score,payoff] at hh ⊢ <;> omega
  · rintro ⟨x,hv,rfl,rfl⟩
    obtain ⟨arm,hp,hn,hz,hlegal⟩ := realise_counts x hv
    let a : (star s B b).V → Mark := Sum.elim (fun _ => x.mark) arm
    have st := star_statistics s B b a
    refine ⟨a,(star_legal s B b a).mpr hlegal,?_,?_⟩
    · rw [st.1]; change indicator x.mark .hole + number arm .hole = _
      rw [hz]; cases hm : x.mark <;> simp [cost,indicator,hm,Nat.add_comm]
    · rw [st.2]; change payoff (b,0) x.mark + (2*B*number arm .pos+B*number arm .neg+3*B*number arm .hole) = _
      rw [hp,hn,hz]; cases hm : x.mark <;> simp [score,payoff,hm] <;> omega

theorem stars_realises (B : Nat) (f : Nat → Nat) (ss : List Nat) (r e : Nat) :
    Realises (stars B f ss) r e ↔ Atlas B f ss r e := by
  induction ss generalizing r e with
  | nil =>
    rw [stars,empty_realises]; constructor
    · rintro ⟨rfl,rfl⟩; exact Atlas.empty
    · intro st; cases st; simp
  | cons s ss ih =>
    rw [stars,union_realises]; constructor
    · rintro ⟨a,k,u,v,hx,hh,rfl,rfl⟩
      obtain ⟨x,hv,rfl,rfl⟩ := (star_realises _ _ _ _ _).mp hx
      exact Atlas.cons x hv ((ih _ _).mp hh)
    · intro st; cases st with
      | cons x hv rest => exact ⟨_,_,_,_,(star_realises _ _ _ _ _).mpr ⟨x,hv,rfl,rfl⟩,(ih _ _).mpr rest,rfl,rfl⟩

theorem device_realises (c : Device) (r e : Nat) : Realises (model c) r e ↔ Run c r e := by
  induction c generalizing r e with
  | stars h B f =>
    rw [model,stars_realises]; constructor
    · exact Run.stars
    · intro st; cases st with | stars hh => exact hh
  | balanced w c ih =>
    rw [model,union_realises]; constructor
    · rintro ⟨a,k,u,v,hx,hh,rfl,rfl⟩
      rcases (single_realises _ _ _).mp hx with ⟨ha,hu⟩|⟨ha,hu⟩ <;> subst a <;> subst u
      · simpa using Run.keep w ((ih _ _).mp hh)
      · simpa [Nat.add_comm] using Run.drop w ((ih _ _).mp hh)
    · intro st; cases st with
      | keep w rest => exact ⟨0,_,w,_,(single_realises _ _ _).mpr (Or.inl ⟨rfl,rfl⟩),(ih _ _).mpr rest,by omega,rfl⟩
      | drop w rest => exact ⟨1,_,2*w,_,(single_realises _ _ _).mpr (Or.inr ⟨rfl,rfl⟩),(ih _ _).mpr rest,by omega,rfl⟩

end
end Assembly
end TerminalCurvature
