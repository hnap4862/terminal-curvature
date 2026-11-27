import Assembly

/-! Turn a word into genuine cardinalities of independent vertex sets of an
explicit, split, leaf-decorated star forest joined at a common source. -/
namespace TerminalCurvature
namespace Family
noncomputable section
open Finset Assembly Counting
attribute [local instance] Classical.propDecidable
set_option linter.unnecessarySeqFocus false

def root (g : Model) : Model where
  V := Unit ⊕ g.V
  finite := inferInstance
  edge := fun i j => match i,j with
    | .inl _,.inr v => g.incomingFromSource v=true
    | .inr v,.inr w => g.edge v w
    | _,_ => False
  incomingFromSource := fun _ => false
  wt := Sum.elim (fun _ => (0,0)) g.wt

abbrev Leaves (g : Model) (p : Nat) := (v : g.V) × (Fin (p*(g.wt v).1) ⊕ Fin (p*(g.wt v).2))

def parent {g : Model} {p : Nat} (l : Leaves g p) : g.V := l.1
def out {g : Model} {p : Nat} (l : Leaves g p) : Bool :=
  Sum.elim (fun _ => true) (fun _ => false) l.2

abbrev Labels (c : Device) (p : Nat) :=
  (root (model c)).V ⊕ Leaves (root (model c)) p

def arrows (c : Device) (p : Nat) : Labels c p → Labels c p → Prop :=
  Attach (root (model c)).edge (@parent _ p) (@out _ p)

def coeff (c : Device) (p r : Nat) : Nat :=
  Fintype.card (PhysicalLayer (arrows c p) r)

def weight (g : Model) : Nat := ∑ v, ((g.wt v).1+(g.wt v).2)

theorem label_card (c : Device) (p : Nat) :
    Fintype.card (Labels c p) = Fintype.card (root (model c)).V + p*weight (root (model c)) := by
  simp only [Labels,Leaves,Fintype.card_sum,Fintype.card_sigma,Fintype.card_fin,weight,Finset.mul_sum,Nat.mul_add]

theorem free_card (g : Model) (p : Nat) (a : g.V → Mark) :
    (freeSet (@parent g p) (@out g p) a).card = p*total g.wt a := by
  classical
  simp only [freeSet,Finset.card_filter,Leaves,Fintype.sum_sigma,Fintype.sum_sum_type,total,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro v _
  cases hm : a v <;> simp [parent,out,hm,isFree,payoff,Nat.mul_add]

theorem hole_number {I : Type} [Fintype I] (a : I → Mark) : (holes a).card=number a .hole := by
  simp only [holes,Finset.card_filter,number,indicator]

theorem root_number (g : Model) (a : (root g).V → Mark) :
    number a .hole=indicator (a (.inl ())) .hole + number (a ∘ Sum.inr) .hole := by
  unfold number
  change (∑ i : Unit ⊕ g.V, _) = _
  rw [Fintype.sum_sum_type]; simp

theorem root_total (g : Model) (a : (root g).V → Mark) :
    total (root g).wt a=total g.wt (a ∘ Sum.inr) := by
  unfold total; change (∑ i : Unit ⊕ g.V, _) = _
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_unique]
  have hz : payoff ((root g).wt (.inl ())) (a (.inl ()))=0 := by cases a (.inl ()) <;> rfl
  rw [hz,Nat.zero_add]; rfl

private theorem root_lower {g : Model} {r e : Nat} (h : Realises g r e) : Realises (root g) r e := by
  obtain ⟨a,ha,hr,he⟩ := h
  let b : (root g).V → Mark := Sum.elim (fun _ => .neg) a
  refine ⟨b,?_,?_,?_⟩
  · intro i j ar hp hn; cases i with
    | inl u => contradiction
    | inr u => cases j with
      | inl v => contradiction
      | inr v => exact ha _ _ ar hp hn
  · rw [root_number]; change 0+number a .hole=r; simpa using hr
  · exact (root_total _ b).trans he

/-- Both bounds concern the cardinality of actual independent vertex subsets. -/
theorem count_bounds {c H lip F} (cert : Certificate c H lip F) (p r : Nat) (hr : r ≤ H) :
    2^(p*F r) ≤ coeff c p r ∧ coeff c p r ≤
      (Fintype.card (Labels c p)).choose r * 2^Fintype.card (root (model c)).V * 2^(p*F r) := by
  classical
  constructor
  · have hh := root_lower ((device_realises c _ _).mpr (cert.attain r hr))
    obtain ⟨a,ha,hn,he⟩ := hh
    have hl := lower_count (p:=@parent (root (model c)) p) (o:=@out _ p) a ha ((hole_number a).trans hn)
    rw [free_card,he] at hl; exact hl
  · apply upper_count
    intro a ha hn
    let b := a ∘ Sum.inr
    have leg : Legal (model c).edge b := fun i j e => ha (.inr i) (.inr j) e
    have hh := cert.upper ((device_realises c _ _).mp ⟨b,leg,rfl,rfl⟩)
    rw [hole_number,root_number] at hn
    have hp := cert.monotone (show number b .hole ≤ r by dsimp [b]; omega)
    rw [free_card,root_total]; exact Nat.mul_le_mul_left _ (hh.trans hp)

/-- Each letter compares products of integer cardinalities. -/
def SignedCounts (A : Nat → Nat) (word : List Bool) : Prop :=
  ∀ (i : Nat) (b : Bool), word[i]?=some b →
    if b then A (i+1)*A (i+1) < A i*A (i+2) else A i*A (i+2) < A (i+1)*A (i+1)

theorem transfer_word {c H lip F} {word : List Bool} (cert : Certificate c H lip F)
    (fits : Fits F word) (hw : word.length+1 ≤ H) (p : Nat)
    (sep : let m := Fintype.card (Labels c p); let d := Fintype.card (root (model c)).V
           (2^d*m^H)*(2^d*m^H)<2^p) : SignedCounts (coeff c p) word := by
  let m := Fintype.card (Labels c p)
  let d := Fintype.card (root (model c)).V
  let C := 2^d*m^H
  have hm : 0<m := Fintype.card_pos_iff.mpr ⟨Sum.inl (.inl ())⟩
  have bound (r : Nat) (hr : r≤H) : 2^(p*F r) ≤ coeff c p r ∧ coeff c p r ≤ C*2^(p*F r) := by
    obtain ⟨hl,hu⟩ := count_bounds cert p r hr
    have hc : m.choose r ≤ m^H := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      exact (Nat.div_le_self _ _).trans ((Nat.descFactorial_le_pow m r).trans (Nat.pow_le_pow_right hm hr))
    exact ⟨hl,hu.trans (Nat.mul_le_mul_right _ ((Nat.mul_le_mul_right _ hc).trans_eq (Nat.mul_comm _ _)))⟩
  intro i b h
  have hi : i < word.length := by
    by_contra! hn; rw [List.getElem?_eq_none_iff.mpr hn] at h; contradiction
  have tr := curvature_transfer sep (bound i (by omega)) (bound (i+1) (by omega)) (bound (i+2) (by omega))
  have hs := fits i b h
  cases b <;> simp only [Agrees,curvature,Bool.false_eq_true,if_false,if_true] at hs ⊢
  · apply tr.2; omega
  · apply tr.1; omega

/-- Uniform in the word, and with no enumeration or search hypothesis. -/
theorem physical_every_word (word : List Bool) : ∃ c : Device, ∃ p : Nat, 0<p ∧ SignedCounts (coeff c p) word := by
  obtain ⟨c,F,lip,cert,fits⟩ := every_word word
  let g := root (model c)
  let d := Fintype.card g.V
  let W := weight g
  let H := word.length+1
  let N := d+W+H+1
  let p := 128*N^2
  let m := Fintype.card (Labels c p)
  have he : m=d+p*W := label_card c p
  have hd : d≤N := by dsimp [N]; omega
  have hW : W≤N := by dsimp [N]; omega
  have hH : H≤N := by dsimp [N]; omega
  have hp : 1≤N := by dsimp [N]; omega
  have hd' : d≤3*N^2 := by have := Nat.le_pow (a:=N) (b:=2) (by decide); omega
  have mpos : 0<m := Fintype.card_pos_iff.mpr ⟨Sum.inl (.inl ())⟩
  have hm : m≤2^14*N^7 := by
    have hz := Nat.pow_le_pow_right (n:=N) hp (show 3≤7 by decide)
    have hx := Nat.mul_le_mul_left (128*N^2) hW
    have hn := Nat.le_pow (a:=N) (b:=3) (by decide)
    rw [he]; dsimp [p]; nlinarith
  have sep := explicit_scale hp hd' hm
  have small := Nat.mul_le_mul_left (2^d) (Nat.pow_le_pow_right mpos hH)
  have pp : 0<p := Nat.mul_pos (by decide : 0<128) (Nat.pow_pos hp)
  refine ⟨c,p,pp,transfer_word cert fits (Nat.le_refl _) p ?_⟩
  exact lt_of_le_of_lt (Nat.mul_le_mul small small) sep

end
end Family
end TerminalCurvature
