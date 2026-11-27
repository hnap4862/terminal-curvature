import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Kernel-checked combinatorial and arithmetic lemmas for terminal curvature.
    Lean 4.19.0 / mathlib v4.19.0. No added axioms or proof placeholders. -/
set_option linter.unnecessarySeqFocus false

namespace TerminalCurvature

inductive Mark | pos | neg | hole deriving DecidableEq, Repr

/-- Counts of the three branch states at a hub; `mark` is the state of the hub. -/
structure StarState where
  mark : Mark
  plusCount : Nat
  minusCount : Nat
  holes : Nat
  deriving Repr

def Valid (s : Nat) (x : StarState) : Prop :=
  x.plusCount + x.minusCount + x.holes = s ∧ (x.mark = .neg → x.plusCount = 0)

def cost (x : StarState) : Nat := x.holes + if x.mark = .hole then 1 else 0

def score (B w : Nat) (x : StarState) : Nat :=
  2*B*x.plusCount + B*x.minusCount + 3*B*x.holes + if x.mark = .pos then 0 else w

def gain (B w s r : Nat) : Nat := B * min r s + if s ≤ r then w else 0

/-- Upper bound for every legal, compressed assignment, including a deleted hub. -/
theorem star_bound {B w s r : Nat} (hw : w ≤ B) (x : StarState)
    (hv : Valid s x) (hc : cost x ≤ r) : score B w x ≤ 2*B*s + gain B w s r := by
  rcases x with ⟨m,a,b,t⟩
  obtain ⟨hs,hneg⟩ := hv
  change a+b+t=s at hs
  cases m with
  | pos =>
    simp [cost] at hc
    simp [score,gain]
    have ht : t ≤ min r s := le_min hc (by omega)
    have hmul := Nat.mul_le_mul_left B ht
    subst s
    have hz : 0 ≤ (if a+b+t ≤ r then w else 0) := Nat.zero_le _
    nlinarith [Nat.zero_le (B*b)]
  | neg =>
    have ha : a = 0 := hneg rfl
    subst a
    simp [cost] at hc
    by_cases h : s ≤ r
    · simp [score,gain,h,min_eq_right h]
      simp at hs
      subst s
      nlinarith [Nat.zero_le (B*b)]
    · have hlt : r < s := by omega
      have hb : 1 ≤ b := by omega
      simp [score,gain,h,min_eq_left (Nat.le_of_lt hlt)]
      simp at hs
      subst s
      nlinarith [Nat.mul_le_mul_left B hb, Nat.mul_le_mul_left B hc]
  | hole =>
    simp [cost] at hc
    by_cases h : s ≤ r
    · simp [score,gain,h,min_eq_right h]
      subst s
      nlinarith [Nat.zero_le (B*a),Nat.zero_le (B*b)]
    · have hlt : r < s := by omega
      simp [score,gain,h,min_eq_left (Nat.le_of_lt hlt)]
      subst s
      nlinarith [Nat.mul_le_mul_left B hc,Nat.zero_le (B*b)]

/-- The upper bound is attainable, not just a relaxation. -/
theorem star_attains (B w s r : Nat) : ∃ x : StarState, Valid s x ∧ cost x ≤ r ∧
    score B w x = 2*B*s + gain B w s r := by
  by_cases h : s ≤ r
  · refine ⟨⟨.neg,0,0,s⟩, ?_, ?_, ?_⟩
    · simp [Valid]
    · simpa [cost] using h
    · simp [score,gain,h,min_eq_right h]; ring
  · have hr : r ≤ s := by omega
    refine ⟨⟨.pos,s-r,0,r⟩, ?_, ?_, ?_⟩
    · simp [Valid,Nat.sub_add_cancel hr]
    · simp [cost]
    · simp [score,gain,h,min_eq_left hr]
      have hh := Nat.sub_add_cancel hr
      have hm := congrArg (fun z : Nat => B*z) hh
      nlinarith

/-- A finite list of true star assignments with the given sizes, total cost, and total score. -/
inductive Atlas (B : Nat) (f : Nat → Nat) : List Nat → Nat → Nat → Prop
| empty : Atlas B f [] 0 0
| cons {s sizes r e} (x : StarState) (valid : Valid s x) (rest : Atlas B f sizes r e) :
    Atlas B f (s::sizes) (cost x+r) (score B (f s) x+e)

def base (B : Nat) (ss : List Nat) : Nat := 2*B*ss.sum

structure Profile (f : Nat → Nat) (H B : Nat) : Prop where
  zero : f 0 = 0
  bounded : ∀ s, s ≤ H → f s ≤ B
  monotone : ∀ {a b}, a ≤ b → b ≤ H → f a ≤ f b
  superadd : ∀ {a b}, a+b ≤ H → f a + f b ≤ f (a+b)

/-- All simultaneous allocations, even with unused budget, satisfy the claimed bound. -/
theorem atlas_bound {B H r e R : Nat} {ss : List Nat} {f : Nat → Nat}
    (prof : Profile f H B) (states : Atlas B f ss r e)
    (hs : ∀ s ∈ ss, s ≤ H) (hr : r ≤ R) (hR : R ≤ H) : e ≤ base B ss + B*R + f R := by
  suffices e ≤ base B ss + B*r + f r by
    have hh := prof.monotone hr hR
    have hm := Nat.mul_le_mul_left B hr
    omega
  have hbudget : r ≤ H := by omega
  clear hr hR R
  induction states with
  | empty => simp [base,prof.zero]
  | @cons s sizes q v x valid rest ih =>
    have hx : cost x ≤ H := by omega
    have hq : q ≤ H := by omega
    have hsH := hs s (by simp)
    have hi := ih (fun a ha => hs a (by simp [ha])) hq
    have hl := star_bound (prof.bounded s hsH) x valid (Nat.le_refl (cost x))
    have bonus : (if s ≤ cost x then f s else 0) ≤ f (cost x) := by
      split <;> rename_i hc
      · exact prof.monotone hc hx
      · omega
    have hm := Nat.mul_le_mul_left B (Nat.min_le_left (cost x) s)
    have hadd := prof.superadd hbudget
    simp only [gain] at hl
    simp only [base,List.sum_cons] at hi ⊢
    nlinarith

/-- Baseline and exact-budget witnesses, on the very same list of hub sizes. -/
theorem atlas_baseline (B : Nat) (f : Nat → Nat) (ss : List Nat) : Atlas B f ss 0 (base B ss) := by
  induction ss with
  | nil => exact Atlas.empty
  | cons s ss ih =>
    have h := Atlas.cons (s:=s) (⟨.pos,s,0,0⟩ : StarState) (by simp [Valid]) ih
    simpa [base,cost,score,Nat.mul_add] using h

theorem atlas_active {B r : Nat} {f : Nat → Nat} {ss : List Nat} (hmem : r ∈ ss) :
    Atlas B f ss r (base B ss+B*r+f r) := by
  induction ss with
  | nil => simp at hmem
  | cons s ss ih =>
    rcases List.mem_cons.mp hmem with h | h
    · subst s
      have h' := Atlas.cons (s:=r) (⟨.neg,0,0,r⟩ : StarState) (by simp [Valid]) (atlas_baseline B f ss)
      convert h' using 1 <;> simp [cost,score,base] <;> ring
    · have h' := Atlas.cons (s:=s) (⟨.pos,s,0,0⟩ : StarState) (by simp [Valid]) (ih h)
      convert h' using 1 <;> simp [cost,score,base] <;> ring

/-- Actual edges of the undirected split graph. `true` denotes a plus endpoint. -/
def Adj {ι : Type} (arrow : ι → ι → Prop) (u v : ι × Bool) : Prop :=
  (u.1 = v.1 ∧ u.2 ≠ v.2) ∨
  (u.2 = true ∧ v.2 = false ∧ arrow u.1 v.1) ∨
  (v.2 = true ∧ u.2 = false ∧ arrow v.1 u.1)

def Independent {ι : Type} (arrow : ι → ι → Prop) (S : ι × Bool → Prop) : Prop :=
  ∀ u v, Adj arrow u v → S u → S v → False

def Legal {ι : Type} (arrow : ι → ι → Prop) (a : ι → Mark) : Prop :=
  ∀ i j, arrow i j → a i = .pos → a j = .neg → False

def selected {ι : Type} (a : ι → Mark) (x : ι × Bool) : Prop :=
  if x.2 then a x.1 = .pos else a x.1 = .neg

theorem legal_iff_independent {ι : Type} (arrow : ι → ι → Prop) (a : ι → Mark) :
    Legal arrow a ↔ Independent arrow (selected a) := by
  constructor
  · intro h ⟨i,b⟩ ⟨j,c⟩ hadj hi hj
    rcases hadj with ⟨eq,ne⟩ | ⟨bp,cn,ar⟩ | ⟨cp,bn,ar⟩
    · change i = j at eq
      subst j
      cases b <;> cases c <;> simp_all [selected]
    · cases b <;> cases c <;> simp_all [selected]
      exact h i j ar hi hj
    · cases b <;> cases c <;> simp_all [selected]
      exact h j i ar hj hi
  · intro h i j ar hp hn
    exact h (i,true) (j,false) (Or.inr (Or.inl ⟨rfl,rfl,ar⟩)) hp hn

noncomputable def markOf {ι : Type} (S : ι × Bool → Prop) (i : ι) : Mark := by
  classical
  exact if S (i,true) then .pos else if S (i,false) then .neg else .hole

theorem mark_selected {ι : Type} (a : ι → Mark) : markOf (selected a) = a := by
  funext i
  cases ha : a i <;> simp [markOf,selected,ha]

theorem selected_mark {ι : Type} {arrow : ι → ι → Prop} (S : ι × Bool → Prop)
    (h : Independent arrow S) : selected (markOf S) = S := by
  funext x
  rcases x with ⟨i,b⟩
  have he : S (i,true) → ¬ S (i,false) := h (i,true) (i,false) (Or.inl ⟨rfl,Bool.noConfusion⟩)
  cases b <;> by_cases hp : S (i,true) <;> by_cases hn : S (i,false) <;>
    simp_all [markOf,selected]

/-- Bijection of independent vertex sets with allowed ternary pair assignments. -/
noncomputable def assignmentsEquiv {ι : Type} (arrow : ι → ι → Prop) :
    {a : ι → Mark // Legal arrow a} ≃ {S : ι × Bool → Prop // Independent arrow S} where
  toFun a := ⟨selected a.val,(legal_iff_independent arrow a.val).mp a.property⟩
  invFun S := ⟨markOf S.val,(legal_iff_independent arrow _).mpr (by rw [selected_mark S.val S.property]; exact S.property)⟩
  left_inv a := Subtype.ext (mark_selected a.val)
  right_inv S := Subtype.ext (selected_mark S.val S.property)

noncomputable def selectedCount {ι : Type} (S : ι × Bool → Prop) (xs : List ι) : Nat := by
  classical
  exact (xs.map (fun i => (if S (i,true) then 1 else 0)+(if S (i,false) then 1 else 0))).sum

def holeCount {ι : Type} (a : ι → Mark) (xs : List ι) : Nat :=
  (xs.map (fun i => if a i = .hole then 1 else 0)).sum

theorem rank_pairing {ι : Type} (a : ι → Mark) (xs : List ι) :
    selectedCount (selected a) xs + holeCount a xs = xs.length := by
  induction xs with
  | nil => simp [selectedCount,holeCount]
  | cons i xs ih =>
    cases hi : a i <;> simp [selectedCount,holeCount,selected,hi] at * <;> omega

/-- Elementary sign transfer from common coefficient envelopes.
    The four entries may coincide, so this also proves both directions for a squared entry. -/
theorem compare_products {p C a b c d A B D E : Nat}
    (hC : C*C < 2^p) (hexp : a+b < c+d)
    (hA : A ≤ C*2^(p*a)) (hB : B ≤ C*2^(p*b))
    (hD : 2^(p*c) ≤ D) (hE : 2^(p*d) ≤ E) : A*B < D*E := by
  calc A*B ≤ (C*2^(p*a))*(C*2^(p*b)) := Nat.mul_le_mul hA hB
       _ = (C*C)*2^(p*(a+b)) := by rw [Nat.mul_add,Nat.pow_add]; ring
       _ < (2^p)*2^(p*(a+b)) := Nat.mul_lt_mul_of_pos_right hC (Nat.pow_pos (by decide))
       _ = 2^(p*(a+b+1)) := by rw [← Nat.pow_add]; congr 1; ring
       _ ≤ 2^(p*(c+d)) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left p hexp)
       _ = 2^(p*c)*2^(p*d) := by rw [Nat.mul_add,Nat.pow_add]
       _ ≤ D*E := Nat.mul_le_mul hD hE

/-- An optional balanced label of weight w, with its baseline contribution removed. -/
def pad (w : Nat) (F : Nat → Nat) : Nat → Nat
| 0 => F 0
| r+1 => max (F (r+1)) (w + F r)

theorem pad_succ {w : Nat} {F : Nat → Nat} (h : ∀ r, F (r+1) ≤ F r+w) (r : Nat) :
    pad w F (r+1) = w+F r := by
  simp only [pad]; exact max_eq_right (by have := h r; omega)

theorem pad_lipschitz {w : Nat} {F : Nat → Nat} (h : ∀ r, F (r+1) ≤ F r+w) (r : Nat) :
    pad w F (r+1) ≤ pad w F r+w := by
  cases r with
  | zero => rw [pad_succ h]; simp [pad,Nat.add_comm]
  | succ r => rw [pad_succ h, pad_succ h]; have := h r; omega

theorem pad_first {w : Nat} {F : Nat → Nat} (h : ∀ r, F (r+1) ≤ F r+w)
    (hw : F 1 < F 0+w) : pad w F 0+pad w F 2 < 2*pad w F 1 := by
  change F 0+pad w F (1+1) < 2*pad w F (0+1)
  rw [pad_succ h, pad_succ h]; omega

theorem pad_shift {w : Nat} {F : Nat → Nat} (h : ∀ r, F (r+1) ≤ F r+w) (r : Nat) :
    (pad w F (r+1)+pad w F (r+3) : Int) - 2*(pad w F (r+2) : Int) =
    (F r : Int)+F (r+2)-2*(F (r+1) : Int) := by
  rw [show r+3=(r+2)+1 by omega,show r+2=(r+1)+1 by omega]
  rw [pad_succ h, pad_succ h, pad_succ h]; push_cast; ring

def increments (w : Nat → Bool) : Nat → Nat
| 0 => 0
| i+1 => increments w i + if w i then 1 else 0

def slope (H : Nat) (w : Nat → Bool) (i : Nat) := H+2*increments w i-i

def integral (H : Nat) (w : Nat → Bool) : Nat → Nat
| 0 => 0
| i+1 => integral H w i + slope H w i

def amplitude (H : Nat) (w : Nat → Bool) := 2*integral H w H + 1

def bonus (H : Nat) (w : Nat → Bool) : Nat → Nat
| 0 => 0
| n+1 => amplitude H w*(2*n+1) + integral H w (n+1)

theorem integral_mono (H : Nat) (w : Nat → Bool) : Monotone (integral H w) :=
  monotone_nat_of_le_succ fun n => by simp [integral]

theorem bonus_mono (H : Nat) (w : Nat → Bool) : Monotone (bonus H w) := by
  apply monotone_nat_of_le_succ
  intro j
  cases j with
  | zero => simp [bonus]
  | succ j =>
    simp only [bonus]
    have h := integral_mono H w (Nat.le_succ (j+1))
    nlinarith [Nat.zero_le (amplitude H w)]

theorem bonus_profile (H : Nat) (w : Nat → Bool) : Profile (bonus H w) H (bonus H w H) := by
  constructor
  · rfl
  · intro s hs; exact bonus_mono H w hs
  · intro a b hab _; exact bonus_mono H w hab
  · intro a b hab
    cases a with
    | zero => simp [bonus]
    | succ a =>
      cases b with
      | zero => simp [bonus]
      | succ b =>
        have hu := integral_mono H w (show a+1 ≤ H by omega)
        have hv := integral_mono H w (show b+1 ≤ H by omega)
        simp only [bonus, Nat.add_succ]
        dsimp [amplitude]
        nlinarith [Nat.zero_le (integral H w (a+1+(b+1)))]

theorem integral_curvature (H : Nat) (w : Nat → Bool) {n : Nat} (hn : n < H) :
    (integral H w n : Int) + integral H w (n+2) - 2*(integral H w (n+1) : Int) =
      (if w n then 1 else -1) := by
  have ha : n ≤ H+2*increments w n := by omega
  have hb : n+1 ≤ H+2*increments w (n+1) := by omega
  simp only [integral, slope, Nat.cast_add, Nat.cast_sub ha, Nat.cast_sub hb]
  cases h : w n <;> simp [increments,h] <;> omega

theorem bonus_curvature_later (H : Nat) (w : Nat → Bool) {n : Nat} (hn : n+1 < H) :
    (bonus H w (n+1) : Int) + bonus H w (n+3) - 2*(bonus H w (n+2) : Int) =
      (if w (n+1) then 1 else -1) := by
  have h := integral_curvature H w hn
  simp only [bonus, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at *
  linarith

theorem bonus_curvature_first {H : Nat} (w : Nat → Bool) (hH : 0 < H) (hw : w 0 = true) :
    2*bonus H w 1 < bonus H w 0+bonus H w 2 := by
  have h := integral_curvature H w hH
  simp only [hw, if_true] at h
  change (0 : Int) + (integral H w 2 : Int) - 2*(integral H w 1 : Int) = 1 at h
  simp [bonus,amplitude]
  omega

/-- Increasing the allocation of a single star by one gains at most 2B. -/
theorem gain_step (B w s r : Nat) (hw : w ≤ B) :
    gain B w s (r+1) ≤ gain B w s r+2*B := by
  rcases lt_trichotomy s (r+1) with h | h | h
  · have hs : s ≤ r := by omega
    simp [gain,hs,Nat.le_of_lt h,min_eq_right hs,min_eq_right (Nat.le_of_lt h)]
  · subst s
    simp [gain,Nat.not_succ_le_self,min_eq_left (Nat.le_succ r)]
    nlinarith
  · have h₁ : ¬s ≤ r+1 := by omega
    have h₂ : ¬s ≤ r := by omega
    have h₃ : r ≤ s := by omega
    simp [gain,h₁,h₂,min_eq_left (Nat.le_of_lt h),min_eq_left h₃]
    nlinarith

/-- Resource allocations for independent stars after their individual maximisation. -/
inductive Allocation (B : Nat) (f : Nat → Nat) : List Nat → Nat → Nat → Prop
| empty : Allocation B f [] 0 0
| cons {s ss r e} (a : Nat) (rest : Allocation B f ss r e) :
    Allocation B f (s::ss) (a+r) (gain B (f s) s a+e)

theorem trim_allocation {B r e : Nat} {ss : List Nat} {f : Nat → Nat}
    (al : Allocation B f ss r e) (hr : 0 < r) (hb : ∀ s ∈ ss, f s ≤ B) :
    ∃ e', Allocation B f ss (r-1) e' ∧ e ≤ e'+2*B := by
  induction al with
  | empty => omega
  | @cons s ss r e a rest ih =>
    cases a with
    | zero =>
      have hpos : 0 < r := by omega
      obtain ⟨e',ha,he⟩ := ih hpos (fun s h => hb s (by simp [h]))
      refine ⟨gain B (f s) s 0+e', ?_, ?_⟩
      · simpa using (Allocation.cons (s:=s) 0 ha)
      · omega
    | succ a =>
      refine ⟨gain B (f s) s a+e, ?_, ?_⟩
      · convert (Allocation.cons (s:=s) a rest) using 1 <;> omega
      · have hh := gain_step B (f s) s a (hb s (by simp))
        omega

/-- The extremal score of the entire main core, expressed without an abstract maximum. -/
theorem atlas_exact {B H r : Nat} {ss : List Nat} {f : Nat → Nat}
    (prof : Profile f H B) (hs : ∀ s ∈ ss, s ≤ H) (hr : r ≤ H)
    (cover : r = 0 ∨ r ∈ ss) :
    (∀ k e, k ≤ r → Atlas B f ss k e → e ≤ base B ss+B*r+f r) ∧
    Atlas B f ss r (base B ss+B*r+f r) := by
  refine ⟨fun k e hk st => atlas_bound prof st hs hk hr, ?_⟩
  rcases cover with hz | hm
  · subst r; simpa [prof.zero] using atlas_baseline B f ss
  · exact atlas_active hm

/-- The closed form for the main extremum is affine plus `f`, so it keeps its curvature. -/
theorem affine_curvature (C B : Nat) (f : Nat → Nat) (r : Nat) :
    ((C+B*r+f r : Nat) : Int) + (C+B*(r+2)+f (r+2) : Nat) - 2*(C+B*(r+1)+f (r+1) : Nat) =
    (f r : Int) + f (r+2) - 2 * (f (r+1) : Int) := by push_cast; ring

/-- Exact contribution of free binary labels, combined across different patterns. -/
def ways (xs : List Nat) : Nat := (xs.map fun e => 2^e).sum

theorem ways_envelope (xs : List Nat) (k : Nat) (upper : ∀ i ∈ xs, i ≤ k) (hit : k ∈ xs) :
    2^k ≤ ways xs ∧ ways xs ≤ xs.length*2^k := by
  constructor
  · induction xs with
    | nil => simp at hit
    | cons a xs ih =>
      simp only [List.mem_cons] at hit
      rcases hit with h | h
      · subst a; simp [ways]
      · have hh := ih (fun i hi => upper i (by simp [hi])) h
        change 2^k ≤ 2^a + ways xs
        exact le_trans hh (Nat.le_add_left _ _)
  · clear hit
    induction xs with
    | nil => simp [ways]
    | cons a xs ih =>
      have ha := Nat.pow_le_pow_right (by decide : 0 < 2) (upper a (by simp))
      have ht := ih (fun i hi => upper i (by simp [hi]))
      simp only [ways,List.map_cons,List.sum_cons,List.length_cons] at *
      rw [Nat.add_mul]; omega

/-- All numerical bounds here are integers. The hypothesis on m is proved from the
    core size and the number of attachments in the accompanying construction. -/
theorem explicit_scale {H d m : Nat} (hH : 1 ≤ H) (hd : d ≤ 3*H^2)
    (hm : m ≤ 2^14 * H^7) : (2^d*m^H)*(2^d*m^H) < 2^(128*H^2) := by
  have ha := Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_two_pow_self (n:=H))) 7
  have hm' : m ≤ 2^(14+H*7) := by
    rw [Nat.pow_add,Nat.pow_mul]; exact Nat.le_trans hm (Nat.mul_le_mul_left _ ha)
  have hc : 2^d*m^H ≤ 2^(d+(14+H*7)*H) := by
    rw [Nat.pow_add,Nat.pow_mul]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm' H)
  have hh : H ≤ H^2 := by nlinarith [Nat.mul_le_mul_left H hH]
  calc _ ≤ 2^(d+(14+H*7)*H)*2^(d+(14+H*7)*H) := Nat.mul_le_mul hc hc
       _ = 2^((d+(14+H*7)*H)+(d+(14+H*7)*H)) := (Nat.pow_add _ _ _).symm
       _ < _ := Nat.pow_lt_pow_right (by decide) (by nlinarith)

/-- Kernel-checked two-sided sign transfer for any triple under a common prefactor. -/
theorem curvature_transfer {p C a b c x y z : Nat} (sep : C*C < 2^p)
    (hx : 2^(p*a) ≤ x ∧ x ≤ C*2^(p*a)) (hy : 2^(p*b) ≤ y ∧ y ≤ C*2^(p*b))
    (hz : 2^(p*c) ≤ z ∧ z ≤ C*2^(p*c)) :
    (b+b < a+c → y*y < x*z) ∧ (a+c < b+b → x*z < y*y) :=
  ⟨fun h => compare_products sep h hy.2 hy.2 hx.1 hz.1,
   fun h => compare_products sep h hx.2 hz.2 hy.1 hy.1⟩

end TerminalCurvature
