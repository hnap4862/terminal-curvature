import TerminalCurvature

/-! A universal construction for arbitrary finite words, at the level of actual
three-state configurations of the weighted stars and balanced labels. All budgets
above the target horizon are controlled, including the extra unit at a prefix.
The common zero-weight source is taken negative throughout. -/
set_option linter.unnecessarySeqFocus false

namespace TerminalCurvature

private theorem toAllocation {B r e} {f : Nat → Nat} {ss : List Nat}
    (st : Atlas B f ss r e) (hb : ∀ s ∈ ss, f s ≤ B) :
    ∃ g, Allocation B f ss r g ∧ e ≤ base B ss+g := by
  induction st with
  | empty => exact ⟨0,Allocation.empty,by simp [base]⟩
  | @cons s ss k e x hv rest ih =>
    obtain ⟨g,ha,he⟩ := ih (fun i hi => hb i (by simp [hi]))
    refine ⟨gain B (f s) s (cost x)+g, Allocation.cons (cost x) ha, ?_⟩
    have hx := star_bound (hb s (by simp)) x hv (Nat.le_refl (cost x))
    simp [base,Nat.mul_add] at he ⊢; omega

private theorem fromAllocation {B r g} {f : Nat → Nat} {ss : List Nat}
    (al : Allocation B f ss r g) : ∃ k, k ≤ r ∧ Atlas B f ss k (base B ss+g) := by
  induction al with
  | empty => exact ⟨0,by decide,Atlas.empty⟩
  | @cons s ss r e a rest ih =>
    obtain ⟨k,hk,hs⟩ := ih
    obtain ⟨x,hv,hc,hg⟩ := star_attains B (f s) s a
    refine ⟨cost x+k, by omega, ?_⟩
    have h' := Atlas.cons x hv hs
    rw [hg] at h'
    convert h' using 1 <;> simp [base] <;> ring

/-- Affine continuation is only an upper envelope outside the target horizon. -/
def mainF (E B h : Nat) (f : Nat → Nat) (r : Nat) :=
  E+B*min r h+f (min r h)+2*B*(r-h)

private theorem mainF_in {E B h r : Nat} {f : Nat → Nat} (hr : r ≤ h) :
    mainF E B h f r = E+B*r+f r := by simp [mainF,min_eq_left hr,Nat.sub_eq_zero_of_le hr]

private theorem mainF_out {E B h r : Nat} {f : Nat → Nat} (hr : h ≤ r) :
    mainF E B h f (r+1) = mainF E B h f r+2*B := by
  simp only [mainF,min_eq_right hr,min_eq_right (show h ≤ r+1 by omega)]
  rw [show r+1-h=(r-h)+1 by omega]; ring

private theorem allocUpper {B h r e} {f : Nat → Nat} {ss : List Nat}
    (prof : Profile f h B) (hs : ∀ s ∈ ss, s ≤ h) (al : Allocation B f ss r e) :
    base B ss+e ≤ mainF (base B ss) B h f r := by
  induction r generalizing e with
  | zero =>
    obtain ⟨k,hk,st⟩ := fromAllocation al
    rw [mainF_in (Nat.zero_le _)]
    exact atlas_bound prof st hs hk (Nat.zero_le _)
  | succ r ih =>
    by_cases hr : r+1 ≤ h
    · obtain ⟨k,hk,st⟩ := fromAllocation al
      rw [mainF_in hr]; exact atlas_bound prof st hs hk hr
    · obtain ⟨e',a',he⟩ := trim_allocation al (by omega) (fun i hi => prof.bounded i (hs i hi))
      have hh := ih (e:=e') (by simpa using a')
      rw [mainF_out (show h ≤ r by omega)]; omega

inductive Device where
  | stars (h B : Nat) (f : Nat → Nat)
  | balanced (weight : Nat) (other : Device)

/-- Actual core score and exact empty-core-label count; either nonempty sign of
    a balanced label has the same score and is allowed by the negative source. -/
inductive Run : Device → Nat → Nat → Prop
  | stars {h B f r e} (st : Atlas B f (List.range' 1 h) r e) : Run (.stars h B f) r e
  | keep {c r e} (w : Nat) (st : Run c r e) : Run (.balanced w c) r (w+e)
  | drop {c r e} (w : Nat) (st : Run c r e) : Run (.balanced w c) (r+1) (2*w+e)

/-- On [0,H] this certificate identifies the exact optimum, with no relaxation
    gap between an at-most budget and a witness spending the entire budget. -/
structure Certificate (c : Device) (H lip : Nat) (F : Nat → Nat) : Prop where
  upper : ∀ {r e}, Run c r e → e ≤ F r
  attain : ∀ r, r ≤ H → Run c r (F r)
  monotone : Monotone F
  step : ∀ r, F (r+1) ≤ F r+lip

theorem Certificate.exact {c : Device} {H lip : Nat} {F : Nat → Nat}
    (cert : Certificate c H lip F) {r : Nat} (hr : r ≤ H) :
    (∀ k e, k ≤ r → Run c k e → e ≤ F r) ∧ Run c r (F r) :=
  ⟨fun _ _ hk st => le_trans (cert.upper st) (cert.monotone hk), cert.attain r hr⟩

theorem main_certificate {h B : Nat} {f : Nat → Nat} (prof : Profile f h B) :
    Certificate (.stars h B f) h (2*B) (mainF (base B (List.range' 1 h)) B h f) := by
  have hs : ∀ s ∈ List.range' 1 h, s ≤ h := by
    intro s hx; obtain ⟨i,hi,he⟩ := List.mem_range'.mp hx; omega
  refine ⟨?_,?_,?_,?_⟩
  · intro r e st
    cases st with
    | stars st =>
      obtain ⟨g,al,he⟩ := toAllocation st (fun s hx => prof.bounded s (hs s hx))
      exact le_trans he (allocUpper prof hs al)
  · intro r hr; rw [mainF_in hr]; apply Run.stars
    apply (atlas_exact prof hs hr ?_).2
    by_cases hz : r=0
    · exact Or.inl hz
    · right; apply List.mem_range'.mpr; exact ⟨r-1,by omega,by omega⟩
  · apply monotone_nat_of_le_succ; intro r
    by_cases hr : r+1 ≤ h
    · rw [mainF_in hr,mainF_in (show r ≤ h by omega)]
      have hf := prof.monotone (Nat.le_succ r) hr
      nlinarith
    · rw [mainF_out (show h ≤ r by omega)]; omega
  · intro r; by_cases hr : r+1 ≤ h
    · rw [mainF_in hr,mainF_in (show r ≤ h by omega)]
      have hf := prof.bounded (r+1) hr
      nlinarith [Nat.zero_le (f r)]
    · rw [mainF_out (show h ≤ r by omega)]

def balanceF (w : Nat) (F : Nat → Nat) : Nat → Nat
| 0 => w+F 0
| r+1 => 2*w+F r

theorem balanced_certificate {c : Device} {H lip : Nat} {F : Nat → Nat}
    (cert : Certificate c H lip F) (w : Nat) (hw : lip ≤ w) :
    Certificate (.balanced w c) (H+1) w (balanceF w F) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro r e st
    cases st with
    | keep _ st =>
      have hh := cert.upper st
      cases r with
      | zero => simp [balanceF]; omega
      | succ k => have hh' := cert.step k; simp [balanceF]; omega
    | drop _ st => have hh := cert.upper st; simp [balanceF]; omega
  · intro r hr
    cases r with
    | zero => exact Run.keep w (cert.attain 0 (Nat.zero_le _))
    | succ k => exact Run.drop w (cert.attain k (by omega))
  · apply monotone_nat_of_le_succ; intro r
    cases r with
    | zero => simp [balanceF]; omega
    | succ k => have hh : F k ≤ F (k+1) := cert.monotone (Nat.le_succ k); simp [balanceF]; omega
  · intro r; cases r with
    | zero => simp [balanceF]; omega
    | succ k => have hh := cert.step k; simp [balanceF]; omega

def curvature (F : Nat → Nat) (i : Nat) : Int :=
  (F i : Int)+F (i+2)-2*(F (i+1) : Int)

def Agrees (b : Bool) (q : Int) : Prop := if b then 0 < q else q < 0

def Fits (F : Nat → Nat) (word : List Bool) : Prop :=
  ∀ i b, word[i]? = some b → Agrees b (curvature F i)

theorem first_positive (word : List Bool) (hd : word[0]?=some true) :
    let h := word.length+1
    let f := bonus h (fun i => (word[i]?).getD false)
    let B := f h
    let c := Device.stars h B f
    let F := mainF (base B (List.range' 1 h)) B h f
    Certificate c h (2*B) F ∧ Fits F word := by
  let h := word.length+1
  let w := fun i : Nat => (word[i]?).getD false
  let f := bonus h w
  let B := f h
  let E := base B (List.range' 1 h)
  refine ⟨main_certificate (bonus_profile h w),?_⟩
  intro i b hb
  have hi : i < word.length := by
    by_contra! hn
    have hnone := (List.getElem?_eq_none_iff.mpr hn : word[i]? = none)
    rw [hnone] at hb; contradiction
  have hw : w i = b := by simp [w,hb]
  have hir : i+2 ≤ h := by dsimp [h]; omega
  have hc : curvature (mainF E B h f) i = curvature f i := by
    unfold curvature
    rw [mainF_in hir,mainF_in (show i+1 ≤ h by omega),mainF_in (show i ≤ h by omega)]
    exact affine_curvature E B f i
  rw [hc]
  cases i with
  | zero =>
    rw [hd] at hb; cases hb
    have hh := bonus_curvature_first w (show 0<h by dsimp [h]; omega) hw
    change (0 : Int) < (bonus h w 0 : Int) + (bonus h w 2 : Int) - 2*(bonus h w 1 : Int)
    omega
  | succ i =>
    have hh := bonus_curvature_later h w (show i+1<h by omega)
    change curvature f (i+1) = (if w (i+1) then 1 else -1) at hh
    rw [hh,hw]; cases b <;> norm_num [Agrees]

theorem prepend_negative {c H lip F} {word : List Bool}
    (cert : Certificate c H lip F) (fits : Fits F word) :
    Fits (balanceF (lip+1) F) (false::word) := by
  intro i b hb
  cases i with
  | zero =>
    simp at hb; subst b
    have hh : F 1 ≤ F 0+lip := cert.step 0
    simp [curvature,Agrees,balanceF]; omega
  | succ i =>
    have hi := fits i b (by simpa using hb)
    have he : curvature (balanceF (lip+1) F) (i+1) = curvature F i := by
      simp [curvature,balanceF]; ring
    rwa [he]

/-- No assumptions on either the length or the contents of the input word. -/
theorem every_word (word : List Bool) :
    ∃ c F lip, Certificate c (word.length+1) lip F ∧ Fits F word := by
  induction word with
  | nil =>
    let f := bonus 1 (fun _ => true)
    let B := f 1
    refine ⟨.stars 1 B f,_,_,main_certificate (bonus_profile 1 (fun _ => true)),?_⟩
    intro i b hb; simp at hb
  | cons b word ih =>
    cases b with
    | true => exact ⟨_,_,_,first_positive (true::word) (by simp)⟩
    | false =>
      obtain ⟨c,F,lip,cert,fits⟩ := ih
      exact ⟨.balanced (lip+1) c,_,_,balanced_certificate cert (lip+1) (Nat.le_succ _),
            prepend_negative cert fits⟩

end TerminalCurvature
