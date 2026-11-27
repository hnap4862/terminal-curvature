import Geometry

namespace TerminalCurvature
namespace Quantitative
noncomputable section
open Assembly Family Geometry

private theorem inc_le (w : Nat → Bool) (i : Nat) : increments w i ≤ i := by
  induction i with
  | zero => simp [increments]
  | succ i ih => cases hw : w i <;> simp [increments,hw] <;> omega

private theorem integral_le (h : Nat) (w : Nat → Bool) (i : Nat) (hi : i ≤ h) :
    integral h w i ≤ 2*h*i := by
  induction i with
  | zero => simp [integral]
  | succ i ih =>
    have hs : slope h w i ≤ 2*h := by
      unfold slope
      have := inc_le w i
      omega
    have ht := ih (by omega)
    simp only [integral, Nat.mul_succ]
    omega

theorem bonus_le (h : Nat) (w : Nat → Bool) (hh : 1≤h) : bonus h w h ≤ 12*h^3 := by
  have hv := integral_le h w h (Nat.le_refl _)
  have hh2 := Nat.le_pow (a:=h) (b:=2) (by decide)
  have hh3 := Nat.pow_le_pow_right (n:=h) hh (show 2≤3 by decide)
  cases h with
  | zero => omega
  | succ j =>
    simp only [bonus,amplitude] at *
    have hD : 2*integral (j+1) w (j+1)+1 ≤ 5*(j+1)^2 := by nlinarith
    have hm := Nat.mul_le_mul hD (show 2*j+1 ≤ 2*(j+1) by omega)
    calc _ ≤ 5*(j+1)^2*(2*(j+1)) + 2*(j+1)*(j+1) := Nat.add_le_add hm hv
         _ ≤ _ := by nlinarith

private theorem union_weight (g k : Model) : weight (union g k)=weight g+weight k :=
  Fintype.sum_sum_type _

private theorem root_weight (g : Model) : weight (root g)=weight g := by
  unfold weight
  change (∑ i : Unit ⊕ g.V, _) = _
  rw [Fintype.sum_sum_type]
  simp [root]

private theorem star_weight (s B b : Nat) : weight (star s B b)=b+s*(3*B) := by
  unfold weight
  change (∑ i : Unit ⊕ Fin s, _) = _
  rw [Fintype.sum_sum_type]
  simp [star, ← Nat.mul_add]
  exact Or.inl (by omega)

private theorem stars_bounds (h B : Nat) (f : Nat → Nat) (ss : List Nat)
    (hs : ∀ s ∈ ss, s≤h) (hf : ∀ s ∈ ss, f s≤B) :
    Fintype.card (stars B f ss).V ≤ ss.length*(h+1) ∧
    weight (stars B f ss) ≤ ss.length*(B+h*(3*B)) := by
  induction ss with
  | nil =>
    simp [stars, empty, weight]
  | cons s ss ih =>
    obtain ⟨hc,hw⟩ := ih (fun i hi => hs i (by simp [hi])) (fun i hi => hf i (by simp [hi]))
    have hsc := hs s (by simp)
    have hsf := hf s (by simp)
    have hsm := Nat.mul_le_mul_right (3*B) hsc
    rw [stars,union_weight,star_weight]
    change Fintype.card ( (Unit ⊕ Fin s) ⊕ (stars B f ss).V) ≤ _ ∧ _
    simp only [Fintype.card_sum,Fintype.card_unit,Fintype.card_fin,List.length_cons,Nat.add_mul]
    omega

private theorem main_size {h B : Nat} {f : Nat → Nat} (prof : Profile f h B) :
    Fintype.card (model (.stars h B f)).V ≤ h*(h+1) ∧
    weight (model (.stars h B f)) ≤ h*(B+h*(3*B)) := by
  have hs : ∀ s ∈ List.range' 1 h, s≤h := by
    intro s hx; obtain ⟨i,hi,he⟩ := List.mem_range'.mp hx; omega
  simpa [model] using stars_bounds h B f _ hs (fun s hx => prof.bounded s (hs s hx))

private theorem balance_card (c : Device) (w : Nat) :
    Fintype.card (model (.balanced w c)).V = 1+Fintype.card (model c).V := by
  change Fintype.card (Unit ⊕ (model c).V) = _
  simp

private theorem balance_weight (c : Device) (w : Nat) :
    weight (model (.balanced w c)) = 2*w+weight (model c) := by
  rw [model,union_weight]
  have hs : weight (single w)=2*w := by
    unfold weight
    change (∑ _ : Unit, w+w) = _
    simp; omega
  rw [hs]

private theorem base_estimates {h B : Nat} {f : Nat → Nat} (hh : 1≤h)
    (prof : Profile f h B) (hb : B≤12*h^3) :
    Fintype.card (model (.stars h B f)).V ≤ h*(h+1) ∧
      weight (model (.stars h B f)) ≤ 100*h^5 ∧ 2*B≤25*h^3 := by
  obtain ⟨hc,hw⟩ := main_size prof
  have hb' : B+h*(3*B) ≤ 48*h^4 := by
    have hm := Nat.mul_le_mul_left (3*h) hb
    have hp := Nat.pow_le_pow_right (n:=h) hh (show 3≤4 by decide)
    nlinarith
  exact ⟨hc, (hw.trans (Nat.mul_le_mul_left h hb')).trans (by nlinarith), by omega⟩

theorem bounded_word (word : List Bool) :
    let H := word.length+1
    ∃ c F lip, Certificate c H lip F ∧ Fits F word ∧
      Fintype.card (model c).V ≤ H*(H+1) ∧ weight (model c) ≤ 100*H^5 ∧ lip≤25*H^3 := by
  induction word with
  | nil =>
    let f := bonus 1 (fun _ => true)
    let B := f 1
    have prof := bonus_profile 1 (fun _ => true)
    refine ⟨.stars 1 B f,_,_,main_certificate prof,?_,base_estimates (by decide) prof (bonus_le 1 _ (by decide))⟩
    intro i b hb; simp at hb
  | cons b word ih =>
    cases b with
    | true =>
      have h := first_positive (true::word) (by simp)
      exact ⟨_,_,_,h.1,h.2,base_estimates (Nat.succ_pos _) (bonus_profile _ _) (bonus_le _ _ (Nat.succ_pos _))⟩
    | false =>
      obtain ⟨c,F,lip,cert,fits,hc,hw,hl⟩ := ih
      let H := word.length+1
      have hc' : Fintype.card (model c).V≤H*(H+1) := hc
      have hw' : weight (model c)≤100*H^5 := hw
      have hl' : lip≤25*H^3 := hl
      refine ⟨.balanced (lip+1) c,_,_,balanced_certificate cert (lip+1) (Nat.le_succ _),
        prepend_negative cert fits,?_,?_,?_⟩
      · rw [balance_card]; change _ ≤ (H+1)*(H+1+1); nlinarith
      · rw [balance_weight]; change _ ≤ 100*(H+1)^5
        nlinarith [Nat.zero_le (H^4),Nat.zero_le (H^3),Nat.zero_le (H^2)]
      · change lip+1 ≤ 25*(H+1)^3
        nlinarith [Nat.zero_le (H^2)]

theorem bounded_instance {c H lip F} {word : List Bool}
    (cert : Certificate c H lip F) (fits : Fits F word) (hw : word.length+1≤H)
    (hd : Fintype.card (model c).V≤H*(H+1)) (hW : weight (model c)≤100*H^5) :
    let p := 128*H^2
    Fintype.card (Labels c p × Bool) < 2^15*H^7 ∧ SignedCounts (coeff c p) word := by
  let p := 128*H^2
  let m := Fintype.card (Labels c p)
  let d := Fintype.card (root (model c)).V
  have hH : 1≤H := by omega
  have hp2 := Nat.le_pow (a:=H) (b:=2) (by decide)
  have hd' : d≤3*H^2 := by
    change Fintype.card (Unit ⊕ (model c).V) ≤ _
    simp only [Fintype.card_sum,Fintype.card_unit]
    nlinarith
  have hm : m<2^14*H^7 := by
    have hx := Nat.mul_le_mul_left p hW
    have hy := Nat.pow_le_pow_right (n:=H) hH (show 2≤7 by decide)
    have hz : 0<H^7 := Nat.pow_pos hH
    change Fintype.card (Labels c p) < _
    rw [label_card,root_weight]
    change d+p*weight (model c) < _
    dsimp [p] at *
    nlinarith
  have sep := explicit_scale hH hd' (Nat.le_of_lt hm)
  exact ⟨by simp only [Fintype.card_prod,Fintype.card_bool]; change m*2 < _; omega,
    transfer_word cert fits hw p sep⟩

theorem bounded_matched_tree_every_word (word : List Bool) :
    ∃ c : Device, let p := 128*(word.length+1)^2
      Fintype.card (Labels c p×Bool) < 2^15*(word.length+1)^7 ∧
      SignedCounts (coeff c p) word ∧ Forest (Adj (arrows c p)) ∧
      (∀ u v, ∃ n, n≤10 ∧ Walk (Adj (arrows c p)) u v n) ∧
      (∀ u, mate (mate u)=u ∧ mate u≠u ∧ Adj (arrows c p) u (mate u)) ∧
      (∀ S : Finset (Labels c p×Bool), Independent (arrows c p) (fun x => x∈S) →
        S.card≤Fintype.card (Labels c p)) ∧
      (∃ S : Finset (Labels c p×Bool), Independent (arrows c p) (fun x => x∈S) ∧
        S.card=Fintype.card (Labels c p)) := by
  obtain ⟨c,F,lip,cert,fits,hd,hW,_⟩ := bounded_word word
  obtain ⟨sz,signs⟩ := bounded_instance cert fits (Nat.le_refl _) hd hW
  exact ⟨c,sz,signs,acyclic _ _,diameter_ten _ _,perfect_matching _,independence_number _⟩

/-- The all-positive word admits a smaller, sixth-degree order bound. -/
theorem all_positive_order (L : Nat) :
    ∃ c : Device, let H := L+1; let p := 128*H^2
      Fintype.card (Labels c p×Bool) < 2^14*H^6 ∧
      SignedCounts (coeff c p) (List.replicate L true) ∧
      Forest (Adj (arrows c p)) ∧
      (∀ u v, ∃ n, n≤10 ∧ Walk (Adj (arrows c p)) u v n) ∧
      (∀ u, mate (mate u)=u ∧ mate u≠u ∧ Adj (arrows c p) u (mate u)) := by
  let H := L+1
  let f : Nat → Nat := fun j => j^2
  let B := H^2
  let c := Device.stars H B f
  let p := 128*H^2
  let F := mainF (base B (List.range' 1 H)) B H f
  have hH : 1≤H := by dsimp [H]; omega
  have prof : Profile f H B := by
    refine ⟨rfl,?_,?_,?_⟩
    · intro s hs; exact Nat.pow_le_pow_left hs 2
    · intro a b hab _; exact Nat.pow_le_pow_left hab 2
    · intro a b _; dsimp [f]; nlinarith [Nat.zero_le (a*b)]
  have cert : Certificate c H (2*B) F := main_certificate prof
  have fit : Fits F (List.replicate L true) := by
    intro i b hi
    have hb : true=b := by
      have he := List.getElem?_replicate (n:=L) (a:=true) (i:=i)
      rw [hi] at he
      split at he <;> simp_all
    subst b
    have hl : i<L := by simpa using ((List.getElem?_eq_some_iff.mp hi).choose)
    have hF (r : Nat) (hr : r≤H) : F r=base B (List.range' 1 H)+B*r+f r := by
      simp [F,mainF,min_eq_left hr,Nat.sub_eq_zero_of_le hr]
    change (0 : Int) < (F i : Int)+F (i+2)-2*(F (i+1) : Int)
    rw [hF i (by dsimp [H]; omega),hF (i+1) (by dsimp [H]; omega),hF (i+2) (by dsimp [H]; omega)]
    rw [affine_curvature]
    dsimp [f]
    push_cast
    ring_nf
    decide
  obtain ⟨hd,hW⟩ := main_size prof
  let m := Fintype.card (Labels c p)
  let d := Fintype.card (root (model c)).V
  have h₂ := Nat.le_pow (a:=H) (b:=2) (by decide)
  have h₄ := Nat.pow_le_pow_right hH (show 2≤4 by decide)
  have h₆ := Nat.pow_le_pow_right hH (show 2≤6 by decide)
  have h₇ := Nat.pow_le_pow_right hH (show 6≤7 by decide)
  have hpos : 0<H^6 := Nat.pow_pos hH
  have hd' : d≤3*H^2 := by
    change Fintype.card (Unit ⊕ (model c).V) ≤ _
    simp only [Fintype.card_sum,Fintype.card_unit]
    nlinarith
  have w' : weight (model c) ≤ 4*H^4 := by
    have h₃ := Nat.pow_le_pow_right hH (show 3≤4 by decide)
    dsimp [B] at hW
    nlinarith
  have hm : m<2^13*H^6 := by
    have hh := Nat.mul_le_mul_left p w'
    change Fintype.card (Labels c p) < _
    rw [label_card,root_weight]
    change d+p*weight (model c) < _
    dsimp [p] at hh ⊢
    nlinarith
  have hm' : m≤2^14*H^7 := by nlinarith
  refine ⟨c,?_,transfer_word cert fit (by simp [H]) p (explicit_scale hH hd' hm'),
    acyclic _ _,diameter_ten _ _,perfect_matching _⟩
  change Fintype.card (Labels c p×Bool) < _
  simp only [Fintype.card_prod,Fintype.card_bool]
  change m*2<2^14*H^6
  omega

end
end Quantitative
end TerminalCurvature
