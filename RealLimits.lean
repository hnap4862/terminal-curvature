import Limits
import Mathlib.Data.Real.Archimedean
import Mathlib.Topology.Algebra.Ring.Real

namespace TerminalCurvature
namespace Quantitative
open Family Filter
open scoped Topology

noncomputable def ratio (c : Device) (i p : Nat) : ℝ :=
  ((coeff c p i : ℝ) * coeff c p (i+2)) /
    ((coeff c p (i+1) : ℝ) * coeff c p (i+1))

private theorem ratios_tendsto (c : Device) (word : List Bool)
    (limits : ∀ K : Nat, ∃ P, ∀ p ≥ P, ∀ (i : Nat) (b : Bool), word[i]?=some b →
      let A := coeff c p
      0 < A (i+1) ∧
      (if b then K*(A (i+1)*A (i+1)) < A i*A (i+2)
       else K*(A i*A (i+2)) < A (i+1)*A (i+1))) :
    ∀ (i : Nat) (b : Bool), word[i]?=some b →
      if b then Tendsto (ratio c i) atTop atTop else Tendsto (ratio c i) atTop (𝓝 0) := by
  intro i b h
  cases b
  · simp only [Bool.false_eq_true,if_false]
    apply tendsto_order.2
    constructor
    · intro a ha
      exact Eventually.of_forall fun p => lt_of_lt_of_le ha (by unfold ratio; positivity)
    · intro a ha
      obtain ⟨K,hK⟩ := exists_nat_gt (1/a)
      obtain ⟨P,hP⟩ := limits K
      apply eventually_atTop.2
      refine ⟨P,?_⟩
      intro p hp
      obtain ⟨hpos,hlt⟩ := hP p hp i false h
      simp only [Bool.false_eq_true,if_false] at hlt
      let x : ℝ := (coeff c p i : ℝ)*coeff c p (i+2)
      let y : ℝ := (coeff c p (i+1) : ℝ)*coeff c p (i+1)
      have hy : 0<y := by dsimp [y]; positivity
      have hx : 0≤x := by dsimp [x]; positivity
      have hkxy : (K : ℝ)*x<y := by dsimp [x,y]; exact_mod_cast hlt
      have hka : 1<(K : ℝ)*a := (div_lt_iff₀ ha).mp hK
      have hKpos : 0<(K : ℝ) := lt_of_le_of_lt (show (0:ℝ) ≤ 1/a by positivity) hK
      change x/y<a
      apply (div_lt_iff₀ hy).mpr
      apply lt_of_mul_lt_mul_left (a:=(K:ℝ)) _ hKpos.le
      calc
        (K:ℝ)*x < y := hkxy
        _ ≤ (K:ℝ)*(a*y) := by nlinarith [mul_le_mul_of_nonneg_right hka.le hy.le]
  · simp only [if_true]
    apply tendsto_atTop.2
    intro a
    obtain ⟨K,hK⟩ := exists_nat_gt a
    obtain ⟨P,hP⟩ := limits K
    apply eventually_atTop.2
    refine ⟨P,?_⟩
    intro p hp
    obtain ⟨hpos,hlt⟩ := hP p hp i true h
    simp only [if_true] at hlt
    have ht := (lt_div_iff₀ (show 0 < (coeff c p (i+1):ℝ)*coeff c p (i+1) by positivity)).mpr
      (show (K:ℝ)*((coeff c p (i+1):ℝ)*coeff c p (i+1))<(coeff c p i:ℝ)*coeff c p (i+2) by exact_mod_cast hlt)
    exact hK.le.trans ht.le

/-- Real-valued limits, with one core and a common threshold for each integer tolerance. -/
theorem real_limits_from_certificate {c H lip F} {word : List Bool}
    (cert : Certificate c H lip F) (fit : Fits F word) (hw : word.length+1≤H) :
    ∀ (i : Nat) (b : Bool), word[i]?=some b →
      if b then Tendsto (ratio c i) atTop atTop else Tendsto (ratio c i) atTop (𝓝 0) :=
  ratios_tendsto c word (ratio_thresholds cert fit hw)

theorem bounded_family_real_limits (word : List Bool) :
    ∃ c : Device,
      (let p := 128*(word.length+1)^2
       Fintype.card (Labels c p×Bool) < 2^15*(word.length+1)^7 ∧ SignedCounts (coeff c p) word) ∧
      (∀ p, Geometry.Forest (Adj (arrows c p)) ∧
        (∀ u v, ∃ n, n≤10 ∧ Geometry.Walk (Adj (arrows c p)) u v n) ∧
        (∀ u, Geometry.mate (Geometry.mate u)=u ∧ Geometry.mate u≠u ∧ Adj (arrows c p) u (Geometry.mate u)) ∧
        (∀ S : Finset (Labels c p×Bool), Independent (arrows c p) (fun x => x∈S) →
          S.card≤Fintype.card (Labels c p)) ∧
        (∃ S : Finset (Labels c p×Bool), Independent (arrows c p) (fun x => x∈S) ∧
          S.card=Fintype.card (Labels c p))) ∧
      (∀ (i : Nat) (b : Bool), word[i]?=some b →
        if b then Tendsto (ratio c i) atTop atTop else Tendsto (ratio c i) atTop (𝓝 0)) := by
  obtain ⟨c,hbound,hgeometry,hlim⟩ := bounded_witness_and_limits word
  exact ⟨c,hbound,hgeometry,ratios_tendsto c word hlim⟩

end Quantitative
end TerminalCurvature
