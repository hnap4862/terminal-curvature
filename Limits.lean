import Bounds
import Mathlib.Data.Nat.Choose.Sum

/-! Ratio limits stated by their positive integer threshold criteria.
The negative branch eventually lies below 1/K for every positive integer K. -/
namespace TerminalCurvature
namespace Quantitative
open Assembly Family

private theorem polynomial_lt_exp (K D : Nat) :
    ∃ P, ∀ p ≥ P, K*p^D < 2^p := by
  let k := D+1
  let Q := k.factorial * K * 2^D
  refine ⟨2*D+Q+1, ?_⟩
  intro p hp
  let u := p-D
  have hpu : p ≤ 2*u := by dsimp [u]; omega
  have hu : Q < u := by dsimp [u]; omega
  have up : 0<u^D := Nat.pow_pos (by omega)
  have le₁ := Nat.mul_le_mul_left (k.factorial*K) (Nat.pow_le_pow_left hpu D)
  rw [Nat.mul_pow] at le₁
  have le₂ := Nat.mul_lt_mul_of_pos_right hu up
  have lo : (p+1-k)^k ≤ k.factorial*p.choose k := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.pow_sub_le_descFactorial _ _
  have hi : p.choose k ≤ 2^p := by
    rw [← Nat.sum_range_choose]
    exact Finset.single_le_sum (f:=fun i => p.choose i) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by dsimp [k]; omega))
  have hh : (p+1-k)^k=u^D*u := by
    rw [show p+1-k=u by dsimp [k,u]; omega]
    exact Nat.pow_succ _ _
  rw [hh] at lo
  have hpos := Nat.factorial_pos k
  have lin : k.factorial*(K*p^D) < k.factorial*2^p := by
    calc
      _ ≤ Q*u^D := by dsimp [Q]; nlinarith only [le₁]
      _ < u*u^D := le₂
      _ ≤ k.factorial*p.choose k := by simpa [Nat.mul_comm] using lo
      _ ≤ _ := Nat.mul_le_mul_left _ hi
  exact Nat.lt_of_mul_lt_mul_left lin

theorem scaled_prefactor (c : Device) (H K : Nat) :
    ∃ P, ∀ p ≥ P, let d := Fintype.card (root (model c)).V; let m := Fintype.card (Labels c p)
      K*(2^d*m^H)*(2^d*m^H) < 2^p := by
  let d := Fintype.card (root (model c)).V
  let W := weight (root (model c))
  let D := 2*H
  let Q := K*(2^d)^2*(d+W)^D
  obtain ⟨P,hP⟩ := polynomial_lt_exp Q D
  refine ⟨P+1,?_⟩
  intro p hp
  have hm : Fintype.card (Labels c p) ≤ (d+W)*p := by
    rw [label_card]
    change d+p*W ≤ (d+W)*p
    have hd := Nat.mul_le_mul_left d (show 1≤p by omega)
    nlinarith
  have hh := Nat.pow_le_pow_left hm H
  have hh' := Nat.mul_le_mul_left (2^d) hh
  have hs := Nat.mul_le_mul_left K (Nat.mul_le_mul hh' hh')
  change K*(2^d*Fintype.card (Labels c p)^H)*(2^d*Fintype.card (Labels c p)^H)<2^p
  refine lt_of_le_of_lt ?_ (hP p (by omega))
  rw [Nat.mul_pow] at hs
  dsimp [Q,D]
  rw [Nat.pow_mul',Nat.pow_mul']
  nlinarith only [hs]

/-- The first product stays less than or equal to an exponential envelope,
with its factor K absorbed by the gap of at least one in the exponents. -/
private theorem factor_compare {K C p a b c d A B X Y : Nat}
    (hs : K*C*C<2^p) (he : a+b<c+d)
    (ha : A≤C*2^(p*a)) (hb : B≤C*2^(p*b))
    (hx : 2^(p*c)≤X) (hy : 2^(p*d)≤Y) :
    K*(A*B)<X*Y := by
  calc
    _ ≤ K*((C*2^(p*a))*(C*2^(p*b))) := Nat.mul_le_mul_left _ (Nat.mul_le_mul ha hb)
    _ = (K*C*C)*2^(p*(a+b)) := by rw [Nat.mul_add,Nat.pow_add]; ring
    _ < (2^p)*2^(p*(a+b)) := Nat.mul_lt_mul_of_pos_right hs (by positivity)
    _ = 2^(p*(a+b+1)) := by rw [←Nat.pow_add]; congr 1; ring
    _ ≤ 2^(p*(c+d)) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left p he)
    _ = 2^(p*c)*2^(p*d) := by rw [Nat.mul_add,Nat.pow_add]
    _ ≤ _ := Nat.mul_le_mul hx hy

theorem ratio_thresholds {c H lip F} {word : List Bool}
    (cert : Certificate c H lip F) (fits : Fits F word) (hw : word.length+1≤H) :
    ∀ K : Nat, ∃ P, ∀ p ≥ P, ∀ (i : Nat) (b : Bool), word[i]?=some b →
      let A := coeff c p
      0 < A (i+1) ∧
      (if b then K*(A (i+1)*A (i+1)) < A i*A (i+2)
       else K*(A i*A (i+2)) < A (i+1)*A (i+1)) := by
  intro K
  obtain ⟨P,hP⟩ := scaled_prefactor c H K
  refine ⟨P,?_⟩
  intro p hp i b h
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
  have hi : i < word.length := by
    by_contra! hn
    rw [List.getElem?_eq_none_iff.mpr hn] at h
    contradiction
  obtain ⟨xl,xu⟩ := bound i (by omega)
  obtain ⟨yl,yu⟩ := bound (i+1) (by omega)
  obtain ⟨zl,zu⟩ := bound (i+2) (by omega)
  have hs := fits i b h
  have sep : K*C*C<2^p := hP p hp
  refine ⟨lt_of_lt_of_le (Nat.pow_pos (by decide)) yl,?_⟩
  cases b <;> simp only [Agrees,curvature,Bool.false_eq_true,if_false,if_true] at hs ⊢
  · exact factor_compare sep (by omega) xu zu yl yl
  · exact factor_compare sep (by omega) yu yu xl zl

/-- One fixed weighted core supplies both the bounded witness and the limiting family. -/
theorem bounded_witness_and_limits (word : List Bool) :
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
      (∀ K : Nat, ∃ P, ∀ p ≥ P, ∀ (i : Nat) (b : Bool), word[i]?=some b →
        let A := coeff c p
        0 < A (i+1) ∧
        (if b then K*(A (i+1)*A (i+1)) < A i*A (i+2)
         else K*(A i*A (i+2)) < A (i+1)*A (i+1))) := by
  obtain ⟨c,F,lip,cert,fits,hd,hW,_⟩ := bounded_word word
  exact ⟨c,bounded_instance cert fits (Nat.le_refl _) hd hW,
    fun p => ⟨Geometry.acyclic c p,Geometry.diameter_ten c p,Geometry.perfect_matching _,Geometry.independence_number _⟩,
    ratio_thresholds cert fits (Nat.le_refl _)⟩

end Quantitative
end TerminalCurvature
