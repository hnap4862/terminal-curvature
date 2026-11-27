import TerminalCurvature
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Actual finite cardinalities for the split graph of a leaf-decorated oriented core.
Types C and L are the core and the already-replicated leaves. This module does not
assume any numerical coefficient envelopes. -/
set_option linter.unusedSectionVars false

namespace TerminalCurvature
namespace Counting
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable

instance : Fintype Mark where
  elems := {.pos,.neg,.hole}
  complete a := by cases a <;> simp

variable {I C L : Type} [Fintype I] [Fintype C] [Fintype L]
variable [DecidableEq I] [DecidableEq C] [DecidableEq L]

def holes (a : I → Mark) := Finset.univ.filter (fun i => a i = .hole)

def chosen (a : I → Mark) : Finset (I × Bool) := Finset.univ.filter (selected a)

@[simp] theorem mem_holes (a : I → Mark) (i : I) : i ∈ holes a ↔ a i = .hole := by simp [holes]
@[simp] theorem mem_chosen (a : I → Mark) (v : I × Bool) : v ∈ chosen a ↔ selected a v := by simp [chosen]

def plusBit : Mark → Bool | .pos => true | _ => false

def occupiedEquiv (a : I → Mark) : ↥(chosen a) ≃ ↥(Finset.univ.filter (fun i => a i ≠ .hole)) where
  toFun x := ⟨x.1.1, by
    rcases x with ⟨⟨i,b⟩,hx⟩
    have hx' := (Finset.mem_filter.mp hx).2
    cases b <;> cases hm : a i <;> simp_all [selected]⟩
  invFun i := ⟨(i.val,plusBit (a i.val)), by
    rcases i with ⟨i,hi⟩; have hi' := (Finset.mem_filter.mp hi).2
    cases hm : a i <;> simp_all [plusBit,selected]⟩
  left_inv x := by
    rcases x with ⟨⟨i,b⟩,hx⟩; have hx' := (Finset.mem_filter.mp hx).2; apply Subtype.ext
    cases b <;> cases hm : a i <;> simp_all [selected,plusBit]
  right_inv _ := rfl

theorem chosen_card (a : I → Mark) : (chosen a).card + (holes a).card = Fintype.card I := by
  have h := Fintype.card_congr (occupiedEquiv a)
  simp only [Fintype.card_coe] at h
  have hh := (Finset.univ : Finset I).filter_card_add_filter_neg_card_eq_card (fun i => a i = .hole)
  change (holes a).card + (Finset.univ.filter (fun i => ¬a i = .hole)).card = _ at hh
  rw [h, Nat.add_comm, hh, Finset.card_univ]

abbrev Config (ar : I → I → Prop) (r : Nat) :=
  {a : I → Mark // Legal ar a ∧ (holes a).card=r}

abbrev PhysicalLayer (ar : I → I → Prop) (r : Nat) :=
  {S : Finset (I × Bool) // Independent ar (fun v => v ∈ S) ∧ S.card+r=Fintype.card I}

def layerEquiv (ar : I → I → Prop) (r : Nat) : Config ar r ≃ PhysicalLayer ar r where
  toFun a := ⟨chosen a.1, by
    constructor
    · simpa only [mem_chosen] using (legal_iff_independent ar a.1).mp a.2.1
    · simpa only [a.2.2] using chosen_card a.1⟩
  invFun s := by
    let a := markOf (fun x => x ∈ s.val)
    have he : selected a = (fun x => x ∈ s.val) := selected_mark _ s.2.1
    have hh : chosen a = s.1 := by ext x; rw [mem_chosen,he]
    refine ⟨a, (legal_iff_independent ar a).mpr (by rw [he]; exact s.2.1), ?_⟩
    have h := chosen_card a; rw [hh] at h; have h' := s.2.2; omega
  left_inv a := by
    apply Subtype.ext
    change markOf (fun x => x ∈ chosen a.1) = a.1
    have hh : (fun x => x ∈ chosen a.1) = selected a.1 := by funext x; exact propext (mem_chosen _ _)
    rw [hh, mark_selected]
  right_inv s := by
    apply Subtype.ext; ext x
    change x ∈ chosen (markOf (fun z => z ∈ s.val)) ↔ x ∈ s.val
    rw [mem_chosen, selected_mark _ s.2.1]

/-- Exactly the oriented core arrows and the single attachment arrow of each leaf. -/
inductive Attach (ar : C → C → Prop) (parent : L → C) (out : L → Bool) : C ⊕ L → C ⊕ L → Prop
  | core {c d} (edge : ar c d) : Attach ar parent out (.inl c) (.inl d)
  | outgoing (l) (dir : out l=true) : Attach ar parent out (.inl (parent l)) (.inr l)
  | incoming (l) (dir : out l=false) : Attach ar parent out (.inr l) (.inl (parent l))

def allowed (m : Mark) (out : Bool) (v : Mark) : Prop :=
  if out then ¬(m=.pos ∧ v=.neg) else ¬(v=.pos ∧ m=.neg)

def isFree (m : Mark) (out : Bool) : Prop := if out then m ≠ .pos else m ≠ .neg

def freeSet (parent : L → C) (out : L → Bool) (a : C → Mark) : Finset L :=
  Finset.univ.filter (fun l => isFree (a (parent l)) (out l))

@[simp] theorem free_mem (p : L → C) (o : L → Bool) (a : C → Mark) (l : L) :
    l ∈ freeSet p o a ↔ isFree (a (p l)) (o l) := by simp [freeSet]

theorem legal_attach {ar : C → C → Prop} {p : L → C} {o : L → Bool} {a : C ⊕ L → Mark} :
    Legal (Attach ar p o) a ↔ Legal ar (a ∘ Sum.inl) ∧
      ∀ l, allowed (a (.inl (p l))) (o l) (a (.inr l)) := by
  constructor
  · intro ha; constructor
    · intro c d e; exact ha _ _ (.core e)
    · intro l; cases h : o l with
      | true => simp only [allowed,if_true]; intro ⟨h₁,h₂⟩; exact ha _ _ (.outgoing l h) h₁ h₂
      | false => simp only [allowed,Bool.false_eq_true,if_false]; intro ⟨h₁,h₂⟩; exact ha _ _ (.incoming l h) h₁ h₂
  · rintro ⟨hc,hl⟩ i j e h₁ h₂
    cases e with
    | core e => exact hc _ _ e h₁ h₂
    | outgoing l h => have hh := hl l; simp [allowed,h,h₁,h₂] at hh
    | incoming l h => have hh := hl l; simp [allowed,h,h₁,h₂] at hh

private theorem leaf_unique {m a b : Mark} {o : Bool}
    (ha : allowed m o a) (hb : allowed m o b) (hz : a=.hole ↔ b=.hole)
    (hbit : isFree m o → plusBit a=plusBit b) : a=b := by
  cases o <;> cases m <;> cases a <;> cases b <;> simp_all [allowed,isFree,plusBit]

private theorem forced_allowed (m : Mark) (o : Bool) : allowed m o (if o then .pos else .neg) := by
  cases o <;> simp [allowed]

private theorem free_allowed {m : Mark} {o : Bool} (h : isFree m o) (v : Mark) : allowed m o v := by
  cases o <;> cases m <;> simp_all [isFree,allowed]

/-- A lower-bound injection. No leaf is empty in an image assignment. -/
def fill (p : L → C) (o : L → Bool) (a : C → Mark) (bits : ↥(freeSet p o a) → Bool) : C ⊕ L → Mark
  | .inl c => a c
  | .inr l => if h : l ∈ freeSet p o a then (if bits ⟨l,h⟩ then .pos else .neg)
               else (if o l then .pos else .neg)

private theorem fill_nonempty (p : L → C) (o : L → Bool) (a : C → Mark)
    (bits : ↥(freeSet p o a) → Bool) (l : L) : fill p o a bits (.inr l) ≠ .hole := by
  simp only [fill]; split <;> split <;> decide

private theorem fill_valid {ar : C → C → Prop} {p : L → C} {o : L → Bool} {a : C → Mark}
    (ha : Legal ar a) (bits : ↥(freeSet p o a) → Bool) : Legal (Attach ar p o) (fill p o a bits) := by
  apply legal_attach.mpr; refine ⟨ha,?_⟩; intro l
  simp only [fill]; split
  · rename_i h; exact free_allowed ((free_mem _ _ _ _).mp h) _
  · exact forced_allowed _ _

private theorem holes_fill (p : L → C) (o : L → Bool) (a : C → Mark)
    (bits : ↥(freeSet p o a) → Bool) :
    holes (fill p o a bits) = (holes a).map (Function.Embedding.inl (β:=L)) := by
  ext x; cases x with
  | inl c => simp [fill,Finset.mem_map]
  | inr l => simp [Finset.mem_map,fill_nonempty]

private theorem fill_inj (p : L → C) (o : L → Bool) (a : C → Mark) : Function.Injective (fill p o a) := by
  intro bits other hh; funext x
  have h := congrFun hh (Sum.inr x.val)
  simp [fill,x.property] at h
  cases a₁ : bits x <;> cases a₂ : other x <;> simp_all

theorem lower_count {ar : C → C → Prop} {p : L → C} {o : L → Bool} {r : Nat}
    (a : C → Mark) (ha : Legal ar a) (hr : (holes a).card=r) :
    2^(freeSet p o a).card ≤ Fintype.card (PhysicalLayer (Attach ar p o) r) := by
  classical
  let enc : (↥(freeSet p o a) → Bool) → Config (Attach ar p o) r :=
    fun bits => ⟨fill p o a bits, fill_valid ha bits, by rw [holes_fill,Finset.card_map,hr]⟩
  have inj : Function.Injective enc := fun _ _ hh => fill_inj p o a (congrArg Subtype.val hh)
  rw [← Fintype.card_congr (layerEquiv (Attach ar p o) r)]
  simpa only [Fintype.card_fun,Fintype.card_bool,Fintype.card_coe] using Fintype.card_le_of_injective enc inj

abbrev HoleSet (I : Type) [Fintype I] [DecidableEq I] (r : Nat) := ↥((Finset.univ : Finset I).powersetCard r)
abbrev Key (C L : Type) [Fintype C] [Fintype L] [DecidableEq C] [DecidableEq L] (r : Nat) :=
  HoleSet (C ⊕ L) r × (C → Bool)

private def key {r : Nat} {ar : C → C → Prop} {p : L → C} {o : L → Bool} (a : Config (Attach ar p o) r) : Key C L r :=
  (⟨holes a.val,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,a.property.2⟩⟩,fun c => plusBit (a.val (.inl c)))

private def decodeCore {r : Nat} (k : Key C L r) (c : C) : Mark :=
  if Sum.inl c ∈ k.1.val then .hole else if k.2 c then .pos else .neg

private theorem decode_key {r : Nat} {ar : C → C → Prop} {p : L → C} {o : L → Bool}
    (a : Config (Attach ar p o) r) : decodeCore (key a) = a.val ∘ Sum.inl := by
  funext c; cases h : a.val (.inl c) <;> simp [decodeCore,key,plusBit,h]

private theorem bound_holes_core (a : C ⊕ L → Mark) : (holes (a ∘ Sum.inl)).card ≤ (holes a).card := by
  apply Finset.card_le_card_of_injOn Sum.inl
  · intro c hc; simpa using hc
  · intro _ _ _ _ hh; exact Sum.inl.inj hh

private theorem fiber_injection {r : Nat} {ar : C → C → Prop} {p : L → C} {o : L → Bool}
    (k : Key C L r) :
    ∃ enc : {a : Config (Attach ar p o) r // key a=k} → (↥(freeSet p o (decodeCore k)) → Bool),
        Function.Injective enc := by
  let enc (x : {a : Config (Attach ar p o) r // key a=k}) :=
    fun l : ↥(freeSet p o (decodeCore k)) => plusBit (x.val.val (.inr l.val))
  refine ⟨enc, ?_⟩; intro x z he
  have cx := decode_key x.val; rw [x.property] at cx
  have cz := decode_key z.val; rw [z.property] at cz
  have hx : holes x.val.val = k.1.val := congrArg (fun t : Key C L r => t.1.val) x.property
  have hz : holes z.val.val = k.1.val := congrArg (fun t : Key C L r => t.1.val) z.property
  apply Subtype.ext; apply Subtype.ext; funext v
  cases v with
  | inl c => exact (congrFun cx c).symm.trans (congrFun cz c)
  | inr l =>
    have ax := (legal_attach.mp x.val.property.1).2 l
    have az := (legal_attach.mp z.val.property.1).2 l
    change allowed ((x.val.val ∘ Sum.inl) (p l)) (o l) _ at ax
    change allowed ((z.val.val ∘ Sum.inl) (p l)) (o l) _ at az
    rw [←cx] at ax; rw [←cz] at az
    apply leaf_unique ax az
    · rw [←mem_holes,←mem_holes,hx,hz]
    · intro fr; exact congrFun he ⟨l,(free_mem _ _ _ _).mpr fr⟩

theorem upper_count {ar : C → C → Prop} {p : L → C} {o : L → Bool} {r K : Nat}
    (upper : ∀ a : C → Mark, Legal ar a → (holes a).card ≤ r → (freeSet p o a).card ≤ K) :
    Fintype.card (PhysicalLayer (Attach ar p o) r) ≤
      (Fintype.card (C ⊕ L)).choose r * (2^Fintype.card C) * 2^K := by
  classical
  let fn := @key C L _ _ _ _ r ar p o
  let X := Config (Attach ar p o) r
  have fiber_bound (k : Key C L r) : Fintype.card {a : X // fn a=k} ≤ 2^K := by
    by_cases h : Nonempty {a : X // fn a=k}
    · obtain ⟨x⟩ := h
      have hc := decode_key x.val; rw [show key x.val=k from x.property] at hc
      have hzero := bound_holes_core x.val.val
      rw [x.val.property.2] at hzero
      have hfree : (freeSet p o (decodeCore k)).card ≤ K := by
        rw [hc]; exact upper _ (legal_attach.mp x.val.property.1).1 hzero
      obtain ⟨enc,hinj⟩ := fiber_injection (ar:=ar) (p:=p) (o:=o) k
      have hh := Fintype.card_le_of_injective enc hinj
      simp only [Fintype.card_fun,Fintype.card_bool,Fintype.card_coe] at hh
      exact le_trans hh (Nat.pow_le_pow_right (by decide) hfree)
    · haveI : IsEmpty {a : X // fn a=k} := not_nonempty_iff.mp h
      simp
  rw [← Fintype.card_congr (layerEquiv (Attach ar p o) r)]
  have he := Fintype.card_congr (Equiv.sigmaFiberEquiv fn)
  rw [Fintype.card_sigma] at he
  have hh := Finset.sum_le_card_nsmul (Finset.univ : Finset (Key C L r))
    (fun k => Fintype.card {a : X // fn a=k}) (2^K) (fun k _ => fiber_bound k)
  rw [←he]
  simpa only [Finset.card_univ,Key,Fintype.card_prod,HoleSet,Fintype.card_coe,
    Finset.card_powersetCard,Fintype.card_fun,Fintype.card_bool,nsmul_eq_mul] using hh

end
end Counting
end TerminalCurvature
