import Family
import Mathlib.Data.Finset.Max

/-! A rooted parent certificate proves acyclicity and the diameter bound on the
same vertex and edge types used for the cardinalities in Family. -/
namespace TerminalCurvature
namespace Geometry
noncomputable section
open Assembly Counting Family

/-- Each nonsource core component has a hub, and every internal arrow runs
    from an arm to its unique hub. A balanced singleton is also a hub. -/
structure Hubs (g : Model) where
  hub : g.V → g.V
  isHub : ∀ i, g.incomingFromSource (hub i)=true
  internal : ∀ i j, g.edge i j ↔ g.incomingFromSource i=false ∧ hub i=j

private def sumHubs {g k : Model} (h : Hubs g) (t : Hubs k) : Hubs (union g k) where
  hub := Sum.map h.hub t.hub
  isHub := by intro i; cases i with | inl i => exact h.isHub i | inr i => exact t.isHub i
  internal := by
    intro i j; cases i <;> cases j <;> simp [union,h.internal,t.internal]

private def starHubs (s B b : Nat) : Hubs (star s B b) where
  hub := fun _ => .inl ()
  isHub := fun _ => rfl
  internal := by intro i j; cases i <;> cases j <;> simp [star]

private def starsHubs (B : Nat) (f : Nat → Nat) : (ss : List Nat) → Hubs (stars B f ss)
  | [] => ⟨Empty.elim,(fun i => nomatch i),(fun i => nomatch i)⟩
  | s::ss => sumHubs (starHubs s B (f s)) (starsHubs B f ss)

def hubs : (c : Device) → Hubs (model c)
  | .stars h B f => starsHubs B f (List.range' 1 h)
  | .balanced w c => sumHubs (g:=single w) ⟨id,fun _ => rfl,by intro i j; simp [single]⟩ (hubs c)

theorem adj_symm {I : Type} {ar : I → I → Prop} {u v : I×Bool} : Adj ar u v → Adj ar v u := by
  rintro (⟨h,ne⟩|h|h)
  · exact Or.inl ⟨h.symm,Ne.symm ne⟩
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

private def center (g : Model) : (root g).V×Bool := (.inl (),true)
private def baseLevel (g : Model) : (root g).V×Bool → Nat
  | (.inl _,b) => if b then 0 else 1
  | (.inr v,b) => if b then 2 else if g.incomingFromSource v then 1 else 3
private def baseUp {g : Model} (h : Hubs g) : (root g).V×Bool → (root g).V×Bool
  | (.inl _,_) => center g
  | (.inr v,true) => if g.incomingFromSource v then (.inr v,false) else (.inr (h.hub v),false)
  | (.inr v,false) => if g.incomingFromSource v then center g else (.inr v,true)

/-- Every edge is directed towards the unique parent of its deeper endpoint. -/
def Oriented {V : Type} (lev : V → Nat) (up : V → V) (u v : V) : Prop :=
  (up u=v ∧ lev v<lev u) ∨ (up v=u ∧ lev u<lev v)

private theorem orient_symm {V : Type} {lev : V → Nat} {up : V → V} {u v : V}
    (h : Oriented lev up u v) : Oriented lev up v u := h.symm

private theorem base_step {g : Model} (h : Hubs g) (u : (root g).V×Bool) (hn : u≠center g) :
    Adj (root g).edge u (baseUp h u) ∧ baseLevel g (baseUp h u)+1=baseLevel g u := by
  rcases u with ⟨i,b⟩; cases i with
  | inl z => cases z; cases b <;> simp_all [center,baseUp,baseLevel,Adj]
  | inr v =>
    have arrow := (h.internal v (h.hub v)).mpr
    have hh := h.isHub v
    cases hb : g.incomingFromSource v <;> cases b <;>
      simp_all [Adj,baseUp,baseLevel,center,root]

private theorem base_pair {g : Model} (h : Hubs g) (i : (root g).V) :
    Oriented (baseLevel g) (baseUp h) (i,true) (i,false) := by
  cases i with
  | inl u => cases u; simp [Oriented,baseLevel,baseUp,center]
  | inr v => cases hb : g.incomingFromSource v <;> simp [Oriented,baseUp,baseLevel,hb]

private theorem base_arrow {g : Model} (h : Hubs g) (i j : (root g).V) (e : (root g).edge i j) :
    Oriented (baseLevel g) (baseUp h) (i,true) (j,false) := by
  cases i with
  | inl z =>
    cases z; cases j with
    | inl k => contradiction
    | inr v => change g.incomingFromSource v=true at e; simp [Oriented,baseLevel,baseUp,e,center]
  | inr u =>
    cases j with
    | inl k => contradiction
    | inr v =>
      obtain ⟨hneg,rfl⟩ := (h.internal _ _).mp e
      simp [Oriented,baseLevel,baseUp,hneg,h.isHub]

def vertexCenter (c : Device) (p : Nat) : Labels c p × Bool := (.inl (.inl ()),true)
def level (c : Device) (p : Nat) : Labels c p × Bool → Nat
  | (.inl i,b) => baseLevel (model c) (i,b)
  | (.inr l,b) => baseLevel (model c) (parent l,out l)+(if b=out l then 2 else 1)
def up (c : Device) (p : Nat) : Labels c p × Bool → Labels c p × Bool
  | (.inl i,b) => let x := baseUp (hubs c) (i,b); (.inl x.1,x.2)
  | (.inr l,b) => if b=out l then (.inr l,!b) else (.inl (parent l),out l)

private theorem lift_edge {c : Device} {p : Nat} (i j : (root (model c)).V) (b k : Bool)
    (h : Adj (root (model c)).edge (i,b) (j,k)) : Adj (arrows c p) (.inl i,b) (.inl j,k) := by
  rcases h with ⟨e,n⟩|⟨hb,hk,e⟩|⟨hk,hb,e⟩
  · exact Or.inl ⟨congrArg Sum.inl e,n⟩
  · exact Or.inr (Or.inl ⟨hb,hk,.core e⟩)
  · exact Or.inr (Or.inr ⟨hk,hb,.core e⟩)

private theorem lift_oriented {c : Device} {p : Nat} (i j : (root (model c)).V) (b k : Bool)
    (h : Oriented (baseLevel (model c)) (baseUp (hubs c)) (i,b) (j,k)) :
    Oriented (level c p) (up c p) (.inl i,b) (.inl j,k) := by
  rcases h with ⟨he,hl⟩|⟨he,hl⟩
  · exact Or.inl ⟨by simp [up,he],hl⟩
  · exact Or.inr ⟨by simp [up,he],hl⟩

private theorem leaf_edge (c : Device) (p : Nat) (l : Leaves (root (model c)) p) :
    Adj (arrows c p) (.inr l,!(out l)) (.inl (parent l),out l) := by
  cases ho : out l with
  | true => exact Or.inr (Or.inr ⟨rfl,rfl,.outgoing _ ho⟩)
  | false => exact Or.inr (Or.inl ⟨rfl,rfl,.incoming _ ho⟩)

theorem parent_step (c : Device) (p : Nat) (u : Labels c p×Bool) (hn : u≠vertexCenter c p) :
    Adj (arrows c p) u (up c p u) ∧ level c p (up c p u)+1=level c p u := by
  rcases u with ⟨i,b⟩; cases i with
  | inl i =>
    have hne : (i,b)≠center (model c) := by
      intro he; apply hn; exact congrArg (fun x : (root (model c)).V×Bool => (Sum.inl x.1,x.2)) he
    obtain ⟨he,hd⟩ := base_step (hubs c) _ hne
    exact ⟨lift_edge _ _ _ _ he,hd⟩
  | inr l =>
    have he := leaf_edge c p l
    cases hb : out l <;> cases b <;> simp_all [up,level,Adj]

private theorem physical_pair (c : Device) (p : Nat) (i : Labels c p) :
    Oriented (level c p) (up c p) (i,true) (i,false) := by
  cases i with
  | inl i => exact lift_oriented _ _ _ _ (base_pair (hubs c) i)
  | inr l => cases hb : out l <;> simp [Oriented,up,level,hb]

private theorem physical_arrow {c : Device} {p : Nat} (i j : Labels c p) (he : arrows c p i j) :
    Oriented (level c p) (up c p) (i,true) (j,false) := by
  cases he with
  | core hh => exact lift_oriented _ _ _ _ (base_arrow (hubs c) _ _ hh)
  | outgoing l ho => simp [Oriented,up,level,ho]
  | incoming l ho => simp [Oriented,up,level,ho]

theorem parent_orientation (c : Device) (p : Nat) (u v : Labels c p×Bool) (e : Adj (arrows c p) u v) :
    Oriented (level c p) (up c p) u v := by
  rcases u with ⟨i,b⟩; rcases v with ⟨j,k⟩
  rcases e with ⟨hij,hne⟩|⟨hb,hk,he⟩|⟨hk,hb,he⟩
  · change i=j at hij; subst j; cases b <;> cases k <;> try contradiction
    · exact orient_symm (physical_pair c p i)
    · exact physical_pair c p i
  · change b=true at hb; change k=false at hk; subst b; subst k; exact physical_arrow _ _ he
  · change k=true at hk; change b=false at hb; subst b; subst k; exact orient_symm (physical_arrow _ _ he)

theorem level_le (c : Device) (p : Nat) (u : Labels c p×Bool) : level c p u ≤ 5 := by
  have h (i : (root (model c)).V) (b : Bool) : baseLevel (model c) (i,b)≤3 := by
    cases i with
    | inl z => cases b <;> simp [baseLevel]
    | inr v => cases b <;> cases hb : (model c).incomingFromSource v <;> simp [baseLevel,hb]
  rcases u with ⟨i,b⟩; cases i with
  | inl i => exact (h i b).trans (by decide)
  | inr l => have hb := h (parent l) (out l); simp only [level]; split <;> omega

/-- An actual walk with exactly the indicated number of edges. -/
inductive Walk {V : Type} (adj : V → V → Prop) : V → V → Nat → Prop
| nil (v) : Walk adj v v 0
| cons {a b c n} (ab : adj a b) (bc : Walk adj b c n) : Walk adj a c (n+1)

private theorem walk_append {V : Type} {adj : V → V → Prop} {a b c n k}
    (ab : Walk adj a b n) (bc : Walk adj b c k) : Walk adj a c (k+n) := by
  induction ab with
  | nil => simpa using bc
  | cons he _ ih => exact Walk.cons he (ih bc)

private theorem walk_reverse {I : Type} {ar : I → I → Prop} {a b n}
    (ab : Walk (Adj ar) a b n) : Walk (Adj ar) b a n := by
  induction ab with
  | nil => exact Walk.nil _
  | cons he _ ih => simpa [Nat.add_comm] using walk_append ih (Walk.cons (adj_symm he) (Walk.nil _))

private theorem to_center (c : Device) (p : Nat) (u : Labels c p×Bool) :
    Walk (Adj (arrows c p)) u (vertexCenter c p) (level c p u) := by
  generalize he : level c p u=n
  induction n generalizing u with
  | zero =>
    by_cases h : u=vertexCenter c p
    · subst u; exact Walk.nil _
    · have hh := (parent_step c p u h).2; omega
  | succ n ih =>
    have h : u≠vertexCenter c p := by rintro rfl; change 0=n+1 at he; omega
    obtain ⟨ha,hl⟩ := parent_step c p u h
    exact Walk.cons ha (ih _ (by omega))

theorem diameter_ten (c : Device) (p : Nat) (u v : Labels c p×Bool) :
    ∃ n, n≤10 ∧ Walk (Adj (arrows c p)) u v n := by
  exact ⟨_,by have := level_le c p u; have := level_le c p v; omega,
    walk_append (to_center c p u) (walk_reverse (to_center c p v))⟩

/-- Every nonempty finite vertex set has a vertex with at most one neighbor in
that set. Taking the vertices of any simple cycle shows this excludes all cycles. -/
def Forest {V : Type} (adj : V → V → Prop) : Prop :=
  ∀ s : Finset V, s.Nonempty → ∃ u ∈ s, ∀ v ∈ s, ∀ w ∈ s, adj u v → adj u w → v=w

theorem acyclic (c : Device) (p : Nat) : Forest (Adj (arrows c p)) := by
  classical
  intro s hn
  obtain ⟨u,hu,high⟩ := Finset.exists_max_image s (level c p) hn
  refine ⟨u,hu,?_⟩
  intro v hv w hw he hf
  have parent (x) (hx : x∈s) (e : Adj (arrows c p) u x) : up c p u=x := by
    rcases parent_orientation c p _ _ e with ⟨h,_⟩|⟨_,h⟩
    · exact h
    · have := high x hx; omega
  exact (parent _ hv he).symm.trans (parent _ hw hf)

def mate {I : Type} (x : I×Bool) : I×Bool := (x.1,!x.2)

theorem perfect_matching {I : Type} (ar : I → I → Prop) (x : I×Bool) :
    mate (mate x)=x ∧ mate x≠x ∧ Adj ar x (mate x) := by
  rcases x with ⟨i,b⟩; cases b <;> simp [mate,Adj]

/-- The exact value of alpha, as an upper bound for every independent set
    and a witness attained by the set of positive endpoints. -/
theorem independence_number {I : Type} [Fintype I] (ar : I → I → Prop) :
    (∀ S : Finset (I×Bool), Independent ar (fun x => x∈S) → S.card≤Fintype.card I) ∧
    ∃ S : Finset (I×Bool), Independent ar (fun x => x∈S) ∧ S.card=Fintype.card I := by
  classical
  constructor
  · intro S hi
    let a := markOf (fun x => x∈S)
    have he : selected a=(fun x => x∈S) := selected_mark _ hi
    have hc : chosen a=S := by ext x; rw [mem_chosen,he]
    have hh := chosen_card a; rw [hc] at hh; omega
  · let a : I→Mark := fun _ => .pos
    refine ⟨chosen a,?_,?_⟩
    · have hl : Legal ar a := by intro _ _ _ _ hn; contradiction
      simpa only [mem_chosen] using (legal_iff_independent ar a).mp hl
    · have hh := chosen_card a
      have hz : holes a=∅ := by ext i; simp [a]
      simpa [hz] using hh

/-- Graph-theoretic realization of every sign word, on the same graph used for
acyclicity, bounded diameter, the matching and the independence number. -/
theorem matched_tree_every_word (word : List Bool) :
    ∃ c : Device, ∃ p : Nat, 0<p ∧ SignedCounts (coeff c p) word ∧
      Forest (Adj (arrows c p)) ∧
      (∀ u v, ∃ n, n≤10 ∧ Walk (Adj (arrows c p)) u v n) ∧
      (∀ u, mate (mate u)=u ∧ mate u≠u ∧ Adj (arrows c p) u (mate u)) ∧
      (∀ S : Finset (Labels c p×Bool), Independent (arrows c p) (fun x => x∈S) →
         S.card≤Fintype.card (Labels c p)) ∧
      (∃ S : Finset (Labels c p×Bool), Independent (arrows c p) (fun x => x∈S) ∧
         S.card=Fintype.card (Labels c p)) := by
  obtain ⟨c,p,hh,hw⟩ := physical_every_word word
  exact ⟨c,p,hh,hw,acyclic c p,diameter_ten c p,perfect_matching _,independence_number _⟩

end
end Geometry
end TerminalCurvature
