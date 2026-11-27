import FormalConjectures.ErdosProblems.«556»

-- Lower-bound construction of Benevides and Skokan (2009), doi:10.1016/j.jctb.2008.12.002.
-- Formalization on the branch of @ardagemci.
namespace Erdos556Construction

-- The first four labels are the ordinary blocks. The last three are singleton hubs.
def hub (c : Fin 3) : Fin 7 := ⟨4 + c.val, by omega⟩

def edgeColor (a b : Fin 7) : Fin 3 :=
  if 4 ≤ max a.val b.val then ⟨(max a.val b.val - 4) % 3, Nat.mod_lt _ (by decide)⟩
  else if a.val / 2 = b.val / 2 then 0
  else if a.val % 2 = b.val % 2 then 1
  else 2

def side (c : Fin 3) (a : Fin 7) : Bool :=
  if c = 0 then decide (a.val < 2)
  else if c = 1 then decide (a.val % 2 = 0)
  else decide (a.val = 0 ∨ a.val = 3)

theorem color_symmetric : ∀ a b, edgeColor a b = edgeColor b a := by decide

-- Any neighbor of a different-colored hub along a c-edge is the unique c-hub.
theorem foreign_hub_neighbor : ∀ (c : Fin 3) (a b : Fin 7),
    4 ≤ a.val → a ≠ hub c → a ≠ b → edgeColor a b = c → b = hub c := by decide

theorem ordinary_edge_preserves_side : ∀ (c : Fin 3) (a b : Fin 7),
    a.val < 4 → b.val < 4 → edgeColor a b = c → side c a = side c b := by decide

theorem blocks_per_side : ∀ (c : Fin 3) (s : Bool),
    (Finset.univ.filter (fun a : Fin 4 => side c ⟨a.val, by omega⟩ = s)).card = 2 := by decide

-- Once the hub is removed, a path of ordinary vertices stays on one side.
theorem path_stays_on_side (c : Fin 3) (v : ℕ → Fin 7) (t : ℕ)
    (ordinary : ∀ i ≤ t, (v i).val < 4)
    (edges : ∀ i < t, edgeColor (v i) (v (i + 1)) = c) :
    side c (v 0) = side c (v t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    exact (ih (fun i hi => ordinary i (by omega)) (fun i hi => edges i (by omega))).trans
      (ordinary_edge_preserves_side c _ _ (ordinary t (by omega))
        (ordinary (t + 1) (by omega)) (edges t (by omega)))

def blockLabel (a : Fin 4) : Fin 7 := ⟨a.val, by omega⟩

-- Deleting a hub from a putative cycle leaves 2m+1 distinct ordinary vertices
-- when each block has size m and the required cycle length is 2m+2.
theorem no_long_ordinary_path (m : ℕ) (c : Fin 3)
    (v : Fin (2 * m + 1) → Fin 4 × Fin m) (hinj : Function.Injective v)
    (edges : ∀ i : Fin (2 * m),
      edgeColor (blockLabel (v i.castSucc).1) (blockLabel (v i.succ).1) = c) : False := by
  let s := side c (blockLabel (v 0).1)
  have hs (i : Fin (2 * m + 1)) : side c (blockLabel (v i).1) = s := by
    induction i using Fin.induction with
    | zero => rfl
    | succ j ih =>
      exact (ordinary_edge_preserves_side c _ _ (v j.castSucc).1.isLt
        (v j.succ).1.isLt (edges j)).symm.trans ih
  let encode (i : Fin (2 * m + 1)) :
      {a : Fin 4 // side c (blockLabel a) = s} × Fin m :=
    (⟨(v i).1, hs i⟩, (v i).2)
  have hi : Function.Injective encode := by
    intro i j hij
    apply hinj
    have h₁ := congrArg (fun x : {a : Fin 4 // side c (blockLabel a) = s} × Fin m => x.1.val) hij
    have h₂ := congrArg (fun x : {a : Fin 4 // side c (blockLabel a) = s} × Fin m => x.2) hij
    exact Prod.ext h₁ h₂
  have hc := Fintype.card_le_of_injective encode hi
  have hb : Fintype.card {a : Fin 4 // side c (blockLabel a) = s} = 2 := by
    have count : ∀ (d : Fin 3) (b : Bool),
        Fintype.card {a : Fin 4 // side d (blockLabel a) = b} = 2 := by decide
    exact count c s
  simp only [Fintype.card_fin, Fintype.card_prod, hb] at hc
  omega

def vertexLabel {m : ℕ} : (Fin 4 × Fin m) ⊕ Fin 3 → Fin 7
  | .inl v => blockLabel v.1
  | .inr c => hub c

theorem eq_of_hub_label {m : ℕ} (c : Fin 3) (w : (Fin 4 × Fin m) ⊕ Fin 3)
    (h : vertexLabel w = hub c) : w = .inr c := by
  cases w with
  | inl a =>
    have hv := congrArg Fin.val h
    change a.1.val = 4 + c.val at hv
    have := a.1.isLt
    omega
  | inr d =>
    have hv := congrArg Fin.val h
    change 4 + d.val = 4 + c.val at hv
    exact congrArg Sum.inr (Fin.ext (by omega))

-- An injective cyclic enumeration with all consecutive edges of one color is impossible.
theorem no_mono_cycle (m : ℕ) (hm : 0 < m) (c : Fin 3)
    (v : Fin (2*m+2) → (Fin 4 × Fin m) ⊕ Fin 3) (hinj : Function.Injective v)
    (edges : ∀ i, edgeColor (vertexLabel (v i)) (vertexLabel (v (i+1))) = c) : False := by
  classical
  have two_ne : (1 + 1 : Fin (2*m+2)) ≠ 0 := by
    intro h
    have e := congrArg Fin.val h
    simp [Fin.val_add, Nat.mod_eq_of_lt (show 2 < 2*m+2 by omega)] at e
  have allowed (i : Fin (2*m+2)) (d : Fin 3) (hd : v i = .inr d) : d = c := by
    by_contra hdc
    have hdiff : hub d ≠ hub c := by
      intro h
      apply hdc
      apply Fin.ext
      have hv := congrArg Fin.val h
      change 4 + d.val = 4 + c.val at hv
      omega
    have only (j : Fin (2*m+2)) (hne : j ≠ i)
        (he : edgeColor (hub d) (vertexLabel (v j)) = c) : v j = .inr c := by
      apply eq_of_hub_label
      apply foreign_hub_neighbor c (hub d) _ (by change 4 ≤ 4 + d.val; omega) hdiff _ he
      intro h
      exact hne (hinj ((eq_of_hub_label d _ h.symm).trans hd.symm))
    have after : v (i+1) = .inr c := by
      apply only (i+1) (by simp)
      simpa [hd, vertexLabel] using edges i
    have before : v (i-1) = .inr c := by
      apply only (i-1) (by simp)
      rw [color_symmetric]
      simpa [hd, vertexLabel] using edges (i-1)
    have h := hinj (before.trans after.symm)
    have h' := congrArg (fun x => x + 1) h
    apply two_ne
    have he : i + 0 = i + (1 + 1) := by simpa [add_assoc] using h'
    exact (add_left_cancel he).symm
  obtain ⟨p, hp⟩ : ∃ p : Fin (2*m+2), (∃ j, v j = .inr c) → v p = .inr c := by
    by_cases he : ∃ j, v j = .inr c
    · exact ⟨he.choose, fun _ => he.choose_spec⟩
    · exact ⟨0, fun h => (he h).elim⟩
  let pos (i : Fin (2*m+1)) : Fin (2*m+2) := p + i.succ
  have ordinary (i : Fin (2*m+1)) : ∃ w, v (pos i) = .inl w := by
    cases e : v (pos i) with
    | inl w => exact ⟨w, rfl⟩
    | inr d =>
      have hdc := allowed _ _ e
      subst d
      have h := hinj (e.trans (hp ⟨_, e⟩).symm)
      have hz : i.succ = 0 := by simpa only [pos, add_eq_left] using h
      exact (Fin.succ_ne_zero _ hz).elim
  choose w hw using ordinary
  apply no_long_ordinary_path m c w
  · intro a b h
    have hpos := hinj ((hw a).trans ((congrArg Sum.inl h).trans (hw b).symm))
    exact Fin.succ_injective _ (add_left_cancel hpos)
  · intro j
    have step : pos j.succ = pos j.castSucc + 1 := by
      dsimp [pos]
      rw [add_assoc p j.castSucc.succ 1]
      apply congrArg (p + ·)
      apply Fin.ext
      simp [Fin.val_add, Fin.val_one, Nat.mod_eq_of_lt (show j.val+1+1 < 2*m+2 by omega)]
    have e := edges (pos j.castSucc)
    rw [← step, hw, hw] at e
    exact e

end Erdos556Construction

namespace Erdos556Construction
open SimpleGraph
open scoped SimpleGraph

-- Reused from OMA.oddCycleRamseySetNonempty in the project's odd lower-bound proof.
-- Its argument establishes finiteness for every cycle length.
lemma cycleRamseySetNonempty (n : ℕ) :
    {N : ℕ | ∀ c : Fin 3 → SimpleGraph (Fin N),
      (⊤ : SimpleGraph (Fin N)).IsEdgeColouring c →
        ∃ i, (cycleGraph n).IsContained (c i)}.Nonempty := by
  classical
  let M := Nat.choose (n + n) n
  let N := Nat.choose (M + n) M
  refine ⟨N, ?_⟩
  intro c hc
  let test (i : Fin 3) (S : Finset (Fin N)) : Bool :=
    decide (∀ a ∈ S, ∀ b ∈ S, a ≠ b → (c i).Adj a b)
  have test_pair (i : Fin 3) (a b : Fin N) (hab : a ≠ b) :
      test i {a, b} = true ↔ (c i).Adj a b := by
    simp only [test, decide_eq_true_eq]
    constructor
    · intro h
      exact h a (by simp) b (by simp) hab
    · intro h x hx y hy hxy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact (hxy rfl).elim
      · exact h
      · exact h.symm
      · exact (hxy rfl).elim
  have copy_of_clique (S : Finset (Fin N)) (hcard : S.card = n) (i : Fin 3)
      (h : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → (c i).Adj a b) :
      (cycleGraph n).IsContained (c i) := by
    let e := (Finset.equivFinOfCardEq hcard).symm
    let f : Fin n → Fin N := fun x => (e x).val
    have hf : Function.Injective f := Subtype.val_injective.comp e.injective
    refine ⟨⟨⟨f, ?_⟩, hf⟩⟩
    intro a b hab
    exact h (f a) (e a).property (f b) (e b).property (hf.ne hab.ne)
  have adjacency_exists (a b : Fin N) (hab : a ≠ b) : ∃ i, (c i).Adj a b := by
    apply iSup_adj.mp
    rw [← hc.1]
    exact (top_adj a b).mpr hab
  have pair_subset (S : Finset (Fin N)) {a b : Fin N} (ha : a ∈ S) (hb : b ∈ S) :
      {a, b} ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  rcases Combinatorics.Diagonal.hasRamseyProperty_choose M n (test 0) Finset.univ
      (by simp [N]) with ⟨S, _, hS, hSmono⟩ | ⟨S, _, hS, hSmono⟩
  · rcases Combinatorics.Diagonal.hasRamseyProperty_choose n n (test 1) S
        (by rw [hS]) with ⟨T, hTS, hT, hTmono⟩ | ⟨T, _, hT, hTmono⟩
    · refine ⟨2, copy_of_clique T hT 2 ?_⟩
      intro a ha b hb hab
      have hpair := Finset.card_pair_eq_two_iff.mpr hab
      have hzero : ¬ (c 0).Adj a b := by
        intro h
        have ht := (test_pair 0 a b hab).mpr h
        rw [hSmono _ (pair_subset S (hTS ha) (hTS hb)) hpair] at ht
        contradiction
      have hone : ¬ (c 1).Adj a b := by
        intro h
        have ht := (test_pair 1 a b hab).mpr h
        rw [hTmono _ (pair_subset T ha hb) hpair] at ht
        contradiction
      obtain ⟨i, hi⟩ := adjacency_exists a b hab
      fin_cases i
      · exact (hzero hi).elim
      · exact (hone hi).elim
      · exact hi
    · refine ⟨1, copy_of_clique T hT 1 ?_⟩
      intro a ha b hb hab
      exact (test_pair 1 a b hab).mp
        (hTmono _ (pair_subset T ha hb) (Finset.card_pair_eq_two_iff.mpr hab))
  · refine ⟨0, copy_of_clique S hS 0 ?_⟩
    intro a ha b hb hab
    exact (test_pair 0 a b hab).mp
      (hSmono _ (pair_subset S ha hb) (Finset.card_pair_eq_two_iff.mpr hab))

theorem bad_three_coloring (m N : ℕ) (hm : 0 < m) (hN : N ≤ 4*m+3) :
    ∃ c : Fin 3 → SimpleGraph (Fin N),
      (⊤ : SimpleGraph (Fin N)).IsEdgeColouring c ∧
        ∀ i, ¬ (cycleGraph (2*m+2)).IsContained (c i) := by
  classical
  obtain ⟨e⟩ : Nonempty (Fin N ↪ (Fin 4 × Fin m) ⊕ Fin 3) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hN)
  let label (x : Fin N) := vertexLabel (e x)
  let c (i : Fin 3) : SimpleGraph (Fin N) :=
    { Adj := fun x y => x ≠ y ∧ edgeColor (label x) (label y) = i
      symm := ⟨fun x y h => ⟨h.1.symm, (color_symmetric _ _).trans h.2⟩⟩
      loopless := ⟨fun _ h => h.1 rfl⟩ }
  refine ⟨c, ⟨?_, ?_⟩, ?_⟩
  · ext x y
    rw [top_adj, iSup_adj]
    exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨_, h⟩ => h.1⟩
  · intro i j hij
    apply disjoint_iff_inf_le.mpr
    intro x y h
    exact (hij (h.1.2.symm.trans h.2.2)).elim
  · intro i ⟨f⟩
    apply no_mono_cycle m hm i (fun a => e (f a)) (e.injective.comp f.injective)
    intro a
    have ha : (cycleGraph (2*m+2)).Adj a (a+1) :=
      cycleGraph_adj.mpr (Or.inr (by simp))
    exact (f.toHom.map_adj ha).2

theorem even_cycle_ramsey_lower (n : ℕ) (hn : 4 ≤ n) (he : Even n) :
    2 * n ≤ multicolourRamsey (cycleGraph n) 3 := by
  obtain ⟨k, hk⟩ := he
  let m := k-1
  have hm : 0 < m := by dsimp [m]; omega
  have hlen : n = 2*m+2 := by dsimp [m]; omega
  rw [hlen]
  let S : Set ℕ := {N | ∀ c : Fin 3 → SimpleGraph (Fin N),
    (⊤ : SimpleGraph (Fin N)).IsEdgeColouring c →
      ∃ i, (cycleGraph (2*m+2)).IsContained (c i)}
  have hS : sInf S ∈ S := Nat.sInf_mem (cycleRamseySetNonempty (2*m+2))
  by_contra! h
  change sInf S < 2 * (2*m+2) at h
  obtain ⟨c, hc, hno⟩ := bad_three_coloring m (sInf S) hm (by omega)
  obtain ⟨i, hi⟩ := hS c hc
  exact hno i hi

end Erdos556Construction

theorem OMA.solution : type_of% @Erdos556.erdos_556.variants.benevides_skokan_large_even := by
  sorry
