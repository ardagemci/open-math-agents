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
  have two_ne : (2 : Fin (2*m+2)) ≠ 0 := by
    intro h
    have e := congrArg Fin.val h
    simp [Fin.val_ofNat, Nat.mod_eq_of_lt (show 2 < 2*m+2 by omega)] at e
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
    simpa using (add_left_cancel he).symm
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
      have hz : i.succ = 0 := add_left_cancel (show p + i.succ = p + 0 by simpa [pos] using h)
      exact (Fin.succ_ne_zero _ hz).elim
  choose w hw using ordinary
  apply no_long_ordinary_path m c w
  · intro a b h
    have hpos := hinj ((hw a).trans ((congrArg Sum.inl h).trans (hw b).symm))
    exact Fin.succ_injective _ (add_left_cancel hpos)
  · intro j
    have step : pos j.succ = pos j.castSucc + 1 := by
      dsimp [pos]
      rw [add_assoc]
      congr 1
      apply Fin.ext
      simp [Fin.val_add, Fin.val_one, Nat.mod_eq_of_lt (show j.val+1+1 < 2*m+2 by omega)]
    have e := edges (pos j.castSucc)
    rw [← step, hw, hw] at e
    exact e

end Erdos556Construction

theorem OMA.solution : type_of% @Erdos556.erdos_556.variants.benevides_skokan_large_even := by
  sorry
