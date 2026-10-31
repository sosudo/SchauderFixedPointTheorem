import Mathlib
import Architect
set_option maxHeartbeats 4000000

/-- A saturated Boolean chain of n+1 elements contains exactly one set of
  each rank from 0 through n. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boolean_saturated_rank_cover {J : Type*} [Fintype J] [DecidableEq J]
    (T : Finset (Finset J))
    (hchain : ∀ a ∈ T, ∀ b ∈ T, a ⊆ b ∨ b ⊆ a)
    (hcard : T.card = Fintype.card J + 1) :
    T.image Finset.card = Finset.range (Fintype.card J + 1) := by
  classical
  have hinj : ∀ a ∈ T, ∀ b ∈ T, a.card = b.card → a = b := by
    intro a ha b hb hab
    rcases hchain a ha b hb with h | h
    · exact Finset.eq_of_subset_of_card_le h (le_of_eq hab.symm)
    · exact (Finset.eq_of_subset_of_card_le h (le_of_eq hab)).symm
  have hsub : T.image Finset.card ⊆ Finset.range (Fintype.card J + 1) := by
    intro k hk
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
    simp only [Finset.mem_range]
    have := Finset.card_le_univ a
    omega
  apply Finset.eq_of_subset_of_card_le hsub
  rw [Finset.card_range, Finset.card_image_iff.mpr hinj, hcard]

/-- Completing a facet to a saturated chain forces the missing rank. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boolean_missing_rank_forced {J : Type*} [Fintype J] [DecidableEq J]
    (F : Finset (Finset J)) (w : Finset J) (r : ℕ)
    (hr : r ≤ Fintype.card J)
    (hmissing : ∀ a ∈ F, a.card ≠ r)
    (hchain : ∀ a ∈ insert w F, ∀ b ∈ insert w F, a ⊆ b ∨ b ⊆ a)
    (hcard : (insert w F).card = Fintype.card J + 1) : w.card = r := by
  have hc := boolean_saturated_rank_cover (insert w F) hchain hcard
  have hrmem : r ∈ (insert w F).image Finset.card := by
    rw [hc, Finset.mem_range]
    omega
  obtain ⟨a, ha, har⟩ := Finset.mem_image.mp hrmem
  rcases Finset.mem_insert.mp ha with h | h
  · simpa [h] using har
  · exact False.elim (hmissing a h har)

/-- Every saturated finite Boolean chain has a monotone enumeration by rank. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boolean_saturated_chain_enumeration {J : Type*} [Fintype J] [DecidableEq J]
    (T : Finset (Finset J))
    (hchain : ∀ a ∈ T, ∀ b ∈ T, a ⊆ b ∨ b ⊆ a)
    (hcard : T.card = Fintype.card J + 1) :
    ∃ c : Fin (Fintype.card J + 1) → Finset J,
      Monotone c ∧ (∀ i, (c i).card = i.val) ∧ T = Finset.univ.image c := by
  classical
  have hr := boolean_saturated_rank_cover T hchain hcard
  have hex : ∀ i : Fin (Fintype.card J + 1), ∃ a ∈ T, a.card = i.val := by
    intro i
    have hm : i.val ∈ T.image Finset.card := by
      rw [hr, Finset.mem_range]
      exact i.isLt
    exact Finset.mem_image.mp hm
  choose c hc hcardc using hex
  refine ⟨c, ?_, hcardc, ?_⟩
  · intro i j hij
    rcases hchain (c i) (hc i) (c j) (hc j) with h | h
    · exact h
    · have hle : (c j).card ≤ (c i).card := Finset.card_le_card h
      rw [hcardc, hcardc] at hle
      have heq : i = j := Fin.ext (Nat.le_antisymm hij hle)
      subst j
      exact Finset.Subset.refl _
  · ext a
    constructor
    · intro ha
      have hi : a.card < Fintype.card J + 1 := by
        have := Finset.card_le_univ a
        omega
      let i : Fin (Fintype.card J + 1) := ⟨a.card, hi⟩
      have hca : c i = a := by
        rcases hchain (c i) (hc i) a ha with h | h
        · apply Finset.eq_of_subset_of_card_le h
          simp [hcardc, i]
        · symm
          apply Finset.eq_of_subset_of_card_le h
          simp [hcardc, i]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hca⟩
    · intro ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      exact hc i

open Finset

/-- Finite cubical chains: all graded monotone Boolean chains whose encoded
vertices obey the selected chamber predicate. The ambient finite lattice is
bounded coordinatewise by N. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
noncomputable def boundedChainSimplices {J : Type*} [Fintype J] [DecidableEq J]
    (N n : ℕ) (chamber : (J → Fin (N+1)) → Prop) :
    Finset (Finset (J → Fin (N+1))) := by
  classical
  exact univ.filter fun T => ∃ (y : J → ℕ) (c : Fin (n+1) → Finset J)
      (v : Fin (n+1) → (J → Fin (N+1))),
      Monotone c ∧ (∀ k, (c k).card = k.val) ∧
      (∀ k i, (v k i).val = y i + if i ∈ c k then 1 else 0) ∧
      (∀ k, chamber (v k)) ∧ T = univ.image v

/-- A simplex from the finite family has a bounded chain representation. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boundedChainSimplices_spec {J : Type*} [Fintype J] [DecidableEq J]
    (N n : ℕ) (chamber : (J → Fin (N+1)) → Prop)
    (T : Finset (J → Fin (N+1))) (hT : T ∈ boundedChainSimplices N n chamber) :
    ∃ (y : J → ℕ) (c : Fin (n+1) → Finset J)
      (v : Fin (n+1) → (J → Fin (N+1))),
      Monotone c ∧ (∀ k, (c k).card = k.val) ∧
      (∀ k i, (v k i).val = y i + if i ∈ c k then 1 else 0) ∧
      (∀ k, chamber (v k)) ∧ T = univ.image v := by
  classical
  simpa [boundedChainSimplices] using hT

/-- Vertices of every bounded-chain simplex satisfy the chamber condition and
lie in one common unit lattice cube. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boundedChainSimplices_cube {J : Type*} [Fintype J] [DecidableEq J]
    (N n : ℕ) (chamber : (J → Fin (N+1)) → Prop)
    (T : Finset (J → Fin (N+1))) (hT : T ∈ boundedChainSimplices N n chamber) :
    (∀ v ∈ T, chamber v) ∧
    ∃ y : J → ℕ, ∀ v ∈ T, ∀ i, y i ≤ (v i).val ∧ (v i).val ≤ y i + 1 := by
  classical
  obtain ⟨y, c, v, hc, hcard, hv, hch, rfl⟩ := boundedChainSimplices_spec N n chamber T hT
  constructor
  · intro w hw
    obtain ⟨k, _, rfl⟩ := mem_image.mp hw
    exact hch k
  · refine ⟨y, ?_⟩
    intro w hw i
    obtain ⟨k, _, rfl⟩ := mem_image.mp hw
    rw [hv]
    split_ifs <;> omega

/-- Distinct vertices of a simplex may be compared coordinatewise within one
unit, an input to the normalized simplex mesh estimate. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boundedChainSimplices_real_bound {J : Type*} [Fintype J] [DecidableEq J]
    (N n : ℕ) (chamber : (J → Fin (N+1)) → Prop)
    (T : Finset (J → Fin (N+1))) (hT : T ∈ boundedChainSimplices N n chamber)
    (v w : J → Fin (N+1)) (hv : v ∈ T) (hw : w ∈ T) :
    ∀ i, |((v i).val : ℝ) - (w i).val| ≤ 1 := by
  obtain ⟨_, y, hy⟩ := boundedChainSimplices_cube N n chamber T hT
  intro i
  have hv' := hy v hv i
  have hw' := hy w hw i
  have a : (y i : ℝ) ≤ (v i).val := by exact_mod_cast hv'.1
  have b : ((v i).val : ℝ) ≤ (y i : ℝ) + 1 := by exact_mod_cast hv'.2
  have c : (y i : ℝ) ≤ (w i).val := by exact_mod_cast hw'.1
  have d : ((w i).val : ℝ) ≤ (y i : ℝ) + 1 := by exact_mod_cast hw'.2
  rw [abs_le]; constructor <;> linarith

/-- Grading makes the encoded chain injective; hence each selected top simplex
has exactly the expected number of vertices. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boundedChainSimplices_card {J : Type*} [Fintype J] [DecidableEq J]
    (N n : ℕ) (chamber : (J → Fin (N+1)) → Prop)
    (T : Finset (J → Fin (N+1))) (hT : T ∈ boundedChainSimplices N n chamber) :
    T.card = n + 1 := by
  classical
  obtain ⟨y, c, v, hc, hcard, hv, hch, rfl⟩ := boundedChainSimplices_spec N n chamber T hT
  have hinj : Function.Injective v := by
    intro a b hab
    have hc_eq : c a = c b := by
      ext i
      have h := congrFun hab i
      have h' := congrArg Fin.val h
      rw [hv, hv] at h'
      by_cases ha : i ∈ c a <;> by_cases hb : i ∈ c b <;> simp_all
    apply Fin.ext
    have := congrArg Finset.card hc_eq
    simpa [hcard] using this
  rw [card_image_iff.mpr (fun _ _ _ _ h => hinj h), card_univ, Fintype.card_fin]

/-- Every bounded-chain simplex contains a vertex. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boundedChainSimplices_nonempty {J : Type*} [Fintype J] [DecidableEq J]
    (N n : ℕ) (chamber : (J → Fin (N+1)) → Prop)
    (T : Finset (J → Fin (N+1))) (hT : T ∈ boundedChainSimplices N n chamber) :
    T.Nonempty := by
  apply card_pos.mp
  rw [boundedChainSimplices_card N n chamber T hT]
  omega

/-- Normalized differences of cumulative-coordinate lattice vertices have
mesh at most 2/N within every bounded-chain simplex. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boundedChainSimplices_mesh {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (N n : ℕ) (hN : 0 < N) (chamber : (J → Fin (N+1)) → Prop)
    (l r : I → J) (T : Finset (J → Fin (N+1)))
    (hT : T ∈ boundedChainSimplices N n chamber)
    (v w : J → Fin (N+1)) (hv : v ∈ T) (hw : w ∈ T) :
    dist (fun i => (((v (r i)).val : ℝ) - (v (l i)).val) / N)
         (fun i => (((w (r i)).val : ℝ) - (w (l i)).val) / N) ≤ 2 / (N : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have h := boundedChainSimplices_real_bound N n chamber T hT v w hv hw
  apply (dist_pi_le_iff (by positivity)).2
  intro i
  rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hn]
  apply div_le_div_of_nonneg_right _ hn.le
  have h' := abs_sub (((v (r i)).val : ℝ) - (w (r i)).val)
    (((v (l i)).val : ℝ) - (w (l i)).val)
  have heq : (((v (r i)).val : ℝ) - (v (l i)).val) -
      (((w (r i)).val : ℝ) - (w (l i)).val) =
      (((v (r i)).val : ℝ) - (w (r i)).val) -
      (((v (l i)).val : ℝ) - (w (l i)).val) := by ring
  rw [heq]
  linarith [h (r i), h (l i)]

/-- Every codimension-one face of a bounded-chain simplex is obtained by
removing a unique rank from its graded representation. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boundedChainSimplices_facet {J : Type*} [Fintype J] [DecidableEq J]
    (N n : ℕ) (chamber : (J → Fin (N+1)) → Prop)
    (T F : Finset (J → Fin (N+1))) (hT : T ∈ boundedChainSimplices N n chamber)
    (hFT : F ⊆ T) (hF : F.card = n) :
    ∃ (y : J → ℕ) (c : Fin (n+1) → Finset J)
      (v : Fin (n+1) → (J → Fin (N+1))) (k : Fin (n+1)),
      Monotone c ∧ (∀ j, (c j).card = j.val) ∧
      (∀ j i, (v j i).val = y i + if i ∈ c j then 1 else 0) ∧
      (∀ j, chamber (v j)) ∧ T = univ.image v ∧
      F = (univ.erase k).image v := by
  classical
  obtain ⟨y, c, v, hc, hcard, hv, hch, hTv⟩ := boundedChainSimplices_spec N n chamber T hT
  have hinj : Function.Injective v := by
    intro a b hab
    have hc_eq : c a = c b := by
      ext i
      have h := congrArg Fin.val (congrFun hab i)
      rw [hv, hv] at h
      by_cases ha : i ∈ c a <;> by_cases hb : i ∈ c b <;> simp_all
    apply Fin.ext
    have := congrArg Finset.card hc_eq
    simpa [hcard] using this
  have hd : (T \ F).card = 1 := by
    rw [card_sdiff, inter_eq_left.mpr hFT, boundedChainSimplices_card N n chamber T hT, hF]
    omega
  obtain ⟨x, hx⟩ := card_eq_one.mp hd
  have hxT : x ∈ T := (mem_sdiff.mp (hx ▸ (by simp : x ∈ ({x} : Finset _)))).1
  have hxF : x ∉ F := (mem_sdiff.mp (hx ▸ (by simp : x ∈ ({x} : Finset _)))).2
  rw [hTv] at hxT
  obtain ⟨k, _, hk⟩ := mem_image.mp hxT
  refine ⟨y, c, v, k, hc, hcard, hv, hch, hTv, ?_⟩
  ext z
  constructor
  · intro hz
    have hzT := hFT hz
    rw [hTv] at hzT
    obtain ⟨j, _, rfl⟩ := mem_image.mp hzT
    apply mem_image.mpr
    refine ⟨j, ?_, rfl⟩
    simp only [mem_erase, mem_univ, and_true]
    intro hj
    subst j
    exact hxF (hk ▸ hz)
  · intro hz
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hz
    have hjk : j ≠ k := (mem_erase.mp hj).1
    have hjT : v j ∈ T := hTv.symm ▸ mem_image.mpr ⟨j, mem_univ _, rfl⟩
    by_contra hjF
    have hm : v j ∈ T \ F := mem_sdiff.mpr ⟨hjT, hjF⟩
    rw [hx] at hm
    have he : v j = x := mem_singleton.mp hm
    exact hjk (hinj (he.trans hk.symm))

/-- An admissible saturated Boolean chain in a complete lattice cube is a
member of the concrete bounded-chain simplex family. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boundedChainSimplices_of_boolean_chain {J : Type*} [Fintype J] [DecidableEq J]
    (N : ℕ) (chamber : (J → Fin (N+1)) → Prop) (y : J → ℕ)
    (hy : ∀ i, y i + 1 ≤ N) (T : Finset (Finset J))
    (hchain : ∀ a ∈ T, ∀ b ∈ T, a ⊆ b ∨ b ⊆ a)
    (hcard : T.card = Fintype.card J + 1)
    (hch : ∀ s ∈ T, chamber (fun i => ⟨y i + if i ∈ s then 1 else 0, by
      have := hy i; split_ifs <;> omega⟩)) :
    T.image (fun s i => (⟨y i + if i ∈ s then 1 else 0, by
      have := hy i; split_ifs <;> omega⟩ : Fin (N+1))) ∈
      boundedChainSimplices N (Fintype.card J) chamber := by
  classical
  obtain ⟨c, hc, hcc, hT⟩ := boolean_saturated_chain_enumeration T hchain hcard
  let enc : Finset J → J → Fin (N+1) := fun s i => ⟨y i + if i ∈ s then 1 else 0, by
    have := hy i; split_ifs <;> omega⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, y, c, fun k => enc (c k), hc, hcc, ?_, ?_, ?_⟩
  · intro k i
    rfl
  · intro k
    apply hch
    rw [hT]
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  · change T.image enc = _
    rw [hT, Finset.image_image]
    rfl

/-- Opposite corners in a bounded simplex determine its cube base, yielding
an encoding over the given base even if its original witness used another. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boundedChainSimplices_base_of_corners {J : Type*} [Fintype J] [DecidableEq J]
    (N : ℕ) (chamber : (J → Fin (N+1)) → Prop) (y : J → ℕ)
    (hy : ∀ i, y i + 1 ≤ N) (T : Finset (J → Fin (N+1)))
    (hT : T ∈ boundedChainSimplices N (Fintype.card J) chamber)
    (hbot : (fun i => (⟨y i, by have := hy i; omega⟩ : Fin (N+1))) ∈ T)
    (htop : (fun i => (⟨y i + 1, by have := hy i; omega⟩ : Fin (N+1))) ∈ T) :
    ∃ (c : Fin (Fintype.card J + 1) → Finset J)
      (v : Fin (Fintype.card J + 1) → (J → Fin (N+1))),
      Monotone c ∧ (∀ k, (c k).card = k.val) ∧
      (∀ k i, (v k i).val = y i + if i ∈ c k then 1 else 0) ∧
      (∀ k, chamber (v k)) ∧ T = Finset.univ.image v := by
  obtain ⟨z, c, v, hc, hcard, hv, hch, heq⟩ := boundedChainSimplices_spec N _ chamber T hT
  have hz : z = y := by
    funext i
    have hcube := (boundedChainSimplices_cube N _ chamber T hT).2
    -- Work directly with the given witness, rather than the existential cube.
    have hb : ∃ k, v k = (fun i => (⟨y i, by have := hy i; omega⟩ : Fin (N+1))) := by
      rw [heq] at hbot
      obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hbot
      exact ⟨k, hk⟩
    have ht : ∃ k, v k = (fun i => (⟨y i + 1, by have := hy i; omega⟩ : Fin (N+1))) := by
      rw [heq] at htop
      obtain ⟨k, _, hk⟩ := Finset.mem_image.mp htop
      exact ⟨k, hk⟩
    obtain ⟨k, hk⟩ := hb
    obtain ⟨l, hl⟩ := ht
    have hk' := congrArg Fin.val (congrFun hk i)
    have hl' := congrArg Fin.val (congrFun hl i)
    rw [hv] at hk' hl'
    split_ifs at hk' hl' <;> simp_all <;> omega
  subst z
  exact ⟨c, v, hc, hcard, hv, hch, heq⟩

/-- Interior incident simplices are encoded saturated Boolean chains over the
uniquely determined cube, with all vertices satisfying the chamber condition. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boundedChainSimplices_boolean_of_corners {J : Type*} [Fintype J] [DecidableEq J]
    (N : ℕ) (chamber : (J → Fin (N+1)) → Prop) (y : J → ℕ)
    (hy : ∀ i, y i + 1 ≤ N) (T : Finset (J → Fin (N+1)))
    (hT : T ∈ boundedChainSimplices N (Fintype.card J) chamber)
    (hbot : (fun i => (⟨y i, by have := hy i; omega⟩ : Fin (N+1))) ∈ T)
    (htop : (fun i => (⟨y i + 1, by have := hy i; omega⟩ : Fin (N+1))) ∈ T) :
    ∃ S : Finset (Finset J),
      (∀ a ∈ S, ∀ b ∈ S, a ⊆ b ∨ b ⊆ a) ∧
      S.card = Fintype.card J + 1 ∧
      (∀ s ∈ S, chamber (fun i => ⟨y i + if i ∈ s then 1 else 0, by
        have := hy i; split_ifs <;> omega⟩)) ∧
      T = S.image (fun s i => (⟨y i + if i ∈ s then 1 else 0, by
        have := hy i; split_ifs <;> omega⟩ : Fin (N+1))) := by
  classical
  obtain ⟨c, v, hc, hcard, hv, hch, hTv⟩ :=
    boundedChainSimplices_base_of_corners N chamber y hy T hT hbot htop
  let enc : Finset J → J → Fin (N+1) := fun s i => ⟨y i + if i ∈ s then 1 else 0, by
    have := hy i; split_ifs <;> omega⟩
  have hve : ∀ k, v k = enc (c k) := by
    intro k
    funext i
    apply Fin.ext
    exact hv k i
  refine ⟨Finset.univ.image c, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    rcases le_total i j with hij | hji
    · exact Or.inl (hc hij)
    · exact Or.inr (hc hji)
  · rw [Finset.card_image_iff.mpr, Finset.card_univ, Fintype.card_fin]
    intro i _ j _ hij
    apply Fin.ext
    have h := congrArg Finset.card hij
    simpa [hcard] using h
  · intro s hs
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
    change chamber (enc (c i))
    rw [← hve]
    exact hch i
  · rw [hTv, Finset.image_image]
    apply Finset.image_congr
    intro i _
    exact hve i

/-- For a facet retaining both cube corners, the incident concrete simplices
are precisely encoded admissible saturated Boolean chain completions. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boundedChainSimplices_interior_incidents {J : Type*} [Fintype J] [DecidableEq J]
    (N : ℕ) (chamber : (J → Fin (N+1)) → Prop) [DecidablePred chamber] (y : J → ℕ)
    (hy : ∀ i, y i + 1 ≤ N) (F : Finset (Finset J))
    (hbot : ∅ ∈ F) (htop : Finset.univ ∈ F) :
    let enc : Finset J → J → Fin (N+1) := fun s i => ⟨y i + if i ∈ s then 1 else 0, by
      have := hy i; split_ifs <;> omega⟩
    (boundedChainSimplices N (Fintype.card J) chamber).filter (fun T => F.image enc ⊆ T) =
      (Finset.univ.filter (fun S : Finset (Finset J) => F ⊆ S ∧
        S.card = Fintype.card J + 1 ∧
        (∀ a ∈ S, ∀ b ∈ S, a ⊆ b ∨ b ⊆ a) ∧
        ∀ s ∈ S, chamber (enc s))).image (fun S => S.image enc) := by
  classical
  dsimp only
  let enc : Finset J → J → Fin (N+1) := fun s i => ⟨y i + if i ∈ s then 1 else 0, by
    have := hy i; split_ifs <;> omega⟩
  change (boundedChainSimplices N _ chamber).filter (fun T => F.image enc ⊆ T) =
    (Finset.univ.filter (fun S : Finset (Finset J) => F ⊆ S ∧
      S.card = Fintype.card J + 1 ∧
      (∀ a ∈ S, ∀ b ∈ S, a ⊆ b ∨ b ⊆ a) ∧
      ∀ s ∈ S, chamber (enc s))).image (fun S => S.image enc)
  have hinj : Function.Injective enc := by
    intro a b h
    ext i
    have hi := congrArg Fin.val (congrFun h i)
    change y i + (if i ∈ a then 1 else 0) = y i + (if i ∈ b then 1 else 0) at hi
    by_cases ha : i ∈ a <;> by_cases hb : i ∈ b <;> simp_all
  ext T
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hT, hFT⟩
    have hb : (fun i => (⟨y i, by have := hy i; omega⟩ : Fin (N+1))) ∈ T := by
      apply hFT
      exact Finset.mem_image.mpr ⟨∅, hbot, by ext i; simp [enc]⟩
    have ht : (fun i => (⟨y i + 1, by have := hy i; omega⟩ : Fin (N+1))) ∈ T := by
      apply hFT
      exact Finset.mem_image.mpr ⟨Finset.univ, htop, by ext i; simp [enc]⟩
    obtain ⟨S, hchain, hc, hch, hTS⟩ :=
      boundedChainSimplices_boolean_of_corners N chamber y hy T hT hb ht
    refine ⟨S, ⟨?_, hc, hchain, hch⟩, hTS.symm⟩
    intro s hs
    have h : enc s ∈ S.image enc := by
      rw [← hTS]
      exact hFT (Finset.mem_image.mpr ⟨s, hs, rfl⟩)
    obtain ⟨s', hs', he⟩ := Finset.mem_image.mp h
    have : s' = s := hinj he
    simpa [this] using hs'
  · rintro ⟨S, ⟨hFS, hc, hchain, hch⟩, rfl⟩
    constructor
    · exact boundedChainSimplices_of_boolean_chain N chamber y hy S hchain hc hch
    · exact Finset.image_subset_image hFS
/-- The top-dimensional simplices containing a facet are precisely the distinct
insertions of a missing vertex that produce a simplex in the family. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem facet_incident_eq_image {α : Type*} [Fintype α] [DecidableEq α]
    (K : Finset (Finset α)) (F : Finset α) :
    K.filter (fun T => F ⊆ T ∧ T.card = F.card + 1) =
      (Finset.univ.filter (fun x => x ∉ F ∧ insert x F ∈ K)).image (fun x => insert x F) := by
  classical
  ext T
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hTK, hFT, hcard⟩
    have hd : (T \ F).card = 1 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hFT]
      omega
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hd
    have hxT : x ∈ T := (Finset.mem_sdiff.mp (hx ▸ (by simp : x ∈ ({x} : Finset α)))).1
    have hxF : x ∉ F := (Finset.mem_sdiff.mp (hx ▸ (by simp : x ∈ ({x} : Finset α)))).2
    have hT : insert x F = T := by
      ext y
      constructor
      · intro hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hxT
        · exact hFT hy
      · intro hy
        by_cases hyF : y ∈ F
        · exact Finset.mem_insert_of_mem hyF
        · have : y ∈ T \ F := Finset.mem_sdiff.mpr ⟨hy, hyF⟩
          rw [hx] at this
          simp only [Finset.mem_singleton] at this
          exact this ▸ Finset.mem_insert_self x F
    exact ⟨x, ⟨hxF, hT ▸ hTK⟩, hT⟩
  · rintro ⟨x, ⟨hxF, hxK⟩, rfl⟩
    exact ⟨hxK, Finset.subset_insert _ _, Finset.card_insert_of_notMem hxF⟩

/-- Incidence multiplicity is exactly the number of eligible missing vertices. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem facet_incident_card {α : Type*} [Fintype α] [DecidableEq α]
    (K : Finset (Finset α)) (F : Finset α) :
    (K.filter (fun T => F ⊆ T ∧ T.card = F.card + 1)).card =
      (Finset.univ.filter (fun x => x ∉ F ∧ insert x F ∈ K)).card := by
  classical
  rw [facet_incident_eq_image, Finset.card_image_iff]
  intro x hx y hy hxy
  have hxF : x ∉ F := (Finset.mem_filter.mp hx).2.1
  have hyF : y ∉ F := (Finset.mem_filter.mp hy).2.1
  change insert x F = insert y F at hxy
  have h : x ∈ insert y F := hxy ▸ Finset.mem_insert_self x F
  simpa [hxF] using h


/-- Exact incident count transfers to the number of admissible missing Boolean
vertices; the facet itself must have codimension one. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boundedChainSimplices_interior_incident_card {J : Type*} [Fintype J] [DecidableEq J]
    (N : ℕ) (chamber : (J → Fin (N+1)) → Prop) [DecidablePred chamber] (y : J → ℕ)
    (hy : ∀ i, y i + 1 ≤ N) (F : Finset (Finset J))
    (hbot : ∅ ∈ F) (htop : Finset.univ ∈ F) (hcard : F.card = Fintype.card J)
    (hch : ∀ s ∈ F, chamber (fun i => ⟨y i + if i ∈ s then 1 else 0, by
      have := hy i; split_ifs <;> omega⟩)) :
    let enc : Finset J → J → Fin (N+1) := fun s i => ⟨y i + if i ∈ s then 1 else 0, by
      have := hy i; split_ifs <;> omega⟩
    ((boundedChainSimplices N (Fintype.card J) chamber).filter (fun T => F.image enc ⊆ T)).card =
      (Finset.univ.filter (fun w : Finset J => w ∉ F ∧
        (insert w F).card = Fintype.card J + 1 ∧
        (∀ a ∈ insert w F, ∀ b ∈ insert w F, a ⊆ b ∨ b ⊆ a) ∧ chamber (enc w))).card := by
  classical
  dsimp only
  let enc : Finset J → J → Fin (N+1) := fun s i => ⟨y i + if i ∈ s then 1 else 0, by
    have := hy i; split_ifs <;> omega⟩
  have hinj : Function.Injective enc := by
    intro a b h
    ext i
    have hi := congrArg Fin.val (congrFun h i)
    change y i + (if i ∈ a then 1 else 0) = y i + (if i ∈ b then 1 else 0) at hi
    by_cases ha : i ∈ a <;> by_cases hb : i ∈ b <;> simp_all
  let K : Finset (Finset (Finset J)) := Finset.univ.filter (fun S =>
      S.card = Fintype.card J + 1 ∧ (∀ a ∈ S, ∀ b ∈ S, a ⊆ b ∨ b ⊆ a) ∧
      ∀ s ∈ S, chamber (enc s))
  have heq := boundedChainSimplices_interior_incidents N chamber y hy F hbot htop
  have heq2 : (boundedChainSimplices N (Fintype.card J) chamber).filter (fun T => F.image enc ⊆ T) = (K.filter (fun S => F ⊆ S)).image (fun S => S.image enc) := by
    rw [heq]
    congr 1
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, K]
    tauto
  rw [heq2, Finset.card_image_iff.mpr]
  · have hK : K.filter (fun S => F ⊆ S) =
        K.filter (fun S => F ⊆ S ∧ S.card = F.card + 1) := by
      ext S
      simp only [Finset.mem_filter, K, Finset.mem_univ, true_and]
      constructor <;> intro h
      · exact ⟨h.1, h.2, by rw [hcard]; exact h.1.1⟩
      · exact ⟨h.1, h.2.1⟩
    rw [hK, facet_incident_card]
    congr 1
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, K, Finset.mem_insert]
    constructor
    · rintro ⟨hn, hc, hchain, hall⟩
      exact ⟨hn, hc, hchain, hall w (Or.inl rfl)⟩
    · rintro ⟨hn, hc, hchain, hw⟩
      refine ⟨hn, hc, hchain, ?_⟩
      intro s hs
      rcases hs with rfl | hs
      · exact hw
      · exact hch s hs
  · intro A _ B _ hAB
    exact (Finset.image_inj hinj).mp hAB

/-- Shift a lower endpoint facet across its singleton direction. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boolean_bottom_shift {J : Type*} [Fintype J] [DecidableEq J]
    (F : Finset (Finset J)) (a : J)
    (hcard : F.card = Fintype.card J)
    (ha : ∀ s ∈ F, a ∈ s)
    (hchain : ∀ s ∈ F, ∀ t ∈ F, s ⊆ t ∨ t ⊆ s) :
    let G := F.image (fun s => s.erase a)
    (insert Finset.univ G).card = Fintype.card J + 1 ∧
      (∀ s ∈ insert Finset.univ G, ∀ t ∈ insert Finset.univ G, s ⊆ t ∨ t ⊆ s) := by
  classical
  dsimp only
  have hinj : ∀ s ∈ F, ∀ t ∈ F, s.erase a = t.erase a → s = t := by
    intro s hs t ht he
    have h1 : insert a (s.erase a) = s := Finset.insert_erase (ha s hs)
    have h2 : insert a (t.erase a) = t := Finset.insert_erase (ha t ht)
    rw [← h1, ← h2, he]
  have hn : Finset.univ ∉ F.image (fun s => s.erase a) := by
    intro h
    obtain ⟨s, hs, he⟩ := Finset.mem_image.mp h
    have hmem : a ∈ s.erase a := he.symm ▸ Finset.mem_univ a
    exact Finset.notMem_erase a s hmem
  constructor
  · rw [Finset.card_insert_of_notMem hn, Finset.card_image_iff.mpr hinj, hcard]
  · intro s hs t ht
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact Or.inr (Finset.subset_univ _)
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact Or.inl (Finset.subset_univ _)
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ht
    rcases hchain u hu v hv with h | h
    · exact Or.inl (Finset.erase_subset_erase a h)
    · exact Or.inr (Finset.erase_subset_erase a h)

/-- An endpoint facet has an explicit adjacent simplex whenever the shifted
cube and its new top corner are admissible. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boundedChainSimplices_bottom_shift {J : Type*} [Fintype J] [DecidableEq J]
    (N : ℕ) (chamber : (J → Fin (N+1)) → Prop)
    (y : J → ℕ) (a : J)
    (hy : ∀ i, y i + 1 ≤ N)
    (hy' : ∀ i, (y i + if i = a then 1 else 0) + 1 ≤ N)
    (F : Finset (Finset J)) (hcard : F.card = Fintype.card J)
    (ha : ∀ s ∈ F, a ∈ s)
    (hchain : ∀ s ∈ F, ∀ t ∈ F, s ⊆ t ∨ t ⊆ s)
    (hF : ∀ s ∈ F, chamber (fun i => ⟨y i + if i ∈ s then 1 else 0, by
      have := hy i; split_ifs <;> omega⟩))
    (htop : chamber (fun i => ⟨(y i + if i = a then 1 else 0) + 1, by
      have := hy' i; omega⟩)) :
    let enc : Finset J → J → Fin (N+1) := fun s i => ⟨y i + if i ∈ s then 1 else 0, by
      have := hy i; split_ifs <;> omega⟩
    let top : J → Fin (N+1) := fun i => ⟨(y i + if i = a then 1 else 0) + 1, by
      have := hy' i; omega⟩
    insert top (F.image enc) ∈ boundedChainSimplices N (Fintype.card J) chamber := by
  classical
  dsimp only
  let z : J → ℕ := fun i => y i + if i = a then 1 else 0
  let enc : Finset J → J → Fin (N+1) := fun s i => ⟨y i + if i ∈ s then 1 else 0, by
    have := hy i; split_ifs <;> omega⟩
  let enc' : Finset J → J → Fin (N+1) := fun s i => ⟨z i + if i ∈ s then 1 else 0, by
    have := hy' i; change z i + 1 ≤ N at this; split_ifs <;> omega⟩
  let G := F.image (fun s => s.erase a)
  have he : ∀ s ∈ F, enc' (s.erase a) = enc s := by
    intro s hs
    funext i
    apply Fin.ext
    change z i + (if i ∈ s.erase a then 1 else 0) = y i + (if i ∈ s then 1 else 0)
    by_cases hia : i = a
    · subst i
      simp [z, ha s hs]
    · simp [z, hia]
  have hg := boolean_bottom_shift F a hcard ha hchain
  have hc : ∀ s ∈ insert Finset.univ G, chamber (enc' s) := by
    intro s hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · simpa [enc', z] using htop
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
      rw [he t ht]
      exact hF t ht
  have ht := boundedChainSimplices_of_boolean_chain N chamber z hy' (insert Finset.univ G) hg.2 hg.1 hc
  change (insert Finset.univ G).image enc' ∈ _ at ht
  have heq : (insert Finset.univ G).image enc' =
      insert (fun i => (⟨(y i + if i = a then 1 else 0) + 1, by have := hy' i; omega⟩ : Fin (N+1))) (F.image enc) := by
    rw [Finset.image_insert]
    congr 1
    · funext i; apply Fin.ext; simp [enc', z]
    · ext v
      simp only [G, Finset.mem_image]
      constructor
      · rintro ⟨s, ⟨t, ht, rfl⟩, rfl⟩
        exact ⟨t, ht, (he t ht).symm⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨t.erase a, ⟨t, ht, rfl⟩, he t ht⟩
  rw [heq] at ht
  exact ht

/-- Shift an upper endpoint facet down across the omitted coordinate. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boolean_top_shift {J : Type*} [Fintype J] [DecidableEq J]
    (F : Finset (Finset J)) (a : J)
    (hcard : F.card = Fintype.card J)
    (ha : ∀ s ∈ F, a ∉ s)
    (hchain : ∀ s ∈ F, ∀ t ∈ F, s ⊆ t ∨ t ⊆ s) :
    let G := F.image (fun s => insert a s)
    (insert ∅ G).card = Fintype.card J + 1 ∧
      (∀ s ∈ insert ∅ G, ∀ t ∈ insert ∅ G, s ⊆ t ∨ t ⊆ s) := by
  classical
  dsimp only
  have hinj : ∀ s ∈ F, ∀ t ∈ F, insert a s = insert a t → s = t := by
    intro s hs t ht he
    have h := congrArg (fun u : Finset J => u.erase a) he
    simpa [Finset.erase_insert, ha s hs, ha t ht] using h
  have hn : (∅ : Finset J) ∉ F.image (fun s => insert a s) := by
    intro h
    obtain ⟨s, hs, he⟩ := Finset.mem_image.mp h
    have hmem : a ∈ (∅ : Finset J) := he ▸ Finset.mem_insert_self a s
    simpa using hmem
  constructor
  · rw [Finset.card_insert_of_notMem hn, Finset.card_image_iff.mpr hinj, hcard]
  · intro s hs t ht
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact Or.inl (Finset.empty_subset _)
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact Or.inr (Finset.empty_subset _)
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ht
    rcases hchain u hu v hv with h | h
    · exact Or.inl (Finset.insert_subset_insert a h)
    · exact Or.inr (Finset.insert_subset_insert a h)

/-- An upper endpoint facet has the adjacent lower cube simplex when its new
bottom corner is admissible. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boundedChainSimplices_top_shift {J : Type*} [Fintype J] [DecidableEq J]
    (N : ℕ) (chamber : (J → Fin (N+1)) → Prop)
    (y z : J → ℕ) (a : J)
    (hy : ∀ i, y i + 1 ≤ N) (hz : ∀ i, z i + 1 ≤ N)
    (hzy : ∀ i, z i + (if i = a then 1 else 0) = y i)
    (F : Finset (Finset J)) (hcard : F.card = Fintype.card J)
    (ha : ∀ s ∈ F, a ∉ s)
    (hchain : ∀ s ∈ F, ∀ t ∈ F, s ⊆ t ∨ t ⊆ s)
    (hF : ∀ s ∈ F, chamber (fun i => ⟨y i + if i ∈ s then 1 else 0, by
      have := hy i; split_ifs <;> omega⟩))
    (hbot : chamber (fun i => ⟨z i, by have := hz i; omega⟩)) :
    let enc : Finset J → J → Fin (N+1) := fun s i => ⟨y i + if i ∈ s then 1 else 0, by
      have := hy i; split_ifs <;> omega⟩
    let bot : J → Fin (N+1) := fun i => ⟨z i, by have := hz i; omega⟩
    insert bot (F.image enc) ∈ boundedChainSimplices N (Fintype.card J) chamber := by
  classical
  dsimp only
  let enc : Finset J → J → Fin (N+1) := fun s i => ⟨y i + if i ∈ s then 1 else 0, by
    have := hy i; split_ifs <;> omega⟩
  let enc' : Finset J → J → Fin (N+1) := fun s i => ⟨z i + if i ∈ s then 1 else 0, by
    have := hz i; split_ifs <;> omega⟩
  let G := F.image (fun s => insert a s)
  have he : ∀ s ∈ F, enc' (insert a s) = enc s := by
    intro s hs
    funext i
    apply Fin.ext
    change z i + (if i ∈ insert a s then 1 else 0) = y i + (if i ∈ s then 1 else 0)
    have hh := hzy i
    by_cases hia : i = a
    · subst i
      simp [ha s hs] at hh ⊢
      omega
    · simp [hia] at hh ⊢
      rw [hh]
  have hg := boolean_top_shift F a hcard ha hchain
  have hc : ∀ s ∈ insert ∅ G, chamber (enc' s) := by
    intro s hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · simpa [enc'] using hbot
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
      rw [he t ht]
      exact hF t ht
  have ht := boundedChainSimplices_of_boolean_chain N chamber z hz (insert ∅ G) hg.2 hg.1 hc
  change (insert ∅ G).image enc' ∈ _ at ht
  have heq : (insert ∅ G).image enc' =
      insert (fun i => (⟨z i, by have := hz i; omega⟩ : Fin (N+1))) (F.image enc) := by
    rw [Finset.image_insert]
    congr 1
    ext v
    simp only [G, Finset.mem_image]
    constructor
    · rintro ⟨s, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨t, ht, (he t ht).symm⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨insert a t, ⟨t, ht, rfl⟩, he t ht⟩
  rw [heq] at ht
  exact ht

/-- Each full-dimensional cubical chain contains both corners of its cube. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boundedChainSimplices_corners {J : Type*} [Fintype J] [DecidableEq J]
    (N : ℕ) (chamber : (J → Fin (N+1)) → Prop)
    (T : Finset (J → Fin (N+1)))
    (hT : T ∈ boundedChainSimplices N (Fintype.card J) chamber) :
    ∃ z : J → ℕ, ∃ bot top : J → Fin (N+1),
      (∀ i, (bot i).val = z i) ∧ (∀ i, (top i).val = z i + 1) ∧
      bot ∈ T ∧ top ∈ T ∧
      (∀ v ∈ T, ∀ i, z i ≤ (v i).val ∧ (v i).val ≤ z i + 1) := by
  classical
  obtain ⟨z, c, v, hc, hcard, hv, hch, hTv⟩ := boundedChainSimplices_spec N _ chamber T hT
  have hc0 : c 0 = ∅ := Finset.card_eq_zero.mp (by simpa using hcard 0)
  have hct : c (Fin.last _) = Finset.univ := Finset.eq_univ_of_card _ (by simpa using hcard (Fin.last _))
  refine ⟨z, v 0, v (Fin.last _), ?_, ?_, ?_, ?_, ?_⟩
  · intro i; simpa [hc0] using hv 0 i
  · intro i; simpa [hct] using hv (Fin.last _) i
  · rw [hTv]; exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · rw [hTv]; exact Finset.mem_image.mpr ⟨Fin.last _, Finset.mem_univ _, rfl⟩
  · intro w hw i
    rw [hTv] at hw
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hw
    rw [hv]
    split_ifs <;> omega
/-- Auxiliary unit cube base endpoint result for the lattice construction.
The proof uses the preceding finite, order, and continuity lemmas as applicable. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem unit_cube_base_endpoint {J : Type*} [DecidableEq J] (y z : J → ℕ) (a : J)
    (hlow : ∀ j, z j ≤ y j + (if j = a then 1 else 0) ∧
      y j + (if j = a then 1 else 0) ≤ z j + 1)
    (hhigh : ∀ j, z j ≤ y j + 1 ∧ y j + 1 ≤ z j + 1) :
    z = y ∨ z = fun j => y j + if j = a then 1 else 0 := by
  have hout : ∀ j, j ≠ a → z j = y j := by
    intro j hja
    have h₁ := hlow j
    have h₂ := hhigh j
    simp only [hja, ↓reduceIte, add_zero] at h₁
    omega
  have ha₁ := hlow a
  have ha₂ := hhigh a
  simp only [↓reduceIte] at ha₁
  by_cases h : z a = y a
  · left
    funext j
    by_cases hj : j = a
    · subst j; exact h
    · exact hout j hj
  · right
    funext j
    by_cases hj : j = a
    · subst j
      simp only [↓reduceIte]
      omega
    · simp only [hj, ↓reduceIte, add_zero]
      exact hout j hj


/-- Every completion of a bottom endpoint facet is obtained by adding either
its original bottom corner or the opposite shifted cube's top corner. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boundedChainSimplices_bottom_missing_classify {J : Type*} [Fintype J] [DecidableEq J]
    (N : ℕ) (chamber : (J → Fin (N+1)) → Prop)
    (y : J → ℕ) (a : J) (F T : Finset (J → Fin (N+1)))
    (hT : T ∈ boundedChainSimplices N (Fintype.card J) chamber)
    (hFT : F ⊆ T) (hcard : F.card = Fintype.card J)
    (L H : J → Fin (N+1)) (hL : L ∈ F) (hH : H ∈ F)
    (hLv : ∀ i, (L i).val = y i + if i = a then 1 else 0)
    (hHv : ∀ i, (H i).val = y i + 1)
    (hFa : ∀ v ∈ F, (v a).val = y a + 1)
    (x : J → Fin (N+1)) (hx : x ∈ T) (hxF : x ∉ F) :
    (∀ i, (x i).val = y i) ∨
      (∀ i, (x i).val = (y i + if i = a then 1 else 0) + 1) := by
  classical
  obtain ⟨z, bot, top, hb, ht, hbT, htT, hcube⟩ := boundedChainSimplices_corners N chamber T hT
  have hbase := unit_cube_base_endpoint y z a (by simpa only [hLv] using hcube L (hFT hL))
    (by simpa only [hHv] using hcube H (hFT hH))
  have hdiff : (T \ F).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hFT, boundedChainSimplices_card N _ chamber T hT, hcard]
    omega
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hdiff
  have hxw : x = w := by
    have : x ∈ T \ F := Finset.mem_sdiff.mpr ⟨hx, hxF⟩
    simpa [hw] using this
  rcases hbase with rfl | hz
  · have hbF : bot ∉ F := by
      intro h
      have := hFa bot h
      have := hb a
      omega
    have hbw : bot = w := by
      have : bot ∈ T \ F := Finset.mem_sdiff.mpr ⟨hbT, hbF⟩
      simpa [hw] using this
    left
    intro i
    rw [hxw, ← hbw]
    exact hb i
  · have htF : top ∉ F := by
      intro h
      have h₁ := hFa top h
      have h₂ := ht a
      rw [hz] at h₂
      simp at h₂
      omega
    have htw : top = w := by
      have : top ∈ T \ F := Finset.mem_sdiff.mpr ⟨htT, htF⟩
      simpa [hw] using this
    right
    intro i
    rw [hxw, ← htw, ht, hz]
/-- Auxiliary unit cube base endpoint dual result for the lattice construction.
The proof uses the preceding finite, order, and continuity lemmas as applicable. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem unit_cube_base_endpoint_dual {J : Type*} [DecidableEq J] (y z : J → ℕ) (a : J)
    (hlow : ∀ j, z j ≤ y j ∧ y j ≤ z j + 1)
    (hhigh : ∀ j, z j ≤ y j + (if j = a then 0 else 1) ∧
      y j + (if j = a then 0 else 1) ≤ z j + 1) :
    z = y ∨ (fun j => z j + if j = a then 1 else 0) = y := by
  have hout : ∀ j, j ≠ a → z j = y j := by
    intro j hja
    have h₁ := hlow j
    have h₂ := hhigh j
    simp only [hja, ↓reduceIte] at h₂
    omega
  have ha₁ := hlow a
  by_cases h : z a = y a
  · left
    funext j
    by_cases hj : j = a
    · subst j; exact h
    · exact hout j hj
  · right
    funext j
    by_cases hj : j = a
    · subst j
      simp only [↓reduceIte]
      omega
    · simp only [hj, ↓reduceIte, add_zero]
      exact hout j hj

/-- Every completion of a top endpoint facet adds either the old cube top or
its adjacent lower cube's bottom corner. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boundedChainSimplices_top_missing_classify {J : Type*} [Fintype J] [DecidableEq J]
    (N : ℕ) (chamber : (J → Fin (N+1)) → Prop)
    (y : J → ℕ) (a : J) (F T : Finset (J → Fin (N+1)))
    (hT : T ∈ boundedChainSimplices N (Fintype.card J) chamber)
    (hFT : F ⊆ T) (hcard : F.card = Fintype.card J)
    (L H : J → Fin (N+1)) (hL : L ∈ F) (hH : H ∈ F)
    (hLv : ∀ i, (L i).val = y i)
    (hHv : ∀ i, (H i).val = y i + if i = a then 0 else 1)
    (hFa : ∀ v ∈ F, (v a).val = y a)
    (x : J → Fin (N+1)) (hx : x ∈ T) (hxF : x ∉ F) :
    (∀ i, (x i).val = y i + 1) ∨
      (∀ i, (x i).val + (if i = a then 1 else 0) = y i) := by
  classical
  obtain ⟨z, bot, top, hb, ht, hbT, htT, hcube⟩ := boundedChainSimplices_corners N chamber T hT
  have hbase := unit_cube_base_endpoint_dual y z a (by simpa only [hLv] using hcube L (hFT hL))
    (by simpa only [hHv] using hcube H (hFT hH))
  have hdiff : (T \ F).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hFT, boundedChainSimplices_card N _ chamber T hT, hcard]
    omega
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hdiff
  have hxw : x = w := by
    have : x ∈ T \ F := Finset.mem_sdiff.mpr ⟨hx, hxF⟩
    simpa [hw] using this
  rcases hbase with rfl | hz
  · have htF : top ∉ F := by
      intro h
      have := hFa top h
      have := ht a
      omega
    have htw : top = w := by
      have : top ∈ T \ F := Finset.mem_sdiff.mpr ⟨htT, htF⟩
      simpa [hw] using this
    left
    intro i
    rw [hxw, ← htw]
    exact ht i
  · have hbF : bot ∉ F := by
      intro h
      have h₁ := hFa bot h
      have h₂ := hb a
      have h₃ := congrFun hz a
      simp at h₃
      omega
    have hbw : bot = w := by
      have : bot ∈ T \ F := Finset.mem_sdiff.mpr ⟨hbT, hbF⟩
      simpa [hw] using this
    right
    intro i
    rw [hxw, ← hbw, hb]
    exact congrFun hz i

/-- A finite family covered by two subsingleton properties has at most two members. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem finset_card_le_two_of_unique_properties {α : Type*} (S : Finset α) (P Q : α → Prop)
    (hcover : ∀ x ∈ S, P x ∨ Q x)
    (hp : ∀ x ∈ S, ∀ y ∈ S, P x → P y → x = y)
    (hq : ∀ x ∈ S, ∀ y ∈ S, Q x → Q y → x = y) : S.card ≤ 2 := by
  classical
  have h := Finset.card_le_card_of_injOn (s := S) (t := (Finset.univ : Finset Bool))
      (fun (x : α) => decide (P x)) (by intro x hx; change decide (P x) ∈ (Finset.univ : Finset Bool); exact Finset.mem_univ _) (by
        intro x hx y hy he
        by_cases hpx : P x
        · have hpy : P y := by simpa [hpx] using he.symm
          exact hp x hx y hy hpx hpy
        · have hpy : ¬ P y := by simpa [hpx] using he.symm
          have hqx := (hcover x hx).resolve_left hpx
          have hqy := (hcover y hy).resolve_left hpy
          exact hq x hx y hy hqx hqy)
  simpa using h

/-- The number of global incident simplices at a bottom endpoint facet is at most two. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boundedChainSimplices_bottom_incident_le_two {J : Type*} [Fintype J] [DecidableEq J]
    (N : ℕ) (chamber : (J → Fin (N+1)) → Prop)
    (y : J → ℕ) (a : J) (F : Finset (J → Fin (N+1)))
    (hcard : F.card = Fintype.card J)
    (L H : J → Fin (N+1)) (hL : L ∈ F) (hH : H ∈ F)
    (hLv : ∀ i, (L i).val = y i + if i = a then 1 else 0)
    (hHv : ∀ i, (H i).val = y i + 1)
    (hFa : ∀ v ∈ F, (v a).val = y a + 1) :
    ((boundedChainSimplices N (Fintype.card J) chamber).filter (fun T => F ⊆ T)).card ≤ 2 := by
  classical
  let K := boundedChainSimplices N (Fintype.card J) chamber
  have heq : K.filter (fun T => F ⊆ T) = K.filter (fun T => F ⊆ T ∧ T.card = F.card + 1) := by
    ext T
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hT, hFT⟩
      exact ⟨hT, hFT, by rw [boundedChainSimplices_card N _ chamber T hT, hcard]⟩
    · rintro ⟨hT, hFT, _⟩
      exact ⟨hT, hFT⟩
  rw [heq, facet_incident_card]
  apply finset_card_le_two_of_unique_properties _
    (fun x => ∀ i, (x i).val = y i)
    (fun x => ∀ i, (x i).val = (y i + if i = a then 1 else 0) + 1)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact boundedChainSimplices_bottom_missing_classify N chamber y a F (insert x F) hx.2
      (Finset.subset_insert _ _) hcard L H hL hH hLv hHv hFa x (Finset.mem_insert_self _ _) hx.1
  · intro x hx z hz hpx hpz
    funext i; exact Fin.ext ((hpx i).trans (hpz i).symm)
  · intro x hx z hz hpx hpz
    funext i; exact Fin.ext ((hpx i).trans (hpz i).symm)

/-- The number of global incident simplices at a top endpoint facet is at most two. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boundedChainSimplices_top_incident_le_two {J : Type*} [Fintype J] [DecidableEq J]
    (N : ℕ) (chamber : (J → Fin (N+1)) → Prop)
    (y : J → ℕ) (a : J) (F : Finset (J → Fin (N+1)))
    (hcard : F.card = Fintype.card J)
    (L H : J → Fin (N+1)) (hL : L ∈ F) (hH : H ∈ F)
    (hLv : ∀ i, (L i).val = y i)
    (hHv : ∀ i, (H i).val = y i + if i = a then 0 else 1)
    (hFa : ∀ v ∈ F, (v a).val = y a) :
    ((boundedChainSimplices N (Fintype.card J) chamber).filter (fun T => F ⊆ T)).card ≤ 2 := by
  classical
  let K := boundedChainSimplices N (Fintype.card J) chamber
  have heq : K.filter (fun T => F ⊆ T) = K.filter (fun T => F ⊆ T ∧ T.card = F.card + 1) := by
    ext T
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hT, hFT⟩
      exact ⟨hT, hFT, by rw [boundedChainSimplices_card N _ chamber T hT, hcard]⟩
    · rintro ⟨hT, hFT, _⟩
      exact ⟨hT, hFT⟩
  rw [heq, facet_incident_card]
  apply finset_card_le_two_of_unique_properties _
    (fun x => ∀ i, (x i).val = y i + 1)
    (fun x => ∀ i, (x i).val + (if i = a then 1 else 0) = y i)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact boundedChainSimplices_top_missing_classify N chamber y a F (insert x F) hx.2
      (Finset.subset_insert _ _) hcard L H hL hH hLv hHv hFa x (Finset.mem_insert_self _ _) hx.1
  · intro x hx z hz hpx hpz
    funext i; exact Fin.ext ((hpx i).trans (hpz i).symm)
  · intro x hx z hz hpx hpz
    funext i; apply Fin.ext
    have h₁ := hpx i
    have h₂ := hpz i
    omega

/-- If both completions are admissible, the bottom endpoint facet has exactly
 two concrete incident simplices. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boundedChainSimplices_bottom_incident_two {J : Type*} [Fintype J] [DecidableEq J]
    (N : ℕ) (chamber : (J → Fin (N+1)) → Prop)
    (y : J → ℕ) (a : J)
    (hy : ∀ i, y i + 1 ≤ N)
    (hy' : ∀ i, (y i + if i = a then 1 else 0) + 1 ≤ N)
    (F : Finset (Finset J)) (hcard : F.card = Fintype.card J)
    (ha : ∀ s ∈ F, a ∈ s)
    (hchain : ∀ s ∈ F, ∀ t ∈ F, s ⊆ t ∨ t ⊆ s)
    (hsingle : {a} ∈ F) (huniv : Finset.univ ∈ F)
    (hF : ∀ s ∈ F, chamber (fun i => ⟨y i + if i ∈ s then 1 else 0, by
      have := hy i; split_ifs <;> omega⟩))
    (hbot : chamber (fun i => ⟨y i, by have := hy i; omega⟩))
    (htop : chamber (fun i => ⟨(y i + if i = a then 1 else 0) + 1, by
      have := hy' i; omega⟩)) :
    let enc : Finset J → J → Fin (N+1) := fun s i => ⟨y i + if i ∈ s then 1 else 0, by
      have := hy i; split_ifs <;> omega⟩
    ((boundedChainSimplices N (Fintype.card J) chamber).filter (fun T => F.image enc ⊆ T)).card = 2 := by
  classical
  dsimp only
  let enc : Finset J → J → Fin (N+1) := fun s i => ⟨y i + if i ∈ s then 1 else 0, by
      have := hy i; split_ifs <;> omega⟩
  let bot : J → Fin (N+1) := fun i => ⟨y i, by have := hy i; omega⟩
  let top : J → Fin (N+1) := fun i => ⟨(y i + if i = a then 1 else 0) + 1, by
      have := hy' i; omega⟩
  let V := F.image enc
  let K := (boundedChainSimplices N (Fintype.card J) chamber).filter (fun T => V ⊆ T)
  have hinj : Function.Injective enc := by
    intro s t h
    ext i
    have hh := congrArg Fin.val (congrFun h i)
    change y i + (if i ∈ s then 1 else 0) = y i + (if i ∈ t then 1 else 0) at hh
    by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all
  have hVc : V.card = Fintype.card J := by
    rw [show V = F.image enc from rfl, Finset.card_image_iff.mpr (fun _ _ _ _ h => hinj h), hcard]
  have hle : K.card ≤ 2 := by
    apply boundedChainSimplices_bottom_incident_le_two N chamber y a V hVc (enc {a}) (enc Finset.univ)
    · exact Finset.mem_image.mpr ⟨{a}, hsingle, rfl⟩
    · exact Finset.mem_image.mpr ⟨Finset.univ, huniv, rfl⟩
    · intro i; simp [enc, eq_comm]
    · intro i; simp [enc]
    · intro v hv
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hv
      simp [enc, ha s hs]
  have hzero : (∅ : Finset J) ∉ F := by
    intro h
    have := ha ∅ h
    simpa using this
  have hold : insert bot V ∈ K := by
    have hc : ∀ s ∈ insert ∅ F, ∀ t ∈ insert ∅ F, s ⊆ t ∨ t ⊆ s := by
      intro s hs t ht
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact Or.inl (Finset.empty_subset _)
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact Or.inr (Finset.empty_subset _)
      exact hchain s hs t ht
    have hcs : (insert ∅ F).card = Fintype.card J + 1 := by rw [Finset.card_insert_of_notMem hzero, hcard]
    have hch : ∀ s ∈ insert ∅ F, chamber (enc s) := by
      intro s hs
      rcases Finset.mem_insert.mp hs with rfl | hs
      · simpa [enc] using hbot
      · exact hF s hs
    have h := boundedChainSimplices_of_boolean_chain N chamber y hy (insert ∅ F) hc hcs hch
    apply Finset.mem_filter.mpr
    refine ⟨?_, Finset.subset_insert _ _⟩
    simpa [Finset.image_insert, enc, bot, V] using h
  have hnew : insert top V ∈ K := by
    apply Finset.mem_filter.mpr
    exact ⟨boundedChainSimplices_bottom_shift N chamber y a hy hy' F hcard ha hchain hF htop,
      Finset.subset_insert _ _⟩
  have hbotV : bot ∉ V := by
    intro hv
    obtain ⟨s, hs, he⟩ := Finset.mem_image.mp hv
    have h := congrArg Fin.val (congrFun he a)
    simp [enc, bot, ha s hs] at h
  have htopV : top ∉ V := by
    intro hv
    obtain ⟨s, hs, he⟩ := Finset.mem_image.mp hv
    have h := congrArg Fin.val (congrFun he a)
    simp [enc, top, ha s hs] at h
  have hne : insert bot V ≠ insert top V := by
    intro h
    have hm : bot ∈ insert top V := h ▸ Finset.mem_insert_self bot V
    rcases Finset.mem_insert.mp hm with he | he
    · have hv := congrArg Fin.val (congrFun he a)
      simp [bot, top] at hv
      omega
    · exact hbotV he
  have hge : 2 ≤ K.card := Finset.one_lt_card.mpr ⟨_, hold, _, hnew, hne⟩
  exact Nat.le_antisymm hle hge

/-- If no shifted top corner is admissible, at most one simplex meets the
bottom endpoint facet. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boundedChainSimplices_bottom_incident_le_one {J : Type*} [Fintype J] [DecidableEq J]
    (N : ℕ) (chamber : (J → Fin (N+1)) → Prop)
    (y : J → ℕ) (a : J) (F : Finset (J → Fin (N+1)))
    (hcard : F.card = Fintype.card J)
    (L H : J → Fin (N+1)) (hL : L ∈ F) (hH : H ∈ F)
    (hLv : ∀ i, (L i).val = y i + if i = a then 1 else 0)
    (hHv : ∀ i, (H i).val = y i + 1)
    (hFa : ∀ v ∈ F, (v a).val = y a + 1)
    (hno : ∀ x : J → Fin (N+1),
      (∀ i, (x i).val = (y i + if i = a then 1 else 0) + 1) → ¬ chamber x) :
    ((boundedChainSimplices N (Fintype.card J) chamber).filter (fun T => F ⊆ T)).card ≤ 1 := by
  classical
  let K := boundedChainSimplices N (Fintype.card J) chamber
  have heq : K.filter (fun T => F ⊆ T) = K.filter (fun T => F ⊆ T ∧ T.card = F.card + 1) := by
    ext T
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hT, hFT⟩
      exact ⟨hT, hFT, by rw [boundedChainSimplices_card N _ chamber T hT, hcard]⟩
    · rintro ⟨hT, hFT, _⟩
      exact ⟨hT, hFT⟩
  rw [heq, facet_incident_card]
  apply Finset.card_le_one.mpr
  intro x hx z hz
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hz
  have base : ∀ x, x ∉ F → insert x F ∈ K → ∀ i, (x i).val = y i := by
    intro x hxF hxK
    rcases boundedChainSimplices_bottom_missing_classify N chamber y a F (insert x F) hxK
      (Finset.subset_insert _ _) hcard L H hL hH hLv hHv hFa x (Finset.mem_insert_self _ _) hxF with h | h
    · exact h
    · exact False.elim (hno x h ((boundedChainSimplices_cube N _ chamber _ hxK).1 x (Finset.mem_insert_self _ _)))
  have h₁ := base x hx.1 hx.2
  have h₂ := base z hz.1 hz.2
  funext i
  exact Fin.ext ((h₁ i).trans (h₂ i).symm)

/-- If no shifted bottom corner is admissible, at most one simplex meets the
 top endpoint facet. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boundedChainSimplices_top_incident_le_one {J : Type*} [Fintype J] [DecidableEq J]
    (N : ℕ) (chamber : (J → Fin (N+1)) → Prop)
    (y : J → ℕ) (a : J) (F : Finset (J → Fin (N+1)))
    (hcard : F.card = Fintype.card J)
    (L H : J → Fin (N+1)) (hL : L ∈ F) (hH : H ∈ F)
    (hLv : ∀ i, (L i).val = y i)
    (hHv : ∀ i, (H i).val = y i + if i = a then 0 else 1)
    (hFa : ∀ v ∈ F, (v a).val = y a)
    (hno : ∀ x : J → Fin (N+1),
      (∀ i, (x i).val + (if i = a then 1 else 0) = y i) → ¬ chamber x) :
    ((boundedChainSimplices N (Fintype.card J) chamber).filter (fun T => F ⊆ T)).card ≤ 1 := by
  classical
  let K := boundedChainSimplices N (Fintype.card J) chamber
  have heq : K.filter (fun T => F ⊆ T) = K.filter (fun T => F ⊆ T ∧ T.card = F.card + 1) := by
    ext T
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hT, hFT⟩
      exact ⟨hT, hFT, by rw [boundedChainSimplices_card N _ chamber T hT, hcard]⟩
    · rintro ⟨hT, hFT, _⟩
      exact ⟨hT, hFT⟩
  rw [heq, facet_incident_card]
  apply Finset.card_le_one.mpr
  intro x hx z hz
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hz
  have base : ∀ x, x ∉ F → insert x F ∈ K → ∀ i, (x i).val = y i + 1 := by
    intro x hxF hxK
    rcases boundedChainSimplices_top_missing_classify N chamber y a F (insert x F) hxK
      (Finset.subset_insert _ _) hcard L H hL hH hLv hHv hFa x (Finset.mem_insert_self _ _) hxF with h | h
    · exact h
    · exact False.elim (hno x h ((boundedChainSimplices_cube N _ chamber _ hxK).1 x (Finset.mem_insert_self _ _)))
  have h₁ := base x hx.1 hx.2
  have h₂ := base z hz.1 hz.2
  funext i
  exact Fin.ext ((h₁ i).trans (h₂ i).symm)

/-- A top endpoint facet has two incident simplices when both its original
upper corner and the shifted lower corner are admissible. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boundedChainSimplices_top_incident_two {J : Type*} [Fintype J] [DecidableEq J]
    (N : ℕ) (chamber : (J → Fin (N+1)) → Prop)
    (y z : J → ℕ) (a : J)
    (hy : ∀ i, y i + 1 ≤ N) (hz : ∀ i, z i + 1 ≤ N)
    (hzy : ∀ i, z i + (if i = a then 1 else 0) = y i)
    (F : Finset (Finset J)) (hcard : F.card = Fintype.card J)
    (ha : ∀ s ∈ F, a ∉ s)
    (hchain : ∀ s ∈ F, ∀ t ∈ F, s ⊆ t ∨ t ⊆ s)
    (hempty : ∅ ∈ F) (hco : Finset.univ \ {a} ∈ F)
    (hF : ∀ s ∈ F, chamber (fun i => ⟨y i + if i ∈ s then 1 else 0, by
      have := hy i; split_ifs <;> omega⟩))
    (htop : chamber (fun i => ⟨y i + 1, by have := hy i; omega⟩))
    (hbot : chamber (fun i => ⟨z i, by have := hz i; omega⟩)) :
    let enc : Finset J → J → Fin (N+1) := fun s i => ⟨y i + if i ∈ s then 1 else 0, by
      have := hy i; split_ifs <;> omega⟩
    ((boundedChainSimplices N (Fintype.card J) chamber).filter (fun T => F.image enc ⊆ T)).card = 2 := by
  classical
  dsimp only
  let enc : Finset J → J → Fin (N+1) := fun s i => ⟨y i + if i ∈ s then 1 else 0, by
      have := hy i; split_ifs <;> omega⟩
  let bot : J → Fin (N+1) := fun i => ⟨z i, by have := hz i; omega⟩
  let top : J → Fin (N+1) := fun i => ⟨y i + 1, by have := hy i; omega⟩
  let V := F.image enc
  let K := (boundedChainSimplices N (Fintype.card J) chamber).filter (fun T => V ⊆ T)
  have hinj : Function.Injective enc := by
    intro s t h
    ext i
    have hh := congrArg Fin.val (congrFun h i)
    change y i + (if i ∈ s then 1 else 0) = y i + (if i ∈ t then 1 else 0) at hh
    by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all
  have hVc : V.card = Fintype.card J := by
    rw [show V = F.image enc from rfl, Finset.card_image_iff.mpr (fun _ _ _ _ h => hinj h), hcard]
  have hle : K.card ≤ 2 := by
    apply boundedChainSimplices_top_incident_le_two N chamber y a V hVc (enc ∅) (enc (Finset.univ \ {a}))
    · exact Finset.mem_image.mpr ⟨∅, hempty, rfl⟩
    · exact Finset.mem_image.mpr ⟨Finset.univ \ {a}, hco, rfl⟩
    · intro i; simp [enc]
    · intro i; by_cases h : i = a <;> simp [enc, h]
    · intro v hv
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hv
      simp [enc, ha s hs]
  have hfull : (Finset.univ : Finset J) ∉ F := by
    intro h
    have := ha Finset.univ h
    simpa using this
  have hold : insert top V ∈ K := by
    have hc : ∀ s ∈ insert Finset.univ F, ∀ t ∈ insert Finset.univ F, s ⊆ t ∨ t ⊆ s := by
      intro s hs t ht
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact Or.inr (Finset.subset_univ _)
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact Or.inl (Finset.subset_univ _)
      exact hchain s hs t ht
    have hcs : (insert Finset.univ F).card = Fintype.card J + 1 := by rw [Finset.card_insert_of_notMem hfull, hcard]
    have hch : ∀ s ∈ insert Finset.univ F, chamber (enc s) := by
      intro s hs
      rcases Finset.mem_insert.mp hs with rfl | hs
      · simpa [enc] using htop
      · exact hF s hs
    have h := boundedChainSimplices_of_boolean_chain N chamber y hy (insert Finset.univ F) hc hcs hch
    apply Finset.mem_filter.mpr
    refine ⟨?_, Finset.subset_insert _ _⟩
    simpa [Finset.image_insert, enc, top, V] using h
  have hnew : insert bot V ∈ K := by
    apply Finset.mem_filter.mpr
    exact ⟨boundedChainSimplices_top_shift N chamber y z a hy hz hzy F hcard ha hchain hF hbot,
      Finset.subset_insert _ _⟩
  have htopV : top ∉ V := by
    intro hv
    obtain ⟨s, hs, he⟩ := Finset.mem_image.mp hv
    have h := congrArg Fin.val (congrFun he a)
    simp [enc, top, ha s hs] at h
  have hne : insert top V ≠ insert bot V := by
    intro h
    have hm : top ∈ insert bot V := h ▸ Finset.mem_insert_self top V
    rcases Finset.mem_insert.mp hm with he | he
    · have hv := congrArg Fin.val (congrFun he a)
      have hh := hzy a
      simp [bot, top] at hv
      simp at hh
      omega
    · exact htopV he
  have hge : 2 ≤ K.card := Finset.one_lt_card.mpr ⟨_, hold, _, hnew, hne⟩
  exact Nat.le_antisymm hle hge

/-- At the outer upper grid wall, a bottom endpoint facet with an existing
incident simplex is incident to exactly one simplex. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boundedChainSimplices_bottom_outer_incident_one {J : Type*} [Fintype J] [DecidableEq J]
    (N : ℕ) (chamber : (J → Fin (N+1)) → Prop)
    (y : J → ℕ) (a : J) (F T : Finset (J → Fin (N+1)))
    (hcard : F.card = Fintype.card J)
    (L H : J → Fin (N+1)) (hL : L ∈ F) (hH : H ∈ F)
    (hLv : ∀ i, (L i).val = y i + if i = a then 1 else 0)
    (hHv : ∀ i, (H i).val = y i + 1)
    (hFa : ∀ v ∈ F, (v a).val = y a + 1)
    (hwall : y a + 1 = N)
    (hT : T ∈ boundedChainSimplices N (Fintype.card J) chamber) (hFT : F ⊆ T) :
    ((boundedChainSimplices N (Fintype.card J) chamber).filter (fun T => F ⊆ T)).card = 1 := by
  classical
  apply Nat.le_antisymm
  · apply boundedChainSimplices_bottom_incident_le_one N chamber y a F hcard L H hL hH hLv hHv hFa
    intro x hx _
    have h := hx a
    have hxbound := (x a).isLt
    simp at h
    omega
  · apply Finset.one_le_card.mpr
    exact ⟨T, Finset.mem_filter.mpr ⟨hT, hFT⟩⟩

/-- At the outer lower grid wall, a top endpoint facet with an existing
incident simplex is incident to exactly one simplex. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boundedChainSimplices_top_outer_incident_one {J : Type*} [Fintype J] [DecidableEq J]
    (N : ℕ) (chamber : (J → Fin (N+1)) → Prop)
    (y : J → ℕ) (a : J) (F T : Finset (J → Fin (N+1)))
    (hcard : F.card = Fintype.card J)
    (L H : J → Fin (N+1)) (hL : L ∈ F) (hH : H ∈ F)
    (hLv : ∀ i, (L i).val = y i)
    (hHv : ∀ i, (H i).val = y i + if i = a then 0 else 1)
    (hFa : ∀ v ∈ F, (v a).val = y a)
    (hwall : y a = 0)
    (hT : T ∈ boundedChainSimplices N (Fintype.card J) chamber) (hFT : F ⊆ T) :
    ((boundedChainSimplices N (Fintype.card J) chamber).filter (fun T => F ⊆ T)).card = 1 := by
  classical
  apply Nat.le_antisymm
  · apply boundedChainSimplices_top_incident_le_one N chamber y a F hcard L H hL hH hLv hHv hFa
    intro x hx _
    have h := hx a
    simp at h
    omega
  · apply Finset.one_le_card.mpr
    exact ⟨T, Finset.mem_filter.mpr ⟨hT, hFT⟩⟩

/-- An existing bottom-endpoint facet has exactly one incident simplex if its
shifted completion is not chamber-admissible. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boundedChainSimplices_bottom_inadmissible_incident_one {J : Type*} [Fintype J] [DecidableEq J]
    (N : ℕ) (chamber : (J → Fin (N+1)) → Prop)
    (y : J → ℕ) (a : J) (F T : Finset (J → Fin (N+1)))
    (hcard : F.card = Fintype.card J)
    (L H : J → Fin (N+1)) (hL : L ∈ F) (hH : H ∈ F)
    (hLv : ∀ i, (L i).val = y i + if i = a then 1 else 0)
    (hHv : ∀ i, (H i).val = y i + 1)
    (hFa : ∀ v ∈ F, (v a).val = y a + 1)
    (hno : ∀ x : J → Fin (N+1),
      (∀ i, (x i).val = (y i + if i = a then 1 else 0) + 1) → ¬ chamber x)
    (hT : T ∈ boundedChainSimplices N (Fintype.card J) chamber) (hFT : F ⊆ T) :
    ((boundedChainSimplices N (Fintype.card J) chamber).filter (fun T => F ⊆ T)).card = 1 := by
  classical
  apply Nat.le_antisymm
  · exact boundedChainSimplices_bottom_incident_le_one N chamber y a F hcard L H hL hH hLv hHv hFa hno
  · exact Finset.one_le_card.mpr ⟨T, Finset.mem_filter.mpr ⟨hT, hFT⟩⟩

/-- An existing top-endpoint facet has exactly one incident simplex if its
shifted completion is not chamber-admissible. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boundedChainSimplices_top_inadmissible_incident_one {J : Type*} [Fintype J] [DecidableEq J]
    (N : ℕ) (chamber : (J → Fin (N+1)) → Prop)
    (y : J → ℕ) (a : J) (F T : Finset (J → Fin (N+1)))
    (hcard : F.card = Fintype.card J)
    (L H : J → Fin (N+1)) (hL : L ∈ F) (hH : H ∈ F)
    (hLv : ∀ i, (L i).val = y i)
    (hHv : ∀ i, (H i).val = y i + if i = a then 0 else 1)
    (hFa : ∀ v ∈ F, (v a).val = y a)
    (hno : ∀ x : J → Fin (N+1),
      (∀ i, (x i).val + (if i = a then 1 else 0) = y i) → ¬ chamber x)
    (hT : T ∈ boundedChainSimplices N (Fintype.card J) chamber) (hFT : F ⊆ T) :
    ((boundedChainSimplices N (Fintype.card J) chamber).filter (fun T => F ⊆ T)).card = 1 := by
  classical
  apply Nat.le_antisymm
  · exact boundedChainSimplices_top_incident_le_one N chamber y a F hcard L H hL hH hLv hHv hFa hno
  · exact Finset.one_le_card.mpr ⟨T, Finset.mem_filter.mpr ⟨hT, hFT⟩⟩
open Finset

/-- Deleting rank zero from a saturated Boolean chain leaves a chain containing
its singleton and full endpoints, with the singleton in every remaining vertex. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem deleted_bottom_boolean_chain {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (hn : n = Fintype.card J) (hp : 0 < n)
    (c : Fin (n+1) → Finset J) (hc : Monotone c)
    (hr : ∀ k, (c k).card = k.val) :
    ∃ a : J, let F := (Finset.univ.erase (⟨0, by omega⟩ : Fin (n+1))).image c
      F.card = Fintype.card J ∧
      (∀ s ∈ F, a ∈ s) ∧
      (∀ s ∈ F, ∀ t ∈ F, s ⊆ t ∨ t ⊆ s) ∧
      {a} ∈ F ∧ Finset.univ ∈ F := by
  classical
  let i : Fin (n+1) := ⟨1, by omega⟩
  have hi : (c i).card = 1 := by simpa [i] using hr i
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hi
  refine ⟨a, ?_⟩
  dsimp only
  have hinj : Function.Injective c := by
    intro j k h
    apply Fin.ext
    have h' := congrArg Finset.card h
    simpa [hr] using h'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_iff.mpr (fun _ _ _ _ h => hinj h), Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  · intro s hs
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hs
    have hj0 : j ≠ 0 := (Finset.mem_erase.mp hj).1
    have hji : i ≤ j := by
      apply Fin.le_def.mpr
      have hval : j.val ≠ 0 := by intro h; apply hj0; exact Fin.ext h
      dsimp [i]; omega
    have := hc hji
    rw [ha] at this
    exact this (Finset.mem_singleton_self a)
  · intro s hs t ht
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp ht
    rcases le_total j k with h | h
    · exact Or.inl (hc h)
    · exact Or.inr (hc h)
  · apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, ha⟩
    intro h
    have := congrArg Fin.val h
    simp [i] at this
  · let top : Fin (n+1) := ⟨n, by omega⟩
    have htop : c top = Finset.univ := by
      apply Finset.eq_univ_of_card
      simpa [top, hn] using hr top
    apply Finset.mem_image.mpr
    refine ⟨top, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, htop⟩
    intro h
    have h' := congrArg Fin.val h
    simp [top] at h'
    omega

/-- Deleting the top rank leaves the empty and co-singleton endpoints and
excludes one common coordinate from all remaining Boolean vertices. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem deleted_top_boolean_chain {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (hn : n = Fintype.card J) (hp : 0 < n)
    (c : Fin (n+1) → Finset J) (hc : Monotone c)
    (hr : ∀ k, (c k).card = k.val) :
    ∃ a : J, let F := (Finset.univ.erase (⟨n, by omega⟩ : Fin (n+1))).image c
      F.card = Fintype.card J ∧
      (∀ s ∈ F, a ∉ s) ∧
      (∀ s ∈ F, ∀ t ∈ F, s ⊆ t ∨ t ⊆ s) ∧
      ∅ ∈ F ∧ Finset.univ.erase a ∈ F := by
  classical
  let i : Fin (n+1) := ⟨n-1, by omega⟩
  have hi : (Finset.univ \ c i).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _), Finset.card_univ, hr]
    simp only [i]
    omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hi
  have hia : a ∉ c i := by
    have : a ∈ Finset.univ \ c i := ha.symm ▸ Finset.mem_singleton_self a
    exact (Finset.mem_sdiff.mp this).2
  have hic : c i = Finset.univ.erase a := by
    ext x
    have hx : x ∈ Finset.univ \ c i ↔ x = a := by rw [ha]; simp
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    tauto
  refine ⟨a, ?_⟩
  dsimp only
  have hinj : Function.Injective c := by
    intro j k h
    apply Fin.ext
    have h' := congrArg Finset.card h
    simpa [hr] using h'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_iff.mpr (fun _ _ _ _ h => hinj h), Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  · intro s hs
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hs
    have hjtop : j ≠ (⟨n, by omega⟩ : Fin (n+1)) := (Finset.mem_erase.mp hj).1
    have hji : j ≤ i := by
      apply Fin.le_def.mpr
      have hjn : j.val ≠ n := by intro h; apply hjtop; exact Fin.ext h
      have hjbound := j.isLt
      dsimp [i]; omega
    exact fun h => hia (hc hji h)
  · intro s hs t ht
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp ht
    rcases le_total j k with h | h
    · exact Or.inl (hc h)
    · exact Or.inr (hc h)
  · let bot : Fin (n+1) := ⟨0, by omega⟩
    have hbot : c bot = ∅ := by
      apply Finset.card_eq_zero.mp
      simpa [bot] using hr bot
    apply Finset.mem_image.mpr
    refine ⟨bot, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, hbot⟩
    intro h
    have h' := congrArg Fin.val h
    simp [bot] at h'
    omega
  · apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, hic⟩
    intro h
    have h' := congrArg Fin.val h
    simp [i] at h'
    omega

/-- Every actual codimension-one facet has a bounded Boolean-chain encoding,
with the original simplex supplying an incident witness. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem actual_facet_boolean_encoding {J : Type*} [Fintype J] [DecidableEq J]
    (N : ℕ) (chamber : (J → Fin (N+1)) → Prop)
    (T F : Finset (J → Fin (N+1)))
    (hT : T ∈ boundedChainSimplices N (Fintype.card J) chamber)
    (hFT : F ⊆ T) (hF : F.card = Fintype.card J) :
    ∃ (y : J → ℕ) (hy : ∀ i, y i + 1 ≤ N)
      (c : Fin (Fintype.card J + 1) → Finset J)
      (k : Fin (Fintype.card J + 1)),
      Monotone c ∧ (∀ j, (c j).card = j.val) ∧
      let enc : Finset J → J → Fin (N+1) := fun s i =>
        ⟨y i + if i ∈ s then 1 else 0, by have := hy i; split_ifs <;> omega⟩
      T = Finset.univ.image (fun j => enc (c j)) ∧
      F = ((Finset.univ.erase k).image c).image enc ∧
      (∀ j, chamber (enc (c j))) := by
  classical
  obtain ⟨y, c, v, k, hc, hr, hv, hch, hTv, hFv⟩ :=
    boundedChainSimplices_facet N (Fintype.card J) chamber T F hT hFT hF
  let top : Fin (Fintype.card J + 1) := ⟨Fintype.card J, by omega⟩
  have htop : c top = Finset.univ := by
    apply Finset.eq_univ_of_card
    simpa [top] using hr top
  have hy : ∀ i, y i + 1 ≤ N := by
    intro i
    have h := (v top i).isLt
    rw [hv, htop] at h
    simp only [Finset.mem_univ, ite_true] at h
    omega
  let enc : Finset J → J → Fin (N+1) := fun s i =>
    ⟨y i + if i ∈ s then 1 else 0, by have := hy i; split_ifs <;> omega⟩
  have heq : ∀ j, v j = enc (c j) := by
    intro j
    funext i
    apply Fin.ext
    exact hv j i
  refine ⟨y, hy, c, k, hc, hr, ?_, ?_, ?_⟩
  · change T = Finset.univ.image (fun j => enc (c j))
    rw [hTv]
    congr 1
    funext j
    exact heq j
  · rw [hFv, Finset.image_image]
    congr 1
    funext j
    exact heq j
  · intro j
    change chamber (enc (c j))
    rw [← heq]
    exact hch j

/-- A bottom-rank facet of an actual encoded simplex has one or two
incident simplices, without additional chamber hypotheses. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem actual_bottom_facet_incidence_bounds {J : Type*} [Fintype J] [DecidableEq J]
    (N : ℕ) (chamber : (J → Fin (N+1)) → Prop)
    (y : J → ℕ) (hy : ∀ i, y i + 1 ≤ N)
    (c : Fin (Fintype.card J+1) → Finset J)
    (hc : Monotone c) (hr : ∀ k, (c k).card = k.val)
    (hp : 0 < Fintype.card J)
    (hch : ∀ k, chamber (fun i => ⟨y i + if i ∈ c k then 1 else 0, by
      have := hy i; split_ifs <;> omega⟩)) :
    let enc : Finset J → J → Fin (N+1) := fun s i =>
      ⟨y i + if i ∈ s then 1 else 0, by have := hy i; split_ifs <;> omega⟩
    let F := ((Finset.univ.erase (0 : Fin (Fintype.card J+1))).image c).image enc
    1 ≤ ((boundedChainSimplices N (Fintype.card J) chamber).filter (fun T => F ⊆ T)).card ∧
    ((boundedChainSimplices N (Fintype.card J) chamber).filter (fun T => F ⊆ T)).card ≤ 2 := by
  classical
  dsimp only
  let enc : Finset J → J → Fin (N+1) := fun s i =>
    ⟨y i + if i ∈ s then 1 else 0, by have := hy i; split_ifs <;> omega⟩
  let B := (Finset.univ.erase (0 : Fin (Fintype.card J+1))).image c
  let F := B.image enc
  have hinj : Function.Injective enc := by
    intro s t h
    ext i
    have hh := congrArg Fin.val (congrFun h i)
    change y i + (if i ∈ s then 1 else 0) = y i + (if i ∈ t then 1 else 0) at hh
    by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all
  obtain ⟨a, hcard, ha, hchain, hsingle, huniv⟩ :=
    deleted_bottom_boolean_chain (Fintype.card J) rfl hp c hc hr
  change B.card = Fintype.card J at hcard
  change ∀ s ∈ B, a ∈ s at ha
  change {a} ∈ B at hsingle
  change Finset.univ ∈ B at huniv
  have hFc : F.card = Fintype.card J := by
    rw [show F = B.image enc from rfl, Finset.card_image_iff.mpr (fun _ _ _ _ h => hinj h), hcard]
  constructor
  · apply Finset.card_pos.mpr
    let T := Finset.univ.image (fun k => enc (c k))
    have hT : T ∈ boundedChainSimplices N (Fintype.card J) chamber := by
      classical
      simp only [boundedChainSimplices, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨y, c, (fun k => enc (c k)), hc, hr, ?_, ?_, rfl⟩
      · intro k i; rfl
      · exact hch
    refine ⟨T, Finset.mem_filter.mpr ⟨hT, ?_⟩⟩
    intro v hv
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  · apply boundedChainSimplices_bottom_incident_le_two N chamber y a F hFc (enc {a}) (enc Finset.univ)
    · exact Finset.mem_image.mpr ⟨_, hsingle, rfl⟩
    · exact Finset.mem_image.mpr ⟨_, huniv, rfl⟩
    · intro i; simp [enc, eq_comm]
    · intro i; simp [enc]
    · intro v hv
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hv
      simp [enc, ha s hs]

/-- A top-rank facet of an actual encoded simplex has one or two
incident simplices, without additional chamber hypotheses. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem actual_top_facet_incidence_bounds {J : Type*} [Fintype J] [DecidableEq J]
    (N : ℕ) (chamber : (J → Fin (N+1)) → Prop)
    (y : J → ℕ) (hy : ∀ i, y i + 1 ≤ N)
    (c : Fin (Fintype.card J+1) → Finset J)
    (hc : Monotone c) (hr : ∀ k, (c k).card = k.val)
    (hp : 0 < Fintype.card J)
    (hch : ∀ k, chamber (fun i => ⟨y i + if i ∈ c k then 1 else 0, by
      have := hy i; split_ifs <;> omega⟩)) :
    let enc : Finset J → J → Fin (N+1) := fun s i =>
      ⟨y i + if i ∈ s then 1 else 0, by have := hy i; split_ifs <;> omega⟩
    let F := ((Finset.univ.erase (⟨Fintype.card J, by omega⟩ : Fin (Fintype.card J+1))).image c).image enc
    1 ≤ ((boundedChainSimplices N (Fintype.card J) chamber).filter (fun T => F ⊆ T)).card ∧
    ((boundedChainSimplices N (Fintype.card J) chamber).filter (fun T => F ⊆ T)).card ≤ 2 := by
  classical
  dsimp only
  let enc : Finset J → J → Fin (N+1) := fun s i =>
    ⟨y i + if i ∈ s then 1 else 0, by have := hy i; split_ifs <;> omega⟩
  let B := (Finset.univ.erase (⟨Fintype.card J, by omega⟩ : Fin (Fintype.card J+1))).image c
  let F := B.image enc
  have hinj : Function.Injective enc := by
    intro s t h
    ext i
    have hh := congrArg Fin.val (congrFun h i)
    change y i + (if i ∈ s then 1 else 0) = y i + (if i ∈ t then 1 else 0) at hh
    by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all
  obtain ⟨a, hcard, ha, hchain, hsingle, huniv⟩ :=
    deleted_top_boolean_chain (Fintype.card J) rfl hp c hc hr
  change B.card = Fintype.card J at hcard
  change ∀ s ∈ B, a ∉ s at ha
  change ∅ ∈ B at hsingle
  change Finset.univ.erase a ∈ B at huniv
  have hFc : F.card = Fintype.card J := by
    rw [show F = B.image enc from rfl, Finset.card_image_iff.mpr (fun _ _ _ _ h => hinj h), hcard]
  constructor
  · apply Finset.card_pos.mpr
    let T := Finset.univ.image (fun k => enc (c k))
    have hT : T ∈ boundedChainSimplices N (Fintype.card J) chamber := by
      classical
      simp only [boundedChainSimplices, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨y, c, (fun k => enc (c k)), hc, hr, ?_, ?_, rfl⟩
      · intro k i; rfl
      · exact hch
    refine ⟨T, Finset.mem_filter.mpr ⟨hT, ?_⟩⟩
    intro v hv
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  · apply boundedChainSimplices_top_incident_le_two N chamber y a F hFc (enc ∅) (enc (Finset.univ.erase a))
    · exact Finset.mem_image.mpr ⟨_, hsingle, rfl⟩
    · exact Finset.mem_image.mpr ⟨_, huniv, rfl⟩
    · intro i; simp [enc]
    · intro i; by_cases h : i = a <;> simp [enc, h, eq_comm]
    · intro v hv
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hv
      simp [enc, ha s hs]
/-- Auxiliary boolean gap fill chain result for the lattice construction.
The proof uses the preceding finite, order, and continuity lemmas as applicable. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boolean_gap_fill_chain {J : Type*} [DecidableEq J]
    (F : Finset (Finset J)) (u v w : Finset J)
    (hchain : ∀ a ∈ F, ∀ b ∈ F, a ⊆ b ∨ b ⊆ a)
    (hgap : ∀ a ∈ F, a ⊆ u ∨ v ⊆ a)
    (huw : u ⊆ w) (hwv : w ⊆ v) :
    ∀ a ∈ insert w F, ∀ b ∈ insert w F, a ⊆ b ∨ b ⊆ a := by
  intro a ha b hb
  simp only [Finset.mem_insert] at ha hb
  rcases ha with ha | ha
  · subst a
    rcases hb with hb | hb
    · subst b; exact Or.inl (Finset.Subset.refl _)
    · rcases hgap b hb with h | h
      · exact Or.inr (h.trans huw)
      · exact Or.inl (hwv.trans h)
  · rcases hb with hb | hb
    · subst b
      rcases hgap a ha with h | h
      · exact Or.inl (h.trans huw)
      · exact Or.inr (hwv.trans h)
    · exact hchain a ha b hb

/-- A missing rank certifies that an intermediate vertex is not already in a facet. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boolean_gap_fill_not_mem {J : Type*} [DecidableEq J]
    (F : Finset (Finset J)) (w : Finset J) (r : ℕ)
    (hmissing : ∀ a ∈ F, a.card ≠ r) (hw : w.card = r) : w ∉ F := by
  intro h
  exact hmissing w h hw

/-- Replacing one point in a monotone chain preserves monotonicity exactly

possible intermediate subsets. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boolean_interval_middle {α : Type*} [DecidableEq α] (u v w : Finset α)
    (huv : u ⊆ v) (huw : u ⊆ w) (hwv : w ⊆ v)
    (hv : v.card = u.card + 2) (hw : w.card = u.card + 1) :
    ∃ a b, a ≠ b ∧ a ∉ u ∧ b ∉ u ∧ v = insert a (insert b u) ∧
      (w = insert a u ∨ w = insert b u) := by
  have hd : (v \ u).card = 2 := by rw [Finset.card_sdiff, Finset.inter_eq_left.mpr huv]; omega
  obtain ⟨a, b, hab, hdiff⟩ := Finset.card_eq_two.mp hd
  have ha : a ∈ v \ u := by rw [hdiff]; simp
  have hb : b ∈ v \ u := by rw [hdiff]; simp [hab.symm]
  have hav : a ∈ v := (Finset.mem_sdiff.mp ha).1
  have hau : a ∉ u := (Finset.mem_sdiff.mp ha).2
  have hbv : b ∈ v := (Finset.mem_sdiff.mp hb).1
  have hbu : b ∉ u := (Finset.mem_sdiff.mp hb).2
  have hv' : v = insert a (insert b u) := by
    ext x
    have hx : x ∈ v ↔ x ∈ v \ u ∨ x ∈ u := by
      simp only [Finset.mem_sdiff]; constructor
      · intro hx; by_cases hu : x ∈ u <;> simp_all
      · rintro (⟨h, _⟩ | h); exact h; exact huv h
    rw [hx, hdiff]
    simp [or_assoc]
  have hwd : (w \ u).card = 1 := by rw [Finset.card_sdiff, Finset.inter_eq_left.mpr huw]; omega
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hwd
  have hcsub : w \ u ⊆ v \ u := by
    intro x hx
    simp only [Finset.mem_sdiff] at hx ⊢
    exact ⟨hwv hx.1, hx.2⟩
  rw [hc, hdiff] at hcsub
  have hc' : c = a ∨ c = b := by
    have := hcsub (by simp : c ∈ ({c} : Finset α))
    simpa using this
  have hw' : w = insert c u := by
    ext x
    have hx : x ∈ w ↔ x ∈ w \ u ∨ x ∈ u := by
      simp only [Finset.mem_sdiff]; constructor
      · intro hx; by_cases hu : x ∈ u <;> simp_all
      · rintro (⟨h, _⟩ | h); exact h; exact huw h
    rw [hx, hc]; simp [or_comm]
  exact ⟨a, b, hab, hau, hbu, hv', by rcases hc' with rfl | rfl <;> simp [hw']⟩

/-- The two rank-one intermediates of a Boolean interval are distinct. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boolean_two_intermediates_ne {α : Type*} [DecidableEq α] (u : Finset α)
    (a b : α) (hab : a ≠ b) (hau : a ∉ u) (hbu : b ∉ u) :
    insert a u ≠ insert b u := by
  intro h
  have ha : a ∈ insert b u := h ▸ Finset.mem_insert_self a u
  simp [hab, hau] at ha

/-- A two-step Boolean interval has precisely two intermediate sets. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boolean_interval_intermediates {α : Type*} [DecidableEq α] (u : Finset α)
    (a b : α) (hab : a ≠ b) (hau : a ∉ u) (hbu : b ∉ u) :
    ((insert a (insert b u)).powerset.filter
      (fun w => u ⊆ w ∧ w.card = u.card + 1)) = {insert a u, insert b u} := by
  classical
  ext w
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hwv, huw, hw⟩
    have hwd : (w \ u).card = 1 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr huw]; omega
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hwd
    have hcw : c ∈ w := (Finset.mem_sdiff.mp (hc ▸ (by simp : c ∈ ({c} : Finset α)))).1
    have hcu : c ∉ u := (Finset.mem_sdiff.mp (hc ▸ (by simp : c ∈ ({c} : Finset α)))).2
    have hcv := hwv hcw
    simp only [Finset.mem_insert] at hcv
    have hw' : w = insert c u := by
      ext x
      have hx : x ∈ w ↔ x ∈ w \ u ∨ x ∈ u := by
        simp only [Finset.mem_sdiff]; constructor
        · intro hx; by_cases hu : x ∈ u <;> simp_all
        · rintro (⟨h, _⟩ | h); exact h; exact huw h
      rw [hx, hc]; simp
    rcases hcv with rfl | rfl | hcU
    · exact Or.inl hw'
    · exact Or.inr hw'
    · exact (hcu hcU).elim
  · rintro (rfl | rfl)
    · simp [hau, hab, hbu, Finset.subset_insert]
    · simp [hau, hab, hbu, Finset.subset_insert]

/-- Consequently, before imposing chamber walls, an interior chain gap has
exactly two filling vertices. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boolean_interval_intermediates_card {α : Type*} [DecidableEq α] (u : Finset α)
    (a b : α) (hab : a ≠ b) (hau : a ∉ u) (hbu : b ∉ u) :
    ((insert a (insert b u)).powerset.filter
      (fun w => u ⊆ w ∧ w.card = u.card + 1)).card = 2 := by
  rw [boolean_interval_intermediates u a b hab hau hbu]
  exact Finset.card_pair (boolean_two_intermediates_ne u a b hab hau hbu)

/-- Auxiliary boolean chain gap forced result for the lattice construction.
The proof uses the preceding finite, order, and continuity lemmas as applicable. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boolean_chain_gap_forced {J : Type*} [DecidableEq J]
    (F : Finset (Finset J)) (u v w : Finset J) (r : ℕ)
    (hu : u ∈ F) (hv : v ∈ F) (huc : u.card + 1 = r)
    (hvc : v.card = r + 1) (hwc : w.card = r)
    (hchain : ∀ a ∈ insert w F, ∀ b ∈ insert w F, a ⊆ b ∨ b ⊆ a) :
    u ⊆ w ∧ w ⊆ v := by
  have hu' : u ∈ insert w F := Finset.mem_insert_of_mem hu
  have hv' : v ∈ insert w F := Finset.mem_insert_of_mem hv
  have hw' : w ∈ insert w F := Finset.mem_insert_self _ _
  constructor
  · rcases hchain u hu' w hw' with h | h
    · exact h
    · have hh := Finset.card_le_card h
      omega
  · rcases hchain w hw' v hv' with h | h
    · exact h
    · have hh := Finset.card_le_card h
      omega

/-- Auxiliary boolean facet interior constrained result for the lattice construction.
The proof uses the preceding finite, order, and continuity lemmas as applicable. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boolean_facet_interior_constrained {J : Type*} [Fintype J] [DecidableEq J]
    (F : Finset (Finset J)) (u : Finset J) (a b : J) (r : ℕ)
    (hab : a ≠ b) (ha : a ∉ u) (hb : b ∉ u)
    (hu : u ∈ F) (hv : insert a (insert b u) ∈ F)
    (huc : u.card + 1 = r) (hr : r ≤ Fintype.card J)
    (hmissing : ∀ x ∈ F, x.card ≠ r)
    (hFcard : F.card = Fintype.card J)
    (hFchain : ∀ x ∈ F, ∀ y ∈ F, x ⊆ y ∨ y ⊆ x)
    (hgap : ∀ x ∈ F, x ⊆ u ∨ insert a (insert b u) ⊆ x)
    (P : Finset J → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun w : Finset J => w ∉ F ∧
      (insert w F).card = Fintype.card J + 1 ∧
      (∀ x ∈ insert w F, ∀ y ∈ insert w F, x ⊆ y ∨ y ⊆ x) ∧ P w)) =
    ({insert a u, insert b u} : Finset (Finset J)).filter P := by
  classical
  have hvc : (insert a (insert b u)).card = r + 1 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, ha]), Finset.card_insert_of_notMem hb]
    omega
  have heq : (Finset.univ.filter (fun w : Finset J => w ∉ F ∧
      (insert w F).card = Fintype.card J + 1 ∧
      (∀ x ∈ insert w F, ∀ y ∈ insert w F, x ⊆ y ∨ y ⊆ x) ∧ P w)) =
      ((insert a (insert b u)).powerset.filter
        (fun w => u ⊆ w ∧ w.card = u.card + 1)).filter P := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset]
    constructor
    · rintro ⟨hn, hc, hch, hp⟩
      have hwc := boolean_missing_rank_forced F w r hr hmissing hch hc
      have h := boolean_chain_gap_forced F u (insert a (insert b u)) w r hu hv huc hvc hwc hch
      exact ⟨⟨h.2, h.1, by omega⟩, hp⟩
    · rintro ⟨⟨hwv, huw, hwc⟩, hp⟩
      have hnot : w ∉ F := boolean_gap_fill_not_mem F w r hmissing (by omega)
      exact ⟨hnot, by simp [hnot, hFcard], boolean_gap_fill_chain F u _ w hFchain hgap huw hwv, hp⟩
  rw [heq, boolean_interval_intermediates u a b hab ha hb]

/-- Removing an interior rank from a saturated Boolean chain creates a two-step gap. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem deleted_interior_boolean_chain {J : Type*} [Fintype J] [DecidableEq J]
    (n r : ℕ) (hn : n = Fintype.card J) (hr0 : 0 < r) (hrn : r < n)
    (c : Fin (n+1) → Finset J) (hc : Monotone c)
    (hr : ∀ k, (c k).card = k.val) :
    let F := (Finset.univ.erase (⟨r, by omega⟩ : Fin (n+1))).image c
    ∃ u : Finset J, ∃ a b : J,
      a ≠ b ∧ a ∉ u ∧ b ∉ u ∧ u ∈ F ∧ insert a (insert b u) ∈ F ∧
      u.card + 1 = r ∧ r ≤ Fintype.card J ∧
      (∀ x ∈ F, x.card ≠ r) ∧ F.card = Fintype.card J ∧
      (∀ x ∈ F, ∀ z ∈ F, x ⊆ z ∨ z ⊆ x) ∧
      (∀ x ∈ F, x ⊆ u ∨ insert a (insert b u) ⊆ x) ∧
      ∅ ∈ F ∧ Finset.univ ∈ F := by
  classical
  let lo : Fin (n+1) := ⟨r-1, by omega⟩
  let hi : Fin (n+1) := ⟨r+1, by omega⟩
  let u := c lo
  let v := c hi
  have huv : u ⊆ v := hc (by apply Fin.le_def.mpr; dsimp [lo,hi]; omega)
  have hd : (v \ u).card = 2 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr huv]
    have h1 := hr lo; have h2 := hr hi
    dsimp [u,v,lo,hi] at *; omega
  obtain ⟨a,b,hab,habset⟩ := Finset.card_eq_two.mp hd
  have ha : a ∉ u := by
    have : a ∈ v \ u := habset.symm ▸ (by simp : a ∈ ({a,b} : Finset J))
    exact (Finset.mem_sdiff.mp this).2
  have hb : b ∉ u := by
    have : b ∈ v \ u := habset.symm ▸ (by simp : b ∈ ({a,b} : Finset J))
    exact (Finset.mem_sdiff.mp this).2
  have hv : v = insert a (insert b u) := by
    ext x
    have hx : x ∈ v ↔ x ∈ v \ u ∨ x ∈ u := by
      simp only [Finset.mem_sdiff]; constructor
      · intro hx; by_cases h : x ∈ u <;> simp_all
      · rintro (⟨h, _⟩ | h); exact h; exact huv h
    rw [hx, habset]; simp; tauto
  have hinj : Function.Injective c := by
    intro i j h; apply Fin.ext
    have h' := congrArg Finset.card h
    simpa [hr] using h'
  dsimp only
  refine ⟨u,a,b,hab,ha,hb,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact Finset.mem_image.mpr ⟨lo, Finset.mem_erase.mpr ⟨by intro h; have := congrArg Fin.val h; dsimp [lo] at this; omega, Finset.mem_univ _⟩, rfl⟩
  · apply Finset.mem_image.mpr
    exact ⟨hi, Finset.mem_erase.mpr ⟨by intro h; have := congrArg Fin.val h; dsimp [hi] at this; omega, Finset.mem_univ _⟩, hv⟩
  · change (c lo).card + 1 = r
    rw [hr]; dsimp [lo]; omega
  · omega
  · intro x hx
    obtain ⟨i,hi',rfl⟩ := Finset.mem_image.mp hx
    have hne := (Finset.mem_erase.mp hi').1
    rw [hr]; intro h; apply hne; exact Fin.ext h
  · rw [Finset.card_image_iff.mpr (fun _ _ _ _ h => hinj h), Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]; omega
  · intro x hx z hz
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hz
    rcases le_total i j with h | h
    · exact Or.inl (hc h)
    · exact Or.inr (hc h)
  · intro x hx
    obtain ⟨i,hi',rfl⟩ := Finset.mem_image.mp hx
    have hne := (Finset.mem_erase.mp hi').1
    have hvne : i.val ≠ r := by intro h; exact hne (Fin.ext h)
    by_cases h : i.val < r
    · left; exact hc (by apply Fin.le_def.mpr; dsimp [lo]; omega)
    · right; rw [← hv]; exact hc (by apply Fin.le_def.mpr; dsimp [hi]; omega)
  · let bot : Fin (n+1) := ⟨0, by omega⟩
    have hb : c bot = ∅ := Finset.card_eq_zero.mp (by simpa [bot] using hr bot)
    exact Finset.mem_image.mpr ⟨bot, Finset.mem_erase.mpr ⟨by intro h; have := congrArg Fin.val h; dsimp [bot] at this; omega, Finset.mem_univ _⟩, hb⟩
  · let top : Fin (n+1) := ⟨n, by omega⟩
    have ht : c top = Finset.univ := by
      apply Finset.eq_univ_of_card
      simpa [top, hn] using hr top
    exact Finset.mem_image.mpr ⟨top, Finset.mem_erase.mpr ⟨by intro h; have := congrArg Fin.val h; dsimp [top] at this; omega, Finset.mem_univ _⟩, ht⟩

/-- An interior-rank facet has one or two chamber-admissible completions. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem actual_interior_facet_incidence_bounds {J : Type*} [Fintype J] [DecidableEq J]
    (N : ℕ) (chamber : (J → Fin (N+1)) → Prop)
    (y : J → ℕ) (hy : ∀ i, y i + 1 ≤ N)
    (c : Fin (Fintype.card J+1) → Finset J)
    (hc : Monotone c) (hr : ∀ k, (c k).card = k.val)
    (r : ℕ) (hr0 : 0 < r) (hrn : r < Fintype.card J)
    (hch : ∀ k, chamber (fun i => ⟨y i + if i ∈ c k then 1 else 0, by
      have := hy i; split_ifs <;> omega⟩)) :
    let enc : Finset J → J → Fin (N+1) := fun s i =>
      ⟨y i + if i ∈ s then 1 else 0, by have := hy i; split_ifs <;> omega⟩
    let F := ((Finset.univ.erase (⟨r, by omega⟩ : Fin (Fintype.card J+1))).image c).image enc
    1 ≤ ((boundedChainSimplices N (Fintype.card J) chamber).filter (fun T => F ⊆ T)).card ∧
    ((boundedChainSimplices N (Fintype.card J) chamber).filter (fun T => F ⊆ T)).card ≤ 2 := by
  classical
  dsimp only
  let enc : Finset J → J → Fin (N+1) := fun s i =>
    ⟨y i + if i ∈ s then 1 else 0, by have := hy i; split_ifs <;> omega⟩
  let B := (Finset.univ.erase (⟨r, by omega⟩ : Fin (Fintype.card J+1))).image c
  let F := B.image enc
  obtain ⟨u,a,b,hab,ha,hb,hu,hv,huc,hrle,hmissing,hcard,hchain,hgap,hbot,htop⟩ :=
    deleted_interior_boolean_chain (Fintype.card J) r rfl hr0 hrn c hc hr
  change u ∈ B at hu
  change insert a (insert b u) ∈ B at hv
  change (∀ x ∈ B, x.card ≠ r) at hmissing
  change B.card = Fintype.card J at hcard
  change (∀ x ∈ B, ∀ z ∈ B, x ⊆ z ∨ z ⊆ x) at hchain
  change (∀ x ∈ B, x ⊆ u ∨ insert a (insert b u) ⊆ x) at hgap
  change ∅ ∈ B at hbot
  change Finset.univ ∈ B at htop
  have hvalid : ∀ s ∈ B, chamber (enc s) := by
    intro s hs
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hs
    exact hch k
  have heq := boundedChainSimplices_interior_incident_card N chamber y hy B hbot htop hcard hvalid
  change ((boundedChainSimplices N (Fintype.card J) chamber).filter (fun T => F ⊆ T)).card = _ at heq
  have hset := boolean_facet_interior_constrained B u a b r hab ha hb hu hv huc hrle hmissing hcard hchain hgap (fun s => chamber (enc s))
  change ((Finset.univ.filter (fun w : Finset J => w ∉ B ∧
      (insert w B).card = Fintype.card J + 1 ∧
      (∀ x ∈ insert w B, ∀ z ∈ insert w B, x ⊆ z ∨ z ⊆ x) ∧ chamber (enc w)))) = _ at hset
  rw [hset] at heq
  constructor
  · apply Finset.card_pos.mpr
    let T := Finset.univ.image (fun k => enc (c k))
    have hT : T ∈ boundedChainSimplices N (Fintype.card J) chamber := by
      simp only [boundedChainSimplices, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨y, c, (fun k => enc (c k)), hc, hr, ?_, ?_, rfl⟩
      · intro k i; rfl
      · exact hch
    refine ⟨T, Finset.mem_filter.mpr ⟨hT, ?_⟩⟩
    intro v hv'
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hv'
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  · rw [heq]
    calc
      _ ≤ ({insert a u, insert b u} : Finset (Finset J)).card := Finset.card_filter_le _ _
      _ ≤ 2 := by simpa using (Finset.card_insert_le (insert a u) ({insert b u} : Finset (Finset J)))

/-- Every facet of an actual bounded chamber simplex in positive dimension
is incident to one or two simplices. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem actual_facet_incidence_bounds {J : Type*} [Fintype J] [DecidableEq J]
    (N : ℕ) (chamber : (J → Fin (N+1)) → Prop)
    (T F : Finset (J → Fin (N+1))) (hp : 0 < Fintype.card J)
    (hT : T ∈ boundedChainSimplices N (Fintype.card J) chamber)
    (hFT : F ⊆ T) (hF : F.card = Fintype.card J) :
    1 ≤ ((boundedChainSimplices N (Fintype.card J) chamber).filter (fun U => F ⊆ U)).card ∧
    ((boundedChainSimplices N (Fintype.card J) chamber).filter (fun U => F ⊆ U)).card ≤ 2 := by
  classical
  obtain ⟨y,hy,c,k,hc,hr,hTv,hFv,hch⟩ := actual_facet_boolean_encoding N chamber T F hT hFT hF
  rw [hFv]
  by_cases hk0 : k.val = 0
  · have hk : k = 0 := Fin.ext hk0
    subst k
    exact actual_bottom_facet_incidence_bounds N chamber y hy c hc hr hp hch
  · by_cases hkt : k.val = Fintype.card J
    · have hk : k = ⟨Fintype.card J, by omega⟩ := Fin.ext hkt
      rw [hk]
      exact actual_top_facet_incidence_bounds N chamber y hy c hc hr hp hch
    · have hr0 : 0 < k.val := by omega
      have hrn : k.val < Fintype.card J := by have := k.isLt; omega
      have hk : k = ⟨k.val, by omega⟩ := Fin.ext rfl
      conv_lhs => rw [hk]
      conv_rhs => rw [hk]
      exact actual_interior_facet_incidence_bounds N chamber y hy c hc hr k.val hr0 hrn hch

/-- A monotone bottom facet with one incident simplex lies on the upper grid wall. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem bottom_incidence_one_outer {J : Type*} [Fintype J] [LinearOrder J]
    (N : ℕ) (y : J → ℕ) (a : J) (hy : ∀ i, y i + 1 ≤ N)
    (F : Finset (Finset J)) (hcard : F.card = Fintype.card J)
    (ha : ∀ s ∈ F, a ∈ s)
    (hchain : ∀ s ∈ F, ∀ t ∈ F, s ⊆ t ∨ t ⊆ s)
    (hsingle : {a} ∈ F) (huniv : Finset.univ ∈ F)
    (hF : ∀ s ∈ F, Monotone (fun i => (⟨y i + if i ∈ s then 1 else 0, by
      have := hy i; split_ifs <;> omega⟩ : Fin (N+1))))
    (hbot : Monotone (fun i => (⟨y i, by have := hy i; omega⟩ : Fin (N+1))))
    (hone : ((boundedChainSimplices N (Fintype.card J) Monotone).filter
      (fun T => F.image (fun s i => (⟨y i + if i ∈ s then 1 else 0, by
        have := hy i; split_ifs <;> omega⟩ : Fin (N+1))) ⊆ T)).card = 1) :
    y a + 1 = N := by
  classical
  by_contra hne
  have hy' : ∀ i, (y i + if i = a then 1 else 0) + 1 ≤ N := by
    intro i
    by_cases h : i = a
    · subst i; simp only [ite_true]; have := hy a; omega
    · simp only [h, ite_false, add_zero]; exact hy i
  have ht : Monotone (fun i => (⟨(y i + if i = a then 1 else 0) + 1, by
      have := hy' i; omega⟩ : Fin (N+1))) := by
    intro i j hij
    have h := hF {a} hsingle hij
    change y i + (if i ∈ ({a} : Finset J) then 1 else 0) ≤
      y j + (if j ∈ ({a} : Finset J) then 1 else 0) at h
    change (y i + if i = a then 1 else 0) + 1 ≤
      (y j + if j = a then 1 else 0) + 1
    simpa only [Finset.mem_singleton] using Nat.add_le_add_right h 1
  have htwo := boundedChainSimplices_bottom_incident_two N Monotone y a hy hy' F hcard ha hchain hsingle huniv hF hbot ht
  dsimp only at htwo
  rw [hone] at htwo
  omega

/-- A monotone top facet with one incident simplex lies on the lower grid wall. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem top_incidence_one_outer {J : Type*} [Fintype J] [LinearOrder J]
    (N : ℕ) (y : J → ℕ) (a : J) (hy : ∀ i, y i + 1 ≤ N)
    (F : Finset (Finset J)) (hcard : F.card = Fintype.card J)
    (ha : ∀ s ∈ F, a ∉ s)
    (hchain : ∀ s ∈ F, ∀ t ∈ F, s ⊆ t ∨ t ⊆ s)
    (hempty : ∅ ∈ F) (hco : Finset.univ \ {a} ∈ F)
    (hF : ∀ s ∈ F, Monotone (fun i => (⟨y i + if i ∈ s then 1 else 0, by
      have := hy i; split_ifs <;> omega⟩ : Fin (N+1))))
    (htop : Monotone (fun i => (⟨y i + 1, by have := hy i; omega⟩ : Fin (N+1))))
    (hone : ((boundedChainSimplices N (Fintype.card J) Monotone).filter
      (fun T => F.image (fun s i => (⟨y i + if i ∈ s then 1 else 0, by
        have := hy i; split_ifs <;> omega⟩ : Fin (N+1))) ⊆ T)).card = 1) :
    y a = 0 := by
  classical
  by_contra hne
  let z : J → ℕ := fun i => if i = a then y i - 1 else y i
  have hzy : ∀ i, z i + (if i = a then 1 else 0) = y i := by
    intro i; by_cases h : i = a <;> simp [z, h] <;> omega
  have hz : ∀ i, z i + 1 ≤ N := by
    intro i; have hh := hy i
    dsimp [z]; split_ifs <;> omega
  have hb : Monotone (fun i => (⟨z i, by have := hz i; omega⟩ : Fin (N+1))) := by
    intro i j hij
    have h := hF (Finset.univ \ {a}) hco hij
    change y i + (if i ∈ Finset.univ \ {a} then 1 else 0) ≤
      y j + (if j ∈ Finset.univ \ {a} then 1 else 0) at h
    change z i ≤ z j
    have hv : ∀ k, z k + 1 = y k + (if k ∈ Finset.univ \ {a} then 1 else 0) := by
      intro k
      dsimp [z]
      by_cases hk : k = a <;> simp [hk] <;> omega
    have hi := hv i
    have hj := hv j
    omega
  have htwo := boundedChainSimplices_top_incident_two N Monotone y z a hy hz hzy F hcard ha hchain hempty hco hF htop hb
  dsimp only at htwo
  rw [hone] at htwo
  omega

/-- An actual bottom endpoint facet with one incident simplex is on the upper grid wall. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem actual_bottom_incidence_one_outer {J : Type*} [Fintype J] [LinearOrder J]
    (N : ℕ) (y : J → ℕ) (hy : ∀ i, y i + 1 ≤ N)
    (c : Fin (Fintype.card J+1) → Finset J)
    (hc : Monotone c) (hr : ∀ k, (c k).card = k.val)
    (hp : 0 < Fintype.card J)
    (hch : ∀ k, Monotone (fun i => (⟨y i + if i ∈ c k then 1 else 0, by
      have := hy i; split_ifs <;> omega⟩ : Fin (N+1))))
    (hone : let enc : Finset J → J → Fin (N+1) := fun s i =>
      ⟨y i + if i ∈ s then 1 else 0, by have := hy i; split_ifs <;> omega⟩
      let G := ((Finset.univ.erase (0 : Fin (Fintype.card J+1))).image c).image enc
      ((boundedChainSimplices N (Fintype.card J) Monotone).filter (fun T => G ⊆ T)).card = 1) :
    let enc : Finset J → J → Fin (N+1) := fun s i =>
      ⟨y i + if i ∈ s then 1 else 0, by have := hy i; split_ifs <;> omega⟩
    let G := ((Finset.univ.erase (0 : Fin (Fintype.card J+1))).image c).image enc
    ∃ a, ∀ v ∈ G, (v a).val = N := by
  classical
  dsimp only at hone ⊢
  let enc : Finset J → J → Fin (N+1) := fun s i =>
    ⟨y i + if i ∈ s then 1 else 0, by have := hy i; split_ifs <;> omega⟩
  let B := (Finset.univ.erase (0 : Fin (Fintype.card J+1))).image c
  obtain ⟨a,hcard,ha,hchain,hsingle,huniv⟩ := deleted_bottom_boolean_chain (Fintype.card J) rfl hp c hc hr
  change B.card = _ at hcard
  change ∀ s ∈ B, a ∈ s at ha
  change {a} ∈ B at hsingle
  change Finset.univ ∈ B at huniv
  have hF : ∀ s ∈ B, Monotone (enc s) := by
    intro s hs; obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hs; exact hch j
  have hc0 : c 0 = ∅ := Finset.card_eq_zero.mp (by simpa using hr 0)
  have hbot : Monotone (fun i => (⟨y i, by have := hy i; omega⟩ : Fin (N+1))) := by
    simpa [enc, hc0] using hch 0
  have hout := bottom_incidence_one_outer N y a hy B hcard ha hchain hsingle huniv hF hbot hone
  refine ⟨a, ?_⟩
  intro v hv
  obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hv
  change y a + (if a ∈ s then 1 else 0) = N
  simpa [ha s hs] using hout

/-- An actual top endpoint facet with one incident simplex is on the lower grid wall. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem actual_top_incidence_one_outer {J : Type*} [Fintype J] [LinearOrder J]
    (N : ℕ) (y : J → ℕ) (hy : ∀ i, y i + 1 ≤ N)
    (c : Fin (Fintype.card J+1) → Finset J)
    (hc : Monotone c) (hr : ∀ k, (c k).card = k.val)
    (hp : 0 < Fintype.card J)
    (hch : ∀ k, Monotone (fun i => (⟨y i + if i ∈ c k then 1 else 0, by
      have := hy i; split_ifs <;> omega⟩ : Fin (N+1))))
    (hone : let enc : Finset J → J → Fin (N+1) := fun s i =>
      ⟨y i + if i ∈ s then 1 else 0, by have := hy i; split_ifs <;> omega⟩
      let G := ((Finset.univ.erase (⟨Fintype.card J, by omega⟩ : Fin (Fintype.card J+1))).image c).image enc
      ((boundedChainSimplices N (Fintype.card J) Monotone).filter (fun T => G ⊆ T)).card = 1) :
    let enc : Finset J → J → Fin (N+1) := fun s i =>
      ⟨y i + if i ∈ s then 1 else 0, by have := hy i; split_ifs <;> omega⟩
    let G := ((Finset.univ.erase (⟨Fintype.card J, by omega⟩ : Fin (Fintype.card J+1))).image c).image enc
    ∃ a, ∀ v ∈ G, (v a).val = 0 := by
  classical
  dsimp only at hone ⊢
  let enc : Finset J → J → Fin (N+1) := fun s i =>
    ⟨y i + if i ∈ s then 1 else 0, by have := hy i; split_ifs <;> omega⟩
  let top : Fin (Fintype.card J+1) := ⟨Fintype.card J, by omega⟩
  let B := (Finset.univ.erase top).image c
  obtain ⟨a,hcard,ha,hchain,hempty,hco⟩ := deleted_top_boolean_chain (Fintype.card J) rfl hp c hc hr
  change B.card = _ at hcard
  change ∀ s ∈ B, a ∉ s at ha
  change ∅ ∈ B at hempty
  have hco' : Finset.univ \ {a} ∈ B := by simpa [B, top, Finset.sdiff_singleton_eq_erase] using hco
  have hF : ∀ s ∈ B, Monotone (enc s) := by
    intro s hs; obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hs; exact hch j
  have hct : c top = Finset.univ := by
    apply Finset.eq_univ_of_card
    simpa [top] using hr top
  have htop : Monotone (fun i => (⟨y i + 1, by have := hy i; omega⟩ : Fin (N+1))) := by
    simpa [enc, hct] using hch top
  have hout := top_incidence_one_outer N y a hy B hcard ha hchain hempty hco' hF htop hone
  refine ⟨a, ?_⟩
  intro v hv
  obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hv
  change y a + (if a ∈ s then 1 else 0) = 0
  simpa [ha s hs] using hout

/-- Every incidence-one facet is on an outer wall or is an interior-rank deleted facet. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem actual_incidence_one_outer_or_interior {J : Type*} [Fintype J] [LinearOrder J]
    (N : ℕ) (T G : Finset (J → Fin (N+1)))
    (hT : T ∈ boundedChainSimplices N (Fintype.card J) Monotone)
    (hGT : G ⊆ T) (hG : G.card = Fintype.card J) (hp : 0 < Fintype.card J)
    (hone : ((boundedChainSimplices N (Fintype.card J) Monotone).filter (fun T => G ⊆ T)).card = 1) :
    (∃ a, ∀ v ∈ G, (v a).val = 0) ∨ (∃ a, ∀ v ∈ G, (v a).val = N) ∨
    ∃ (y : J → ℕ) (c : Fin (Fintype.card J + 1) → Finset J)
      (v : Fin (Fintype.card J + 1) → J → Fin (N+1)) (k : Fin (Fintype.card J + 1)),
      Monotone c ∧ (∀ j, (c j).card = j.val) ∧
      (∀ j i, (v j i).val = y i + if i ∈ c j then 1 else 0) ∧
      (∀ j, Monotone (v j)) ∧ G = (Finset.univ.erase k).image v ∧
      0 < k.val ∧ k.val < Fintype.card J := by
  classical
  obtain ⟨y,hy,c,k,hc,hr,hTv,hGv,hch⟩ := actual_facet_boolean_encoding N Monotone T G hT hGT hG
  let enc : Finset J → J → Fin (N+1) := fun s i =>
    ⟨y i + if i ∈ s then 1 else 0, by have := hy i; split_ifs <;> omega⟩
  by_cases hk0 : k.val = 0
  · have hk : k = 0 := Fin.ext hk0
    subst k
    right; left
    rw [hGv] at hone ⊢
    exact actual_bottom_incidence_one_outer N y hy c hc hr hp hch hone
  · by_cases hkt : k.val = Fintype.card J
    · have hk : k = ⟨Fintype.card J, by omega⟩ := Fin.ext hkt
      rw [hk] at hGv
      left
      rw [hGv] at hone ⊢
      exact actual_top_incidence_one_outer N y hy c hc hr hp hch hone
    · right; right
      refine ⟨y,c,(fun j => enc (c j)),k,hc,hr,?_,hch,?_,by omega,by have := k.isLt; omega⟩
      · intros; rfl
      · rw [hGv, Finset.image_image]
        rfl

/-- Auxiliary coordinate increments injective result for the lattice construction.
The proof uses the preceding finite, order, and continuity lemmas as applicable. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem coordinate_increments_injective {J : Type*} [DecidableEq J]
    (y : J → ℕ) : Function.Injective
      (fun s : Finset J => fun i => y i + if i ∈ s then 1 else 0) := by
  intro s t h
  ext i
  have hi := congrFun h i
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all

/-- Filling a gap preserves a chain provided every old vertex lies at or below
its bottom or at or above its top. -/


@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem monotone_update_iff {I P : Type*} [LinearOrder I] [DecidableEq I]
    [Preorder P] (c : I → P) (hc : Monotone c) (k : I) (w : P) :
    Monotone (Function.update c k w) ↔
      (∀ i, i < k → c i ≤ w) ∧ (∀ i, k < i → w ≤ c i) := by
  classical
  constructor
  · intro h
    constructor
    · intro i hi
      have h' := h hi.le
      simpa [Function.update, ne_of_lt hi] using h'
    · intro i hi
      have h' := h hi.le
      simpa [Function.update, ne_of_gt hi] using h'
  · rintro ⟨hl, hr⟩ i j hij
    by_cases hi : i = k
    · subst i
      by_cases hj : j = k
      · subst j; rfl
      · have hj' : k < j := lt_of_le_of_ne hij (Ne.symm hj)
        simpa [Function.update, hj] using hr j hj'
    · by_cases hj : j = k
      · subst j
        have hi' : i < k := lt_of_le_of_ne hij hi
        simpa [Function.update, hi] using hl i hi'
      · simpa [Function.update, hi, hj] using hc hij

/-- For a chain indexed by integers, the two adjacent comparisons are sufficient
for replacing an interior vertex. -/


@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem monotone_update_nat_iff {P : Type*} [Preorder P] (c : ℕ → P)
    (hc : Monotone c) (k : ℕ) (hk : 0 < k) (w : P) :
    Monotone (Function.update c k w) ↔ c (k-1) ≤ w ∧ w ≤ c (k+1) := by
  rw [monotone_update_iff c hc k w]
  constructor
  · rintro ⟨hl, hr⟩
    exact ⟨hl (k-1) (by omega), hr (k+1) (by omega)⟩
  · rintro ⟨hl, hr⟩
    constructor
    · intro i hi
      exact le_trans (hc (by omega : i ≤ k-1)) hl
    · intro i hi
      exact le_trans hr (hc (by omega : k+1 ≤ i))

/-- A vertex lying one rank above the bottom of a Boolean square and below
its top is exactly one of the two middle vertices. -/


@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boolean_square_middle {α : Type*} [DecidableEq α] (a b : α) (hab : a ≠ b)
    (s : Finset α) (hsub : s ⊆ {a,b}) (hcard : s.card = 1) :
    s = {a} ∨ s = {b} := by
  obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hcard
  have hx : x ∈ ({a,b} : Finset α) := hsub (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;> simp

/-- On a bounded coordinate chamber, every potential middle vertex of a
Boolean square is one of the two coordinate updates. -/


@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem chamber_square_middle {J : Type*} [LinearOrder J] (y : J → ℕ)
    (a b : J) (hab : a ≠ b) (s : Finset J) (hsub : s ⊆ {a,b})
    (hcard : s.card = 1) :
    (fun i => y i + if i ∈ s then 1 else 0) =
        (fun i => y i + if i = a then 1 else 0) ∨
    (fun i => y i + if i ∈ s then 1 else 0) =
        (fun i => y i + if i = b then 1 else 0) := by
  classical
  rcases boolean_square_middle a b hab s hsub hcard with h | h <;> simp [h]

/-- A codimension-one gap in a maximal chain of subsets has exactly two
possible intermediate subsets. -/


@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem update_chain_injective {I P : Type*} [DecidableEq I] (c : I → P) (k : I) :
    Function.Injective (fun w => Function.update c k w) := by
  intro a b h
  have h' := congrFun h k
  simpa using h'

open scoped Classical
/-- The two completions of an interior Boolean chain gap are distinct monotone
chains. This connects local Boolean intervals to actual chain completions. -/


@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boolean_chain_gap_completions {α : Type*} [DecidableEq α]
    (c : ℕ → Finset α) (hc : Monotone c) (k : ℕ) (hk : 0 < k)
    (a b : α) (hab : a ≠ b) (ha : a ∉ c (k-1)) (hb : b ∉ c (k-1))
    (htop : c (k+1) = insert a (insert b (c (k-1)))) :
    let candidates := (c (k+1)).powerset.filter
      (fun w => c (k-1) ⊆ w ∧ w.card = (c (k-1)).card + 1)
    (candidates.image (fun w => Function.update c k w)).card = 2 ∧
    ∀ d ∈ candidates.image (fun w => Function.update c k w), Monotone d := by
  classical
  dsimp only
  constructor
  · rw [Finset.card_image_iff.mpr (fun _ _ _ _ h => update_chain_injective c k h), htop]
    exact boolean_interval_intermediates_card _ a b hab ha hb
  · intro d hd
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hd
    have hw' := Finset.mem_filter.mp hw
    have hwv := Finset.mem_powerset.mp hw'.1
    exact (monotone_update_nat_iff c hc k hk w).2 ⟨hw'.2.1, hwv⟩

/-- An interior completion is exactly a monotone chain agreeing outside the
missing rank and having the prescribed cardinality at that rank. -/


@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boolean_chain_completion_iff {α : Type*} [DecidableEq α]
    (c : ℕ → Finset α) (hc : Monotone c) (k : ℕ) (hk : 0 < k)
    (d : ℕ → Finset α) :
    d ∈ ((c (k+1)).powerset.filter
      (fun w => c (k-1) ⊆ w ∧ w.card = (c (k-1)).card + 1)).image
        (fun w => Function.update c k w) ↔
    Monotone d ∧ (∀ i, i ≠ k → d i = c i) ∧
      (d k).card = (c (k-1)).card + 1 := by
  classical
  constructor
  · intro hd
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hd
    have hw' := Finset.mem_filter.mp hw
    have hwv := Finset.mem_powerset.mp hw'.1
    refine ⟨(monotone_update_nat_iff c hc k hk w).2 ⟨hw'.2.1, hwv⟩, ?_, ?_⟩
    · intro i hi; simp [hi]
    · simpa using hw'.2.2
  · rintro ⟨hd, heq, hcard⟩
    have hl : c (k-1) ⊆ d k := by
      rw [← heq (k-1) (by omega)]
      exact hd (by omega)
    have hr : d k ⊆ c (k+1) := by
      rw [← heq (k+1) (by omega)]
      exact hd (by omega)
    refine Finset.mem_image.mpr ⟨d k, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hr, hl, hcard⟩, ?_⟩
    ext i
    by_cases hi : i = k
    · subst i; simp
    · simp [hi, heq i hi]

/-- If a facet contains both opposite vertices of a unit cube, every unit cube
containing that facet has the same base. This applies to interior-rank deletion
of a Freudenthal chain. -/


@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem unit_cube_base_unique {J : Type*} [DecidableEq (J → ℕ)]
    (F : Finset (J → ℕ)) (y z : J → ℕ)
    (hy : y ∈ F) (hy1 : (fun i => y i + 1) ∈ F)
    (hz : ∀ x ∈ F, ∀ i, z i ≤ x i ∧ x i ≤ z i + 1) : z = y := by
  funext i
  have h₀ := hz y hy i
  have h₁ := hz (fun i => y i + 1) hy1 i
  omega

/-- When an endpoint facet contains the upper corner and the vertex one step
above the lower corner, the only possible lower corners of a containing cube
are the original lower corner and the corner shifted across that facet. -/


@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem unit_cube_boolean_encoding {J : Type*} [Fintype J] [DecidableEq J]
    (y x : J → ℕ) (h : ∀ i, y i ≤ x i ∧ x i ≤ y i + 1) :
    ∃! s : Finset J, x = fun i => y i + if i ∈ s then 1 else 0 := by
  classical
  let s : Finset J := Finset.univ.filter (fun i => y i < x i)
  have hs : ∀ i, i ∈ s ↔ y i < x i := by simp [s]
  refine ⟨s, ?_, ?_⟩
  · funext i
    have hi := h i
    by_cases hix : y i < x i
    · simp [hs, hix]; omega
    · simp [hs, hix]; omega
  · intro t ht
    ext i
    rw [hs]
    have hi := congrFun ht i
    by_cases hit : i ∈ t <;> simp [hit] at hi ⊢ <;> omega

/-- Boolean inclusion agrees with pointwise order on integer cube vertices. -/


@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem cube_boolean_order {J : Type*} [DecidableEq J] (y : J → ℕ)
    (s t : Finset J) :
    (∀ i, y i + (if i ∈ s then 1 else 0) ≤ y i + (if i ∈ t then 1 else 0)) ↔ s ⊆ t := by
  constructor
  · intro h i hi
    have hh := h i
    by_contra hn
    simp [hi, hn] at hh
  · intro h i
    by_cases hs : i ∈ s
    · have ht := h hs
      simp [hs, ht]
    · simp [hs]

/-- The coordinate-increment embedding reflects the Boolean order as well as
preserving it. Thus any lattice facet in a fixed cube recovers its underlying
Boolean chain without ambiguity. -/


@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem coordinate_increments_le_iff {J : Type*} [DecidableEq J]
    (y : J → ℕ) (s t : Finset J) :
    (∀ i, y i + (if i ∈ s then 1 else 0) ≤ y i + (if i ∈ t then 1 else 0)) ↔ s ⊆ t := by
  constructor
  · intro h i hi
    have hh := h i
    by_contra ht
    simp [hi, ht] at hh
  · intro h i
    by_cases hs : i ∈ s
    · have ht := h hs
      simp [hs, ht]
    · simp [hs]

/-- A rank-r insertion into a chain containing ranks r-1 and r+1 must lie
between those two vertices. -/


@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem deleted_graded_chain_ranks {J : Type*} [DecidableEq J] {n : ℕ}
    (c : Fin (n+1) → Finset J) (hc : ∀ i, (c i).card = i.val)
    (k : Fin (n+1)) :
    (∀ s ∈ ((Finset.univ.erase k).image c), s.card ≠ k.val) ∧
    (∀ i : Fin (n+1), i ≠ k → ∃ s ∈ ((Finset.univ.erase k).image c), s.card = i.val) := by
  classical
  constructor
  · intro s hs hcard
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hs
    have hik : i ≠ k := (Finset.mem_erase.mp hi).1
    apply hik
    apply Fin.ext
    rw [← hc i, hcard]
  · intro i hi
    refine ⟨c i, Finset.mem_image.mpr ⟨i, ?_, rfl⟩, hc i⟩
    simp [hi]

/-- Two graded maximal chains having the same deleted facet must omit the
same rank. This gives the missing-rank uniqueness needed for interior facets
once their containing cube is identified. -/


@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem deleted_graded_chain_rank_unique {J : Type*} [DecidableEq J] {n : ℕ}
    (c d : Fin (n+1) → Finset J)
    (hc : ∀ i, (c i).card = i.val) (hd : ∀ i, (d i).card = i.val)
    (k l : Fin (n+1))
    (h : (Finset.univ.erase k).image c = (Finset.univ.erase l).image d) : k = l := by
  by_contra hkl
  obtain ⟨s, hs, hrank⟩ := (deleted_graded_chain_ranks d hd l).2 k hkl
  rw [← h] at hs
  exact (deleted_graded_chain_ranks c hc k).1 s hs hrank

/-- Equal facets of graded Boolean chains agree at each retained rank. -/


@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem deleted_graded_chain_agree {J : Type*} [DecidableEq J] {n : ℕ}
    (c d : Fin (n+1) → Finset J)
    (hc : ∀ i, (c i).card = i.val) (hd : ∀ i, (d i).card = i.val)
    (k : Fin (n+1))
    (h : (Finset.univ.erase k).image c = (Finset.univ.erase k).image d) :
    ∀ i, i ≠ k → c i = d i := by
  intro i hik
  have hi : c i ∈ (Finset.univ.erase k).image c := by
    apply Finset.mem_image.mpr
    exact ⟨i, by simp [hik], rfl⟩
  rw [h] at hi
  obtain ⟨j, _, hji⟩ := Finset.mem_image.mp hi
  have heq : i = j := by
    apply Fin.ext
    have hh := congrArg Finset.card hji
    rw [hd j, hc i] at hh
    exact hh.symm
  subst j
  exact hji.symm

/-- An interior lattice facet determines both its cube base and the deleted
rank, and fixes the two representing graded chains at every other rank. -/


@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem interior_lattice_facet_unique {J : Type*} [Fintype J] [DecidableEq J] {n : ℕ}
    (y z : J → ℕ) (c d : Fin (n+1) → Finset J)
    (hc : ∀ i, (c i).card = i.val) (hd : ∀ i, (d i).card = i.val)
    (k l : Fin (n+1))
    (F : Finset (J → ℕ))
    (hF : F = ((Finset.univ.erase k).image c).image
      (fun s i => y i + if i ∈ s then 1 else 0))
    (hG : F = ((Finset.univ.erase l).image d).image
      (fun s i => z i + if i ∈ s then 1 else 0))
    (hy : y ∈ F) (htop : (fun i => y i + 1) ∈ F)
    (hbound : ∀ v ∈ F, ∀ i, z i ≤ v i ∧ v i ≤ z i + 1) :
    y = z ∧ k = l ∧ ∀ i, i ≠ k → c i = d i := by
  classical
  have hyz : y = z := (unit_cube_base_unique F y z hy htop hbound).symm
  subst z
  have hinj : Function.Injective (fun s : Finset J => fun i => y i + if i ∈ s then 1 else 0) := by
    intro s t h
    ext i
    have hi := congrFun h i
    by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all
  have hchain : (Finset.univ.erase k).image c = (Finset.univ.erase l).image d := by
    apply (Finset.image_inj hinj).mp
    rw [← hF, ← hG]
  have hkl := deleted_graded_chain_rank_unique c d hc hd k l hchain
  subst l
  exact ⟨rfl, rfl, deleted_graded_chain_agree c d hc hd k hchain⟩

/-- Every encoded Boolean chain lies inside its base unit cube. -/


@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem lattice_chain_in_unit_cube {J : Type*} [Fintype J] [DecidableEq J] {n : ℕ}
    (z : J → ℕ) (d : Fin (n+1) → Finset J) (l : Fin (n+1)) :
    ∀ v ∈ ((Finset.univ.erase l).image d).image
      (fun s i => z i + if i ∈ s then 1 else 0),
      ∀ i, z i ≤ v i ∧ v i ≤ z i + 1 := by
  classical
  intro v hv i
  obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hv
  by_cases h : i ∈ s <;> simp [h]

/-- Retaining the empty and universal Boolean vertices retains both opposite
lattice corners. -/


@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem lattice_chain_retains_corners {J : Type*} [Fintype J] [DecidableEq J] {n : ℕ}
    (y : J → ℕ) (c : Fin (n+1) → Finset J) (k a b : Fin (n+1))
    (ha : a ≠ k) (hb : b ≠ k) (hca : c a = ∅) (hcb : c b = Finset.univ) :
    let F := ((Finset.univ.erase k).image c).image
      (fun s i => y i + if i ∈ s then 1 else 0)
    y ∈ F ∧ (fun i => y i + 1) ∈ F := by
  classical
  dsimp
  constructor
  · apply Finset.mem_image.mpr
    refine ⟨c a, Finset.mem_image.mpr ⟨a, by simp [ha], rfl⟩, ?_⟩
    simp [hca]
  · apply Finset.mem_image.mpr
    refine ⟨c b, Finset.mem_image.mpr ⟨b, by simp [hb], rfl⟩, ?_⟩
    simp [hcb]

/-- Global uniqueness for an interior facet, with the cube-bound and retained
corner conditions discharged directly from its two chain representations. -/


@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem interior_lattice_facet_unique_of_corners {J : Type*} [Fintype J] [DecidableEq J] {n : ℕ}
    (y z : J → ℕ) (c d : Fin (n+1) → Finset J)
    (hc : ∀ i, (c i).card = i.val) (hd : ∀ i, (d i).card = i.val)
    (k l a b : Fin (n+1)) (ha : a ≠ k) (hb : b ≠ k)
    (hca : c a = ∅) (hcb : c b = Finset.univ)
    (h : ((Finset.univ.erase k).image c).image (fun s i => y i + if i ∈ s then 1 else 0) =
      ((Finset.univ.erase l).image d).image (fun s i => z i + if i ∈ s then 1 else 0)) :
    y = z ∧ k = l ∧ ∀ i, i ≠ k → c i = d i := by
  classical
  let F := ((Finset.univ.erase k).image c).image (fun s i => y i + if i ∈ s then 1 else 0)
  have hcorners := lattice_chain_retains_corners y c k a b ha hb hca hcb
  have hbound : ∀ v ∈ F, ∀ i, z i ≤ v i ∧ v i ≤ z i + 1 := by
    intro v hv
    have hv' : v ∈ ((Finset.univ.erase l).image d).image
        (fun s i => z i + if i ∈ s then 1 else 0) := h ▸ hv
    exact lattice_chain_in_unit_cube z d l v hv'
  exact interior_lattice_facet_unique y z c d hc hd k l F rfl h hcorners.1 hcorners.2 hbound

/-- A saturated Boolean chain of n+1 elements contains exactly one set of
  each rank from 0 through n. -/


@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boolean_facet_interior_count {J : Type*} [Fintype J] [DecidableEq J]
    (F : Finset (Finset J)) (u : Finset J) (a b : J) (r : ℕ)
    (hab : a ≠ b) (ha : a ∉ u) (hb : b ∉ u)
    (hu : u ∈ F) (hv : insert a (insert b u) ∈ F)
    (huc : u.card + 1 = r) (hr : r ≤ Fintype.card J)
    (hmissing : ∀ x ∈ F, x.card ≠ r)
    (hFcard : F.card = Fintype.card J)
    (hFchain : ∀ x ∈ F, ∀ y ∈ F, x ⊆ y ∨ y ⊆ x)
    (hgap : ∀ x ∈ F, x ⊆ u ∨ insert a (insert b u) ⊆ x) :
    (Finset.univ.filter (fun w : Finset J => w ∉ F ∧
      (insert w F).card = Fintype.card J + 1 ∧
      ∀ x ∈ insert w F, ∀ y ∈ insert w F, x ⊆ y ∨ y ⊆ x)).card = 2 := by
  classical
  have hvc : (insert a (insert b u)).card = r + 1 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, ha]), Finset.card_insert_of_notMem hb]
    omega
  have heq : (Finset.univ.filter (fun w : Finset J => w ∉ F ∧
      (insert w F).card = Fintype.card J + 1 ∧
      ∀ x ∈ insert w F, ∀ y ∈ insert w F, x ⊆ y ∨ y ⊆ x)) =
      (insert a (insert b u)).powerset.filter
        (fun w => u ⊆ w ∧ w.card = u.card + 1) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset]
    constructor
    · rintro ⟨_, hc, hch⟩
      have hwc := boolean_missing_rank_forced F w r hr hmissing hch hc
      have h := boolean_chain_gap_forced F u (insert a (insert b u)) w r hu hv huc hvc hwc hch
      exact ⟨h.2, h.1, by omega⟩
    · rintro ⟨hwv, huw, hwc⟩
      have hnot : w ∉ F := boolean_gap_fill_not_mem F w r hmissing (by omega)
      exact ⟨hnot, by simp [hnot, hFcard], boolean_gap_fill_chain F u _ w hFchain hgap huw hwv⟩
  rw [heq]
  exact boolean_interval_intermediates_card u a b hab ha hb

/-- Imposing a vertex constraint on the two completions leaves exactly the
 admissible elements of the two-element cubical diamond. -/


@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem chamber_failed_middle_lt {J : Type*} [LinearOrder J] (y : J → ℕ) (a b : J)
    (hab : a ≠ b) (hbot : Monotone y)
    (htop : Monotone (fun i => y i + if i = a ∨ i = b then 1 else 0))
    (hfail : ¬ Monotone (fun i => y i + if i = a then 1 else 0)) : a < b := by
  classical
  simp only [Monotone] at hfail
  push_neg at hfail
  obtain ⟨i, j, hij, hf⟩ := hfail
  have hb := hbot hij
  have ht := htop hij
  by_cases hia : i = a <;> by_cases hja : j = a
  all_goals simp only [hia, hja, ↓reduceIte] at hf
  all_goals simp_all only [add_zero]
  all_goals try omega
  subst i
  have hjb : j = b := by
    by_contra hjb
    simp [hja, hjb] at ht
    omega
  subst j
  exact lt_of_le_of_ne hij hab

/-- A failed middle is a genuine chamber-boundary phenomenon: the flipped
coordinates are consecutive in the order and have equal bottom values. -/


@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem chamber_failed_middle_boundary {J : Type*} [LinearOrder J] (y : J → ℕ) (a b : J)
    (hab : a ≠ b) (hbot : Monotone y)
    (htop : Monotone (fun i => y i + if i = a ∨ i = b then 1 else 0))
    (hfail : ¬ Monotone (fun i => y i + if i = a then 1 else 0)) :
    a < b ∧ y a = y b ∧ ∀ c, a < c → c < b → False := by
  classical
  have hablt := chamber_failed_middle_lt y a b hab hbot htop hfail
  have heq : y a = y b := by
    have hh := hfail
    simp only [Monotone] at hh
    push_neg at hh
    obtain ⟨i, j, hij, hf⟩ := hh
    have hb := hbot hij
    have ht := htop hij
    by_cases hia : i = a <;> by_cases hja : j = a
    all_goals simp only [hia, hja, ↓reduceIte] at hf
    all_goals simp_all only [add_zero]
    all_goals try omega
    subst i
    have hjb : j = b := by
      by_contra hjb
      simp [hjb] at ht
      omega
    subst j
    omega
  refine ⟨hablt, heq, ?_⟩
  intro c hac hcb
  have ht := htop hac.le
  have hb := hbot hcb.le
  have hca : c ≠ a := ne_of_gt hac
  have hcb' : c ≠ b := ne_of_lt hcb
  simp [hab, hca, hcb'] at ht
  omega

/-- If the bottom and top of a cubical diamond belong to the monotone chamber,
then at least one of its middle vertices belongs to the chamber. -/


@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem chamber_diamond {J : Type*} [LinearOrder J] (y : J → ℕ) (a b : J)
    (hab : a ≠ b) (hbot : Monotone y)
    (htop : Monotone (fun i => y i + if i = a ∨ i = b then 1 else 0)) :
    Monotone (fun i => y i + if i = a then 1 else 0) ∨
    Monotone (fun i => y i + if i = b then 1 else 0) := by
  classical
  by_contra h
  push_neg at h
  have h₁ := chamber_failed_middle_lt y a b hab hbot htop h.1
  have htop' : Monotone (fun i => y i + if i = b ∨ i = a then 1 else 0) := by
    simpa only [or_comm] using htop
  have h₂ := chamber_failed_middle_lt y b a hab.symm hbot htop' h.2
  exact (lt_asymm h₁ h₂)

/-- A middle vertex exits the chamber exactly when its raised coordinate
precedes the other, both coordinates coincide at the bottom, and the two
coordinates are consecutive. -/


@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem chamber_failed_middle_iff {J : Type*} [LinearOrder J] (y : J → ℕ) (a b : J)
    (hab : a ≠ b) (hbot : Monotone y)
    (htop : Monotone (fun i => y i + if i = a ∨ i = b then 1 else 0)) :
    (¬ Monotone (fun i => y i + if i = a then 1 else 0)) ↔
    (a < b ∧ y a = y b ∧ ∀ c, a < c → c < b → False) := by
  constructor
  · exact chamber_failed_middle_boundary y a b hab hbot htop
  · rintro ⟨hlt, heq, _⟩ hm
    have h := hm hlt.le
    simp [hab.symm, heq] at h

/-- Exactly one of the two diamond middles exits the chamber on an equality
wall; otherwise both middles remain. This is the local incidence count at an
internal facet (subject to the global uniqueness of the two completions). -/


@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem chamber_diamond_middle_count {J : Type*} [LinearOrder J]
    (y : J → ℕ) (a b : J) (hab : a ≠ b) (hbot : Monotone y)
    (htop : Monotone (fun i => y i + if i = a ∨ i = b then 1 else 0)) :
    (by classical exact (Finset.univ.filter (fun z : Bool =>
      Monotone (fun i => y i + if i = (if z then b else a) then 1 else 0))).card) =
      if y a = y b then 1 else 2 := by
  classical
  have htop' : Monotone (fun i => y i + if i = b ∨ i = a then 1 else 0) := by
    simpa only [or_comm] using htop
  have ha := chamber_failed_middle_iff y a b hab hbot htop
  have hb := chamber_failed_middle_iff y b a hab.symm hbot htop'
  have hdiamond := chamber_diamond y a b hab hbot htop
  by_cases heq : y a = y b
  · have hnotboth : ¬ (Monotone (fun i => y i + if i = a then 1 else 0) ∧
      Monotone (fun i => y i + if i = b then 1 else 0)) := by
      rintro ⟨hma, hmb⟩
      rcases lt_or_gt_of_ne hab with hlt | hlt
      · have h := hma hlt.le
        simp [hab.symm, heq] at h
      · have h := hmb hlt.le
        simp [hab, heq] at h
    simp only [heq, ↓reduceIte]
    rcases hdiamond with hma | hmb
    · have hnmb : ¬ Monotone (fun i => y i + if i = b then 1 else 0) := fun h => hnotboth ⟨hma, h⟩
      simp [Finset.filter_insert, Finset.filter_singleton, hma, hnmb]
    · have hnma : ¬ Monotone (fun i => y i + if i = a then 1 else 0) := fun h => hnotboth ⟨h, hmb⟩
      simp [Finset.filter_insert, Finset.filter_singleton, hnma, hmb]
  · have hma : Monotone (fun i => y i + if i = a then 1 else 0) := by
      by_contra h; exact heq ((ha.mp h).2.1)
    have hmb : Monotone (fun i => y i + if i = b then 1 else 0) := by
      by_contra h; exact heq ((hb.mp h).2.1.symm)
    simp [Finset.filter_insert, Finset.filter_singleton, heq, hma, hmb]

/-- Local chamber-compatible completions are counted by the two diamond middles. -/


@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem chamber_boolean_interior_count {J : Type*} [Fintype J] [LinearOrder J]
    (F : Finset (Finset J)) (u : Finset J) (a b : J) (r : ℕ) (y : J → ℕ)
    (hab : a ≠ b) (ha : a ∉ u) (hb : b ∉ u)
    (hu : u ∈ F) (hv : insert a (insert b u) ∈ F)
    (huc : u.card + 1 = r) (hr : r ≤ Fintype.card J)
    (hmissing : ∀ x ∈ F, x.card ≠ r)
    (hFcard : F.card = Fintype.card J)
    (hFchain : ∀ x ∈ F, ∀ z ∈ F, x ⊆ z ∨ z ⊆ x)
    (hgap : ∀ x ∈ F, x ⊆ u ∨ insert a (insert b u) ⊆ x)
    (hbot : Monotone (fun i => y i + if i ∈ u then 1 else 0))
    (htop : Monotone (fun i => y i + if i ∈ insert a (insert b u) then 1 else 0)) :
    (by classical exact (Finset.univ.filter (fun w : Finset J => w ∉ F ∧
      (insert w F).card = Fintype.card J + 1 ∧
      (∀ x ∈ insert w F, ∀ z ∈ insert w F, x ⊆ z ∨ z ⊆ x) ∧
      Monotone (fun i => y i + if i ∈ w then 1 else 0))).card) =
    if y a = y b then 1 else 2 := by
  classical
  let v : J → ℕ := fun i => y i + if i ∈ u then 1 else 0
  have ht : Monotone (fun i => v i + if i = a ∨ i = b then 1 else 0) := by
    convert htop using 1
    congr 1; funext i
    dsimp [v]
    simp only [Finset.mem_insert]
    by_cases hia : i = a <;> by_cases hib : i = b <;> by_cases hiu : i ∈ u <;>
      simp_all
  have hc := chamber_diamond_middle_count v a b hab hbot ht
  rw [boolean_facet_interior_constrained F u a b r hab ha hb hu hv huc hr hmissing hFcard hFchain hgap]
  have hma : (fun i => y i + if i ∈ insert a u then 1 else 0) =
      (fun i => v i + if i = a then 1 else 0) := by
    funext i
    dsimp [v]; simp only [Finset.mem_insert]
    by_cases hia : i = a <;> by_cases hiu : i ∈ u <;> simp_all
  have hmb : (fun i => y i + if i ∈ insert b u then 1 else 0) =
      (fun i => v i + if i = b then 1 else 0) := by
    funext i
    dsimp [v]; simp only [Finset.mem_insert]
    by_cases hib : i = b <;> by_cases hiu : i ∈ u <;> simp_all
  have hne : insert a u ≠ insert b u := by
    intro h
    have hm : a ∈ insert b u := h ▸ Finset.mem_insert_self a u
    simp [hab, ha] at hm
  simp only [Finset.filter_insert, Finset.filter_singleton, hma, hmb]
  have hvab : v a = y a ∧ v b = y b := by simp [v, ha, hb]
  rw [hvab.1, hvab.2] at hc
  have huniv : (Finset.univ : Finset Bool) = {true, false} := by decide
  rw [huniv] at hc
  simp only [Finset.filter_insert, Finset.filter_singleton, ↓reduceIte] at hc
  split_ifs at hc ⊢ <;> simp_all [hne]

/-- The count of admissible saturated chains containing a facet equals its
number of admissible one-vertex completions. -/


@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boolean_admissible_incident_card {J : Type*} [Fintype J] [DecidableEq J]
    (F : Finset (Finset J)) (P : Finset J → Prop) [DecidablePred P]
    (hFcard : F.card = Fintype.card J) (hFP : ∀ x ∈ F, P x) :
    (Finset.univ.filter (fun S : Finset (Finset J) => F ⊆ S ∧
      S.card = Fintype.card J + 1 ∧
      (∀ a ∈ S, ∀ b ∈ S, a ⊆ b ∨ b ⊆ a) ∧ ∀ s ∈ S, P s)).card =
    (Finset.univ.filter (fun w : Finset J => w ∉ F ∧
      (insert w F).card = Fintype.card J + 1 ∧
      (∀ a ∈ insert w F, ∀ b ∈ insert w F, a ⊆ b ∨ b ⊆ a) ∧ P w)).card := by
  classical
  let K : Finset (Finset (Finset J)) := Finset.univ.filter (fun S =>
    S.card = Fintype.card J + 1 ∧
    (∀ a ∈ S, ∀ b ∈ S, a ⊆ b ∨ b ⊆ a) ∧ ∀ s ∈ S, P s)
  have h := facet_incident_card K F
  have hl : K.filter (fun T => F ⊆ T ∧ T.card = F.card + 1) =
      Finset.univ.filter (fun S : Finset (Finset J) => F ⊆ S ∧
        S.card = Fintype.card J + 1 ∧
        (∀ a ∈ S, ∀ b ∈ S, a ⊆ b ∨ b ⊆ a) ∧ ∀ s ∈ S, P s) := by
    ext S
    simp only [K, Finset.mem_filter, Finset.mem_univ, true_and, hFcard]
    tauto
  rw [hl] at h
  convert h using 1
  congr 1
  ext w
  simp only [K, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · rintro ⟨hn, hc, hch, hp⟩
    exact ⟨hn, hc, hch, fun s hs => hs.elim (fun e => e ▸ hp) (fun hsF => hFP s hsF)⟩
  · rintro ⟨hn, hc, hch, hp⟩
    exact ⟨hn, hc, hch, hp w (Or.inl rfl)⟩

/-- Exact number of chamber-compatible saturated Boolean chains extending an
interior facet. -/


@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem chamber_boolean_interior_chain_count {J : Type*} [Fintype J] [LinearOrder J]
    (F : Finset (Finset J)) (u : Finset J) (a b : J) (r : ℕ) (y : J → ℕ)
    (hab : a ≠ b) (ha : a ∉ u) (hb : b ∉ u)
    (hu : u ∈ F) (hv : insert a (insert b u) ∈ F)
    (huc : u.card + 1 = r) (hr : r ≤ Fintype.card J)
    (hmissing : ∀ x ∈ F, x.card ≠ r)
    (hFcard : F.card = Fintype.card J)
    (hFchain : ∀ x ∈ F, ∀ z ∈ F, x ⊆ z ∨ z ⊆ x)
    (hgap : ∀ x ∈ F, x ⊆ u ∨ insert a (insert b u) ⊆ x)
    (hFP : ∀ s ∈ F, Monotone (fun i => y i + if i ∈ s then 1 else 0)) :
    (by classical exact (Finset.univ.filter (fun S : Finset (Finset J) => F ⊆ S ∧
      S.card = Fintype.card J + 1 ∧
      (∀ x ∈ S, ∀ z ∈ S, x ⊆ z ∨ z ⊆ x) ∧
      ∀ s ∈ S, Monotone (fun i => y i + if i ∈ s then 1 else 0))).card) =
    if y a = y b then 1 else 2 := by
  classical
  rw [boolean_admissible_incident_card F
    (fun s => Monotone (fun i => y i + if i ∈ s then 1 else 0)) hFcard hFP]
  exact chamber_boolean_interior_count F u a b r y hab ha hb hu hv huc hr hmissing
    hFcard hFchain hgap (hFP u hu) (hFP _ hv)
/-- Every saturated finite Boolean chain has a monotone enumeration by rank. -/


@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem boundedChainSimplices_chamber_interior_count {J : Type*} [Fintype J] [LinearOrder J]
    (N : ℕ) (y : J → ℕ) (hy : ∀ i, y i + 1 ≤ N)
    (F : Finset (Finset J)) (u : Finset J) (a b : J) (r : ℕ)
    (hbot : ∅ ∈ F) (htop : Finset.univ ∈ F)
    (hab : a ≠ b) (ha : a ∉ u) (hb : b ∉ u)
    (hu : u ∈ F) (hv : insert a (insert b u) ∈ F)
    (huc : u.card + 1 = r) (hr : r ≤ Fintype.card J)
    (hmissing : ∀ x ∈ F, x.card ≠ r)
    (hFcard : F.card = Fintype.card J)
    (hFchain : ∀ x ∈ F, ∀ z ∈ F, x ⊆ z ∨ z ⊆ x)
    (hgap : ∀ x ∈ F, x ⊆ u ∨ insert a (insert b u) ⊆ x)
    (hFP : ∀ s ∈ F, Monotone (fun i => y i + if i ∈ s then 1 else 0)) :
    let enc : Finset J → J → Fin (N+1) := fun s i => ⟨y i + if i ∈ s then 1 else 0, by
      have := hy i; split_ifs <;> omega⟩
    (by classical exact ((boundedChainSimplices N (Fintype.card J) Monotone).filter
      (fun T => F.image enc ⊆ T)).card) = if y a = y b then 1 else 2 := by
  classical
  dsimp only
  let enc : Finset J → J → Fin (N+1) := fun s i => ⟨y i + if i ∈ s then 1 else 0, by
    have := hy i; split_ifs <;> omega⟩
  have hch : ∀ s ∈ F, Monotone (enc s) := by
    intro s hs i j hij
    exact hFP s hs hij
  rw [boundedChainSimplices_interior_incident_card N Monotone y hy F hbot htop hFcard hch]
  exact chamber_boolean_interior_count F u a b r y hab ha hb hu hv huc hr hmissing
    hFcard hFchain hgap (hFP u hu) (hFP _ hv)
open Finset

/-- Deleting rank zero from a saturated Boolean chain leaves a chain containing
its singleton and full endpoints, with the singleton in every remaining vertex. -/


@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem concrete_interior_facet_count {J : Type*} [Fintype J] [LinearOrder J]
    (N : ℕ) (T G : Finset (J → Fin (N+1)))
    (hT : T ∈ boundedChainSimplices N (Fintype.card J) Monotone)
    (hGT : G ⊆ T) (hG : G.card = Fintype.card J)
    (hinterior : ∃ (y : J → ℕ) (c : Fin (Fintype.card J + 1) → Finset J)
      (v : Fin (Fintype.card J + 1) → J → Fin (N+1)) (k : Fin (Fintype.card J + 1)), Monotone c ∧ (∀ j, (c j).card = j.val) ∧
      (∀ j i, (v j i).val = y i + if i ∈ c j then 1 else 0) ∧
      (∀ j, Monotone (v j)) ∧ G = (Finset.univ.erase k).image v ∧
      0 < k.val ∧ k.val < Fintype.card J) :
    ∃ a b : J, ∃ y : J → ℕ,
      ((boundedChainSimplices N (Fintype.card J) Monotone).filter (fun T => G ⊆ T)).card =
        if y a = y b then 1 else 2 := by
  classical
  obtain ⟨y,c,v,k,hc,hr,hv,hch,hGv,hk0,hkn⟩ := hinterior
  let top : Fin (Fintype.card J + 1) := ⟨Fintype.card J, by omega⟩
  have htop : c top = Finset.univ := by
    apply Finset.eq_univ_of_card
    simpa [top] using hr top
  have hy : ∀ i, y i + 1 ≤ N := by
    intro i
    have h := (v top i).isLt
    rw [hv, htop] at h
    simp only [Finset.mem_univ, ↓reduceIte] at h
    omega
  let enc : Finset J → J → Fin (N+1) := fun s i => ⟨y i + if i ∈ s then 1 else 0, by
      have := hy i; split_ifs <;> omega⟩
  have he : ∀ j, v j = enc (c j) := by
    intro j; funext i; apply Fin.ext; exact hv j i
  let F := (Finset.univ.erase k).image c
  have hGF : G = F.image enc := by
    rw [hGv]; dsimp [F]; rw [Finset.image_image]
    congr 1
    funext j
    exact he j
  have hFP : ∀ s ∈ F, Monotone (fun i => y i + if i ∈ s then 1 else 0) := by
    intro s hs
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hs
    intro i l hil
    have h := hch j hil
    change (v j i).val ≤ (v j l).val at h
    simpa only [hv] using h
  have hk : k = (⟨k.val, by omega⟩ : Fin (Fintype.card J + 1)) := rfl
  have hgap := deleted_interior_boolean_chain (Fintype.card J) k.val rfl hk0 hkn c hc hr
  rw [← hk] at hgap
  change ∃ u a b, _ at hgap
  obtain ⟨u,a,b,hab,ha,hb,hu,hv',huc,hr',hmissing,hcard,hchain,hgap,hbot,htop'⟩ := hgap
  refine ⟨a,b,y,?_⟩
  rw [hGF]
  exact boundedChainSimplices_chamber_interior_count N y hy F u a b k.val hbot htop'
    hab ha hb hu hv' huc hr' hmissing hcard hchain hgap hFP

/-- An incidence-one interior gap lies on an equality wall of the ordered chamber. -/


@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem interior_incidence_one_wall {J : Type*} [Fintype J] [LinearOrder J]
    (N : ℕ) (y : J → ℕ) (hy : ∀ i, y i + 1 ≤ N)
    (F : Finset (Finset J)) (u : Finset J) (a b : J) (r : ℕ)
    (hbot : ∅ ∈ F) (htop : Finset.univ ∈ F)
    (hab : a ≠ b) (ha : a ∉ u) (hb : b ∉ u)
    (hu : u ∈ F) (hv : insert a (insert b u) ∈ F)
    (huc : u.card + 1 = r) (hr : r ≤ Fintype.card J)
    (hmissing : ∀ x ∈ F, x.card ≠ r)
    (hFcard : F.card = Fintype.card J)
    (hFchain : ∀ x ∈ F, ∀ z ∈ F, x ⊆ z ∨ z ⊆ x)
    (hgap : ∀ x ∈ F, x ⊆ u ∨ insert a (insert b u) ⊆ x)
    (hFP : ∀ s ∈ F, Monotone (fun i => y i + if i ∈ s then 1 else 0)) :
    let enc : Finset J → J → Fin (N+1) := fun s i => ⟨y i + if i ∈ s then 1 else 0, by
      have := hy i; split_ifs <;> omega⟩
    (by classical exact ((boundedChainSimplices N (Fintype.card J) Monotone).filter
      (fun T => F.image enc ⊆ T)).card = 1) →
    ∀ v ∈ F.image enc, v a = v b := by
  classical
  dsimp only
  intro hcount v hv'
  have hc := boundedChainSimplices_chamber_interior_count N y hy F u a b r hbot htop hab ha hb hu hv huc hr hmissing hFcard hFchain hgap hFP
  have hyab : y a = y b := by
    dsimp only at hc
    rw [hcount] at hc
    split_ifs at hc with h
    · exact h
    · omega
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hv'
  apply Fin.ext
  dsimp only
  rcases hgap s hs with h | h
  · have hna : a ∉ s := fun h' => ha (h h')
    have hnb : b ∉ s := fun h' => hb (h h')
    simp [hna, hnb, hyab]
  · have hma : a ∈ s := h (by simp)
    have hmb : b ∈ s := h (by simp)
    simp [hma, hmb, hyab]

/-- Any actual interior facet with one incident simplex lies on an equality wall. -/


@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem concrete_interior_incidence_one_wall {J : Type*} [Fintype J] [LinearOrder J]
    (N : ℕ) (T G : Finset (J → Fin (N+1)))
    (hT : T ∈ boundedChainSimplices N (Fintype.card J) Monotone)
    (hGT : G ⊆ T) (hG : G.card = Fintype.card J)
    (hinterior : ∃ (y : J → ℕ) (c : Fin (Fintype.card J + 1) → Finset J)
      (v : Fin (Fintype.card J + 1) → J → Fin (N+1)) (k : Fin (Fintype.card J + 1)), Monotone c ∧ (∀ j, (c j).card = j.val) ∧
      (∀ j i, (v j i).val = y i + if i ∈ c j then 1 else 0) ∧
      (∀ j, Monotone (v j)) ∧ G = (Finset.univ.erase k).image v ∧
      0 < k.val ∧ k.val < Fintype.card J)
    (hcount : ((boundedChainSimplices N (Fintype.card J) Monotone).filter (fun T => G ⊆ T)).card = 1) :
    ∃ a b : J, a ≠ b ∧ ∀ v ∈ G, v a = v b := by
  classical
  obtain ⟨y,c,v,k,hc,hr,hv,hch,hGv,hk0,hkn⟩ := hinterior
  let top : Fin (Fintype.card J + 1) := ⟨Fintype.card J, by omega⟩
  have htop : c top = Finset.univ := by
    apply Finset.eq_univ_of_card
    simpa [top] using hr top
  have hy : ∀ i, y i + 1 ≤ N := by
    intro i
    have h := (v top i).isLt
    rw [hv, htop] at h
    simp only [Finset.mem_univ, ↓reduceIte] at h
    omega
  let enc : Finset J → J → Fin (N+1) := fun s i => ⟨y i + if i ∈ s then 1 else 0, by
      have := hy i; split_ifs <;> omega⟩
  have he : ∀ j, v j = enc (c j) := by
    intro j; funext i; apply Fin.ext; exact hv j i
  let F := (Finset.univ.erase k).image c
  have hGF : G = F.image enc := by
    rw [hGv]; dsimp [F]; rw [Finset.image_image]
    congr 1
    funext j
    exact he j
  have hFP : ∀ s ∈ F, Monotone (fun i => y i + if i ∈ s then 1 else 0) := by
    intro s hs
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hs
    intro i l hil
    have h := hch j hil
    change (v j i).val ≤ (v j l).val at h
    simpa only [hv] using h
  have hk : k = (⟨k.val, by omega⟩ : Fin (Fintype.card J + 1)) := rfl
  have hgap := deleted_interior_boolean_chain (Fintype.card J) k.val rfl hk0 hkn c hc hr
  rw [← hk] at hgap
  change ∃ u a b, _ at hgap
  obtain ⟨u,a,b,hab,ha,hb,hu,hv',huc,hr',hmissing,hcard,hchain,hgap,hbot,htop'⟩ := hgap
  refine ⟨a, b, hab, ?_⟩
  rw [hGF] at hcount ⊢
  exact interior_incidence_one_wall N y hy F u a b k.val hbot htop' hab ha hb hu hv'
    huc hr' hmissing hcard hchain hgap hFP hcount


/-- Every concrete interior incidence-one facet lies on a chamber wall. -/


@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem concrete_interior_facet_wall {J : Type*} [Fintype J] [LinearOrder J]
    (N : ℕ) (T G : Finset (J → Fin (N+1)))
    (hT : T ∈ boundedChainSimplices N (Fintype.card J) Monotone)
    (hGT : G ⊆ T) (hG : G.card = Fintype.card J)
    (hinterior : ∃ (y : J → ℕ) (c : Fin (Fintype.card J + 1) → Finset J)
      (v : Fin (Fintype.card J + 1) → J → Fin (N+1)) (k : Fin (Fintype.card J + 1)), Monotone c ∧ (∀ j, (c j).card = j.val) ∧
      (∀ j i, (v j i).val = y i + if i ∈ c j then 1 else 0) ∧
      (∀ j, Monotone (v j)) ∧ G = (Finset.univ.erase k).image v ∧
      0 < k.val ∧ k.val < Fintype.card J)
    (hcount : ((boundedChainSimplices N (Fintype.card J) Monotone).filter (fun T => G ⊆ T)).card = 1) :
    ∃ a b : J, a ≠ b ∧ ∀ v ∈ G, v a = v b := by
  classical
  obtain ⟨y,c,v,k,hc,hr,hv,hch,hGv,hk0,hkn⟩ := hinterior
  let top : Fin (Fintype.card J + 1) := ⟨Fintype.card J, by omega⟩
  have htop : c top = Finset.univ := by
    apply Finset.eq_univ_of_card
    simpa [top] using hr top
  have hy : ∀ i, y i + 1 ≤ N := by
    intro i
    have h := (v top i).isLt
    rw [hv, htop] at h
    simp only [Finset.mem_univ, ↓reduceIte] at h
    omega
  let enc : Finset J → J → Fin (N+1) := fun s i => ⟨y i + if i ∈ s then 1 else 0, by
      have := hy i; split_ifs <;> omega⟩
  have he : ∀ j, v j = enc (c j) := by
    intro j; funext i; apply Fin.ext; exact hv j i
  let F := (Finset.univ.erase k).image c
  have hGF : G = F.image enc := by
    rw [hGv]; dsimp [F]; rw [Finset.image_image]
    congr 1
    funext j
    exact he j
  have hFP : ∀ s ∈ F, Monotone (fun i => y i + if i ∈ s then 1 else 0) := by
    intro s hs
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hs
    intro i l hil
    have h := hch j hil
    change (v j i).val ≤ (v j l).val at h
    simpa only [hv] using h
  have hk : k = (⟨k.val, by omega⟩ : Fin (Fintype.card J + 1)) := rfl
  have hgap := deleted_interior_boolean_chain (Fintype.card J) k.val rfl hk0 hkn c hc hr
  rw [← hk] at hgap
  change ∃ u a b, _ at hgap
  obtain ⟨u,a,b,hab,ha,hb,hu,hv',huc,hr',hmissing,hcard,hchain,hgap,hbot,htop'⟩ := hgap
  refine ⟨a,b,hab,?_⟩
  rw [hGF] at hcount ⊢
  exact interior_incidence_one_wall N y hy F u a b k.val hbot htop'
    hab ha hb hu hv' huc hr' hmissing hcard hchain hgap hFP hcount


/-- Every actual incidence-one chamber facet lies on an outer or equality wall. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem actual_incidence_one_wall {J : Type*} [Fintype J] [LinearOrder J]
    (N : ℕ) (T G : Finset (J → Fin (N+1)))
    (hT : T ∈ boundedChainSimplices N (Fintype.card J) Monotone)
    (hGT : G ⊆ T) (hG : G.card = Fintype.card J) (hp : 0 < Fintype.card J)
    (hone : ((boundedChainSimplices N (Fintype.card J) Monotone).filter (fun T => G ⊆ T)).card = 1) :
    (∃ a, ∀ v ∈ G, (v a).val = 0) ∨ (∃ a, ∀ v ∈ G, (v a).val = N) ∨
    (∃ a b, a ≠ b ∧ ∀ v ∈ G, v a = v b) := by
  rcases actual_incidence_one_outer_or_interior N T G hT hGT hG hp hone with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (concrete_interior_incidence_one_wall N T G hT hGT hG h hone))
/-- Auxiliary common wall adjacent result for the lattice construction.
The proof uses the preceding finite, order, and continuity lemmas as applicable. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem common_wall_adjacent {n : ℕ} {α : Type*} [LinearOrder α]
    (G : Finset (Fin n → α)) (hmono : ∀ v ∈ G, Monotone v)
    (a b : Fin n) (hne : a ≠ b) (heq : ∀ v ∈ G, v a = v b) :
    ∃ i : Fin n, ∃ j : Fin n, j.val = i.val + 1 ∧ ∀ v ∈ G, v i = v j := by
  have hlt : a < b ∨ b < a := lt_or_gt_of_ne hne
  rcases hlt with hab | hba
  · let j : Fin n := ⟨a.val + 1, by have := b.isLt; have : a.val < b.val := hab; omega⟩
    refine ⟨a,j,rfl,?_⟩
    intro v hv
    have hj : j ≤ b := Fin.le_def.mpr (by have : a.val < b.val := hab; dsimp [j]; omega)
    have ha : a ≤ j := Fin.le_def.mpr (by dsimp [j]; omega)
    exact le_antisymm (hmono v hv ha) (by rw [heq v hv]; exact hmono v hv hj)
  · let j : Fin n := ⟨b.val + 1, by have := a.isLt; have : b.val < a.val := hba; omega⟩
    refine ⟨b,j,rfl,?_⟩
    intro v hv
    have hj : j ≤ a := Fin.le_def.mpr (by have : b.val < a.val := hba; dsimp [j]; omega)
    have hb : b ≤ j := Fin.le_def.mpr (by dsimp [j]; omega)
    exact le_antisymm (hmono v hv hb) (by rw [← heq v hv]; exact hmono v hv hj)

/-- Incidence-one facets of the ordered lattice chamber lie on one of its standard walls. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem actual_incidence_one_standard_wall (n N : ℕ)
    (T G : Finset (Fin (n+1) → Fin (N+1)))
    (hT : T ∈ boundedChainSimplices N (n+1) Monotone)
    (hGT : G ⊆ T) (hG : G.card = n+1)
    (hone : ((boundedChainSimplices N (n+1) Monotone).filter (fun T => G ⊆ T)).card = 1) :
    (∀ v ∈ G, (v 0).val = 0) ∨
    (∀ v ∈ G, (v (Fin.last n)).val = N) ∨
    ∃ i j : Fin (n+1), j.val = i.val + 1 ∧ ∀ v ∈ G, v i = v j := by
  classical
  have hm : ∀ v ∈ G, Monotone v := by
    intro v hv
    exact (boundedChainSimplices_cube N (n+1) Monotone T hT).1 v (hGT hv)
  have hw := actual_incidence_one_wall N T G (by simpa using hT) hGT (by simpa using hG) (by simp) (by simpa using hone)
  rcases hw with ⟨a,ha⟩ | ⟨a,ha⟩ | ⟨a,b,hab,heq⟩
  · left; intro v hv
    have hv' := hm v hv (show (0 : Fin (n+1)) ≤ a from Fin.zero_le a)
    have he := ha v hv
    change (v 0).val ≤ (v a).val at hv'
    omega
  · right; left; intro v hv
    have hv' := hm v hv (Fin.le_last a)
    have he := ha v hv
    have ht := (v (Fin.last n)).isLt
    change (v a).val ≤ (v (Fin.last n)).val at hv'
    omega
  · right; right
    exact common_wall_adjacent G hm a b hab heq

/-- Prefixing the minimum lattice coordinate preserves the ordered chamber. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem monotone_fin_cons_zero {n N : ℕ} (v : Fin n → Fin (N+1)) (hv : Monotone v) :
    Monotone (Fin.cons 0 v) := by
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i
  · intro _; exact Fin.zero_le _
  · refine Fin.cases ?_ (fun j => ?_) j
    · intro hij; have h : ¬ i.succ ≤ (0 : Fin (n+1)) := by simp
      exact (h hij).elim
    · intro hij; exact hv (Fin.succ_le_succ_iff.mp hij)

/-- Restricting an ordered tuple on the lower wall to the remaining coordinates
recovers a unique smaller ordered tuple. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem zero_wall_cons_equiv {n N : ℕ} (v : Fin (n+1) → Fin (N+1))
    (h0 : v 0 = 0) : Fin.cons 0 (fun i => v i.succ) = v := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using h0.symm
  · simp

/-- Appending a universal set to a monotone Boolean chain preserves monotonicity. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem monotone_snoc_univ {n : ℕ} {J : Type*} [DecidableEq J] [Fintype J]
    (c : Fin n → Finset J) (hc : Monotone c) :
    Monotone (Fin.snoc c Finset.univ) := by
  intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · intro hij
    have hj : j = Fin.last n := by
      apply Fin.ext; have := j.isLt; change n ≤ j.val at hij; simp; omega
    subst j; simp
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · intro _; simp
    · intro hij
      simpa only [Fin.snoc_castSucc] using hc (Fin.castSucc_le_castSucc_iff.mp hij)

/-- A lower-dimensional graded Boolean chain becomes a graded chain in the
ambient coordinate set by omitting coordinate zero and appending the full set. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem graded_chain_zero_wall {n : ℕ} (c : Fin (n+1) → Finset (Fin n))
    (hc : Monotone c) (hr : ∀ k, (c k).card = k.val) :
    let d : Fin (n+2) → Finset (Fin (n+1)) :=
      Fin.snoc (fun k => (c k).image Fin.succ) Finset.univ
    Monotone d ∧ (∀ k, (d k).card = k.val) := by
  classical
  dsimp only
  constructor
  · apply monotone_snoc_univ
    intro i j hij
    exact Finset.image_subset_image (hc hij)
  · intro k
    refine Fin.lastCases ?_ (fun i => ?_) k
    · simp
    · simp only [Fin.snoc_castSucc, Fin.val_castSucc]
      rw [Finset.card_image_iff.mpr (fun _ _ _ _ h => Fin.succ_injective n h), hr]

/-- Prefixing any lower bound to a monotone tuple preserves monotonicity. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem monotone_fin_cons_of_le {n : ℕ} {α : Type*} [Preorder α]
    (a : α) (v : Fin n → α) (hv : Monotone v) (ha : ∀ i, a ≤ v i) :
    Monotone (Fin.cons a v) := by
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · intro _; exact le_rfl
    · intro _; simpa using ha j
  · refine Fin.cases ?_ (fun j => ?_) j
    · intro hij; have h : ¬ i.succ ≤ (0 : Fin (n+1)) := by simp
      exact (h hij).elim
    · intro hij; exact hv (Fin.succ_le_succ_iff.mp hij)

/-- The upper completion of a zero-wall cell has its first coordinate at most
all the others. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem upper_completion_chamber {n N : ℕ} (y : Fin n → ℕ)
    (hy : ∀ i, y i + 1 ≤ N)
    (hmono : Monotone (fun i => (⟨y i + 1, by have := hy i; omega⟩ : Fin (N+1))))
    (hN : 0 < N) :
    Monotone (Fin.cons (⟨1, by omega⟩ : Fin (N+1))
      (fun i => ⟨y i + 1, by have := hy i; omega⟩)) := by
  apply monotone_fin_cons_of_le _ _ hmono
  intro i
  change 1 ≤ y i + 1
  omega

/-- A lower-wall lattice chain admits its canonical upper completion. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem zero_wall_chain_completion {n N : ℕ} (hN : 0 < N)
    (y : Fin n → ℕ) (c : Fin (n+1) → Finset (Fin n))
    (v : Fin (n+1) → Fin n → Fin (N+1))
    (hc : Monotone c) (hr : ∀ k, (c k).card = k.val)
    (hv : ∀ k i, (v k i).val = y i + if i ∈ c k then 1 else 0)
    (hm : ∀ k, Monotone (v k)) :
    ∃ (d : Fin (n+2) → Finset (Fin (n+1)))
      (w : Fin (n+2) → Fin (n+1) → Fin (N+1)),
      Monotone d ∧ (∀ k, (d k).card = k.val) ∧
      (∀ k i, (w k i).val = (Fin.cons (α := fun _ => ℕ) 0 y) i + if i ∈ d k then 1 else 0) ∧
      (∀ k, Monotone (w k)) ∧
      (∀ k : Fin (n+1), w k.castSucc = Fin.cons 0 (v k)) := by
  classical
  have hlast : c (Fin.last n) = Finset.univ := Finset.eq_univ_of_card _ (by simpa using hr (Fin.last n))
  have hy : ∀ i, y i + 1 ≤ N := by
    intro i
    have h := (v (Fin.last n) i).isLt
    rw [hv, hlast] at h
    simp only [Finset.mem_univ, ↓reduceIte] at h
    omega
  let top : Fin n → Fin (N+1) := fun i => ⟨y i + 1, by have := hy i; omega⟩
  let d : Fin (n+2) → Finset (Fin (n+1)) :=
    Fin.snoc (fun k => (c k).image Fin.succ) Finset.univ
  let w : Fin (n+2) → Fin (n+1) → Fin (N+1) :=
    Fin.snoc (fun k => Fin.cons 0 (v k)) (Fin.cons ⟨1, by omega⟩ top)
  refine ⟨d, w, (graded_chain_zero_wall c hc hr).1, (graded_chain_zero_wall c hc hr).2, ?_, ?_, ?_⟩
  · intro k i
    refine Fin.lastCases ?_ (fun k => ?_) k
    · refine Fin.cases ?_ (fun i => ?_) i <;> simp [w, d, top]
    · refine Fin.cases ?_ (fun i => ?_) i
      · simp [w, d]
      · simp only [w, d, Fin.snoc_castSucc, Fin.cons_succ, Finset.mem_image]
        have he : (∃ a ∈ c k, a.succ = i.succ) ↔ i ∈ c k := by
          constructor
          · rintro ⟨a, ha, h⟩; exact Fin.succ_injective n h ▸ ha
          · intro hi; exact ⟨i, hi, rfl⟩
        simpa only [he] using hv k i
  · intro k
    refine Fin.lastCases ?_ (fun k => ?_) k
    · simpa [w, top] using upper_completion_chamber y hy (by
        have ht : top = v (Fin.last n) := by
          funext i; apply Fin.ext; simp [top, hv, hlast]
        change Monotone top; rw [ht]; exact hm _) hN
    · simpa [w] using monotone_fin_cons_zero (v k) (hm k)
  · intro k; simp [w]

/-- Every lower-dimensional chamber simplex lifts to a facet of an ambient
chamber simplex, with the lower wall identified by prefixing zero. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem zero_wall_simplex_has_completion (n N : ℕ) (hN : 0 < N)
    (S : Finset (Fin n → Fin (N+1)))
    (hS : S ∈ boundedChainSimplices N n Monotone) :
    ∃ T ∈ boundedChainSimplices N (n+1) Monotone,
      S.image (fun v => Fin.cons (α := fun _ => Fin (N+1)) 0 v) ⊆ T ∧
      (S.image (fun v => Fin.cons (α := fun _ => Fin (N+1)) 0 v)).card = n+1 := by
  classical
  obtain ⟨y, c, v, hc, hr, hv, hm, rfl⟩ := boundedChainSimplices_spec N n Monotone S hS
  obtain ⟨d, w, hd, hdr, hw, hwm, heq⟩ := zero_wall_chain_completion hN y c v hc hr hv hm
  let T := Finset.univ.image w
  have hT : T ∈ boundedChainSimplices N (n+1) Monotone := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, Fin.cons (α := fun _ => ℕ) 0 y, d, w, hd, hdr, hw, hwm, rfl⟩
  refine ⟨T, hT, ?_, ?_⟩
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨k.castSucc, Finset.mem_univ _, heq k⟩
  · rw [Finset.card_image_iff.mpr (by
        intro a ha b hb h
        funext i
        exact congrFun h i.succ)]
    exact boundedChainSimplices_card N n Monotone _ (by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, y, c, v, hc, hr, hv, hm, rfl⟩)

/-- The canonical lift is incident to exactly one ambient simplex. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem zero_wall_lift_incidence_one (n N : ℕ) (hN : 0 < N)
    (S : Finset (Fin n → Fin (N+1)))
    (hS : S ∈ boundedChainSimplices N n Monotone) :
    ((boundedChainSimplices N (n+1) Monotone).filter
      (fun T => S.image (fun v => Fin.cons (α := fun _ => Fin (N+1)) 0 v) ⊆ T)).card = 1 := by
  classical
  let lift : (Fin n → Fin (N+1)) → (Fin (n+1) → Fin (N+1)) := fun v => Fin.cons 0 v
  let F := S.image lift
  obtain ⟨T, hT, hFT, hcard⟩ := zero_wall_simplex_has_completion n N hN S hS
  obtain ⟨y, L, H, hL, hH, hLS, hHS, _⟩ :=
    boundedChainSimplices_corners N Monotone S (by simpa using hS)
  have h := boundedChainSimplices_top_outer_incident_one N Monotone
    (Fin.cons (α := fun _ => ℕ) 0 y) (0 : Fin (n+1)) F T (by simpa [F, lift] using hcard)
    (lift L) (lift H) (Finset.mem_image.mpr ⟨L,hLS,rfl⟩)
    (Finset.mem_image.mpr ⟨H,hHS,rfl⟩) ?_ ?_ ?_ ?_ (by simpa using hT) hFT
  · simpa [F, lift] using h
  · intro i; refine Fin.cases ?_ (fun i => ?_) i <;> simp [lift, hL]
  · intro i; refine Fin.cases ?_ (fun i => ?_) i <;> simp [lift, hH]
  · intro v hv
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hv
    simp [lift]
  · simp

/-- Every full-size face of a chamber simplex lying on the zero wall is the
lift of a lower-dimensional chamber simplex. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem zero_wall_facet_converse (n N : ℕ)
    (F T : Finset (Fin (n+1) → Fin (N+1)))
    (hT : T ∈ boundedChainSimplices N (n+1) Monotone)
    (hFT : F ⊆ T) (hF : F.card = n+1)
    (hzero : ∀ v ∈ F, v 0 = 0) :
    ∃ S ∈ boundedChainSimplices N n Monotone,
      S.image (fun v => Fin.cons (α := fun _ => Fin (N+1)) 0 v) = F := by
  classical
  obtain ⟨y,c,v,hc,hr,hv,hm,hTeq⟩ := boundedChainSimplices_spec N (n+1) Monotone T hT
  have hlast : c (Fin.last (n+1)) = Finset.univ :=
    Finset.eq_univ_of_card _ (by simpa using hr (Fin.last (n+1)))
  have hvlast : v (Fin.last (n+1)) ∉ F := by
    intro hmem
    have hz := congrArg Fin.val (hzero _ hmem)
    rw [hv, hlast] at hz
    simp at hz
  have hFeq : F = T.erase (v (Fin.last (n+1))) := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      exact Finset.mem_erase.mpr ⟨by intro he; subst x; exact hvlast hx, hFT hx⟩
    · rw [Finset.card_erase_of_mem (by rw [hTeq]; exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩), boundedChainSimplices_card N (n+1) Monotone T hT, hF]
      omega
  have hvinj : Function.Injective v := by
    intro a b hab
    have he : c a = c b := by
      ext i
      have h := congrArg Fin.val (congrFun hab i)
      rw [hv, hv] at h
      by_cases ha : i ∈ c a <;> by_cases hb : i ∈ c b <;> simp_all
    apply Fin.ext
    have := congrArg Finset.card he
    simpa [hr] using this
  have hFimage : F = Finset.univ.image (fun k : Fin (n+1) => v k.castSucc) := by
    rw [hFeq, hTeq]
    ext x
    simp only [Finset.mem_erase, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hne, k, rfl⟩
      have hk : k ≠ Fin.last (n+1) := by intro he; subst k; exact hne rfl
      obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hk
      exact ⟨j, rfl⟩
    · rintro ⟨k,rfl⟩
      exact ⟨by intro he; have := hvinj he; have := congrArg Fin.val this; simp at this; have := k.isLt; omega, k.castSucc, rfl⟩
  have hz (k : Fin (n+1)) : v k.castSucc 0 = 0 := by
    apply hzero
    rw [hFimage]
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  have hnot (k : Fin (n+1)) : (0 : Fin (n+1)) ∉ c k.castSucc := by
    intro h
    have hh := congrArg Fin.val (hz k)
    rw [hv] at hh
    simp [h] at hh
  let d : Fin (n+1) → Finset (Fin n) := fun k => Finset.univ.filter (fun i => i.succ ∈ c k.castSucc)
  have hdimg (k : Fin (n+1)) : (d k).image Fin.succ = c k.castSucc := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hnot]
    · simp [d, Fin.succ_injective]
  have hdmono : Monotone d := by
    intro i j hij x hx
    simp only [d, Finset.mem_filter, Finset.mem_univ, true_and] at *
    exact hc (Fin.castSucc_le_castSucc_iff.mpr hij) hx
  have hdcard (k : Fin (n+1)) : (d k).card = k.val := by
    have h := congrArg Finset.card (hdimg k)
    rw [Finset.card_image_iff.mpr (fun _ _ _ _ he => Fin.succ_injective n he), hr] at h
    exact h
  let w : Fin (n+1) → Fin n → Fin (N+1) := fun k i => v k.castSucc i.succ
  let S := Finset.univ.image w
  refine ⟨S, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, (fun i => y i.succ), d, w, hdmono, hdcard, ?_, ?_, rfl⟩
    · intro k i
      simpa [w, d] using hv k.castSucc i.succ
    · intro k i j hij
      exact hm k.castSucc (Fin.succ_le_succ_iff.mpr hij)
  · rw [hFimage]
    simp only [S, Finset.image_image]
    congr 1
    funext k
    exact zero_wall_cons_equiv _ (hz k)
open Finset
open scoped BigOperators

/-- Finite differences telescope along a finite chain. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem fin_sum_differences (n : ℕ) (p : Fin (n+1) → ℝ) :
    ∑ i : Fin n, (p i.succ - p i.castSucc) = p (Fin.last n) - p 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    have h := ih (fun i => p i.castSucc)
    simp only [Fin.castSucc_zero] at h
    have hcomm : ∀ i : Fin n, i.castSucc.succ = i.succ.castSucc := by intro i; apply Fin.ext; rfl
    simp_rw [hcomm] 
    rw [h]
    simp only [Fin.succ_last]
    ring

/-- Convert a monotone chain with prescribed endpoints into simplex coordinates. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
noncomputable def chainSimplex {n : ℕ} (p : Fin (n+2) → ℝ) (N : ℝ) : Fin (n+1) → ℝ :=
  fun i => (p i.succ - p i.castSucc) / N

/-- Auxiliary chainSimplex mem result for the lattice construction.
The proof uses the preceding finite, order, and continuity lemmas as applicable. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem chainSimplex_mem {n : ℕ} (p : Fin (n+2) → ℝ) (N : ℝ)
    (hN : 0 < N) (hp : Monotone p) (hzero : p 0 = 0)
    (hlast : p (Fin.last (n+1)) = N) :
    (∀ i, 0 ≤ chainSimplex p N i) ∧ ∑ i, chainSimplex p N i = 1 := by
  constructor
  · intro i
    apply div_nonneg _ hN.le
    apply sub_nonneg.mpr
    apply hp
    exact Fin.le_def.mpr (by simp)
  · simp only [chainSimplex, ← Finset.sum_div, fin_sum_differences, hzero, hlast, sub_zero]
    exact div_self (ne_of_gt hN)

/-- Equality at adjacent cumulative coordinates is exactly a zero simplex coordinate. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem chainSimplex_zero_iff {n : ℕ} (p : Fin (n+2) → ℝ) (N : ℝ)
    (hN : 0 < N) (i : Fin (n+1)) :
    chainSimplex p N i = 0 ↔ p i.succ = p i.castSucc := by
  simp [chainSimplex, ne_of_gt hN, sub_eq_zero]

/-- Uniformly close cumulative coordinates give a twice-as-close barycentric mesh. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem chainSimplex_dist {n : ℕ} (p q : Fin (n+2) → ℝ) (N : ℝ)
    (hN : 0 < N) (h : ∀ i, |p i - q i| ≤ 1) :
    dist (chainSimplex p N) (chainSimplex q N) ≤ 2 / N := by
  apply (dist_pi_le_iff (by positivity)).2
  intro i
  simp only [chainSimplex, Real.dist_eq, ← sub_div, abs_div, abs_of_pos hN]
  apply div_le_div_of_nonneg_right _ hN.le
  have hh := abs_sub (p i.succ - q i.succ) (p i.castSucc - q i.castSucc)
  have he : (p i.succ - p i.castSucc) - (q i.succ - q i.castSucc) =
      (p i.succ - q i.succ) - (p i.castSucc - q i.castSucc) := by ring
  rw [he]
  linarith [h i.succ, h i.castSucc]

/-- Pad an ordered lattice tuple with zero and the mesh denominator. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
noncomputable def chainPad {n N : ℕ} (v : Fin (n+1) → Fin (N+1)) : Fin (n+3) → ℝ :=
  Fin.cons 0 (Fin.snoc (fun i => (v i).val) N)

/-- Auxiliary chainPad zero result for the lattice construction.
The proof uses the preceding finite, order, and continuity lemmas as applicable. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem chainPad_zero {n N : ℕ} (v : Fin (n+1) → Fin (N+1)) : chainPad v 0 = 0 := by
  simp [chainPad]

/-- Auxiliary chainPad last result for the lattice construction.
The proof uses the preceding finite, order, and continuity lemmas as applicable. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem chainPad_last {n N : ℕ} (v : Fin (n+1) → Fin (N+1)) :
    chainPad v (Fin.last (n+2)) = N := by
  have h : Fin.last (n+2) = (Fin.last (n+1)).succ := by ext; rfl
  rw [h]; simp [chainPad]

/-- Auxiliary chainPad middle result for the lattice construction.
The proof uses the preceding finite, order, and continuity lemmas as applicable. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem chainPad_middle {n N : ℕ} (v : Fin (n+1) → Fin (N+1)) (i : Fin (n+1)) :
    chainPad v i.castSucc.succ = (v i).val := by
  simp [chainPad]

/-- Auxiliary chainPad monotone result for the lattice construction.
The proof uses the preceding finite, order, and continuity lemmas as applicable. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem chainPad_monotone {n N : ℕ} (v : Fin (n+1) → Fin (N+1)) (hv : Monotone v) :
    Monotone (chainPad v) := by
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i
  · intro _; simp only [chainPad, Fin.cons_zero]
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [chainPad]
    · simp only [chainPad, Fin.cons_succ]
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simp
      · simp
  · refine Fin.cases ?_ (fun j => ?_) j
    · intro hij; have : ¬ i.succ ≤ (0 : Fin (n+3)) := by simp
      exact (this hij).elim
    · intro hij
      have hij' : i ≤ j := Fin.succ_le_succ_iff.mp hij
      clear hij
      simp only [chainPad, Fin.cons_succ]
      revert hij'
      refine Fin.lastCases ?_ (fun i => ?_) i
      · intro hij'
        have hj : j = Fin.last (n+1) := by
          apply Fin.ext
          have := j.isLt
          change n+1 ≤ j.val at hij'
          simp; omega
        subst j; simp
      · revert j
        intro j
        refine Fin.lastCases ?_ (fun j => ?_) j
        · intro hij'
          simp only [Fin.snoc_last, Fin.snoc_castSucc]
          exact_mod_cast Nat.le_of_lt_succ (v i).isLt
        · intro hij'
          simp only [Fin.snoc_castSucc]
          exact_mod_cast (hv (Fin.castSucc_le_castSucc_iff.mp hij'))

/-- The padded chain produces a simplex point, including degenerate dimensions. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem lattice_chain_simplex {n N : ℕ} (v : Fin (n+1) → Fin (N+1))
    (hN : 0 < N) (hv : Monotone v) :
    (∀ i, 0 ≤ chainSimplex (chainPad v) N i) ∧
    ∑ i, chainSimplex (chainPad v) N i = 1 := by
  apply chainSimplex_mem
  · exact_mod_cast hN
  · exact chainPad_monotone v hv
  · exact chainPad_zero v
  · exact chainPad_last v

/-- The zero-th simplex coordinate vanishes exactly on the first chamber wall. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem lattice_simplex_zero_wall {n N : ℕ} (v : Fin (n+1) → Fin (N+1))
    (hN : 0 < N) : chainSimplex (chainPad v) N 0 = 0 ↔ v 0 = 0 := by
  rw [chainSimplex_zero_iff _ _ (by exact_mod_cast hN)]
  have h1 : (0 : Fin (n+2)).succ = (0 : Fin (n+1)).castSucc.succ := by ext; rfl
  rw [h1, chainPad_middle]
  change ((v 0).val : ℝ) = 0 ↔ v 0 = 0
  simp only [Nat.cast_eq_zero]
  constructor
  · intro h; apply Fin.ext; simpa using h
  · intro h; simpa using congrArg Fin.val h

/-- The final simplex coordinate vanishes exactly on the last chamber wall. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem lattice_simplex_last_wall {n N : ℕ} (v : Fin (n+1) → Fin (N+1))
    (hN : 0 < N) : chainSimplex (chainPad v) N (Fin.last (n+1)) = 0 ↔
      (v (Fin.last n)).val = N := by
  rw [chainSimplex_zero_iff _ _ (by exact_mod_cast hN)]
  have h1 : (Fin.last (n+1)).succ = Fin.last (n+2) := by ext; rfl
  have h2 : (Fin.last (n+1)).castSucc = (Fin.last n).castSucc.succ := by ext; rfl
  rw [h1, h2, chainPad_last, chainPad_middle]
  exact_mod_cast eq_comm

/-- Interior simplex coordinate vanishing corresponds to equality of adjacent lattice coordinates. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem lattice_simplex_inner_wall {n N : ℕ} (v : Fin (n+1) → Fin (N+1))
    (hN : 0 < N) (i : Fin n) : chainSimplex (chainPad v) N i.succ.castSucc = 0 ↔
      v i.succ = v i.castSucc := by
  rw [chainSimplex_zero_iff _ _ (by exact_mod_cast hN)]
  have h1 : i.succ.castSucc.succ = i.succ.castSucc.succ := rfl
  have h2 : i.succ.castSucc.castSucc = i.castSucc.castSucc.succ := by ext; rfl
  rw [h1, h2, chainPad_middle, chainPad_middle]
  exact_mod_cast (Fin.ext_iff : v i.succ = v i.castSucc ↔ _).symm

/-- Padding preserves a unit coordinate bound. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem chainPad_bound {n N : ℕ} (v w : Fin (n+1) → Fin (N+1))
    (h : ∀ i, |((v i).val : ℝ) - (w i).val| ≤ 1) :
    ∀ i, |chainPad v i - chainPad w i| ≤ 1 := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [chainPad]
  · refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [chainPad]
    · simpa [chainPad] using h i

/-- Unit cube lattice vertices map to barycentric mesh points at distance ≤ 2/N. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem lattice_simplex_dist {n N : ℕ} (v w : Fin (n+1) → Fin (N+1))
    (hN : 0 < N) (h : ∀ i, |((v i).val : ℝ) - (w i).val| ≤ 1) :
    dist (chainSimplex (chainPad v) N) (chainSimplex (chainPad w) N) ≤ 2 / N :=
  chainSimplex_dist _ _ _ (by exact_mod_cast hN) (chainPad_bound v w h)

/-- Prefixing a zero lattice coordinate shifts the padded chain by one place. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem chainPad_cons_zero {n N : ℕ} (v : Fin (n+1) → Fin (N+1))
    (i : Fin (n+3)) :
    chainPad (Fin.cons 0 v) i.succ = chainPad v i := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [chainPad]
  · refine Fin.lastCases ?_ (fun i => ?_) i
    · have h1 : (Fin.last (n+1)).succ.succ = Fin.last (n+3) := by ext; rfl
      have h2 : (Fin.last (n+1)).succ = Fin.last (n+2) := by ext; rfl
      rw [h1, h2, chainPad_last, chainPad_last]
    · have h1 : i.castSucc.succ.succ = i.succ.castSucc.succ := by ext; rfl
      rw [h1, chainPad_middle, chainPad_middle]
      simp

/-- On the first wall, simplex coordinates are the smaller simplex coordinates
with a leading zero; in particular a positive-coordinate labeling restricts. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem lattice_simplex_cons_zero {n N : ℕ} (v : Fin (n+1) → Fin (N+1))
    (i : Fin (n+2)) :
    chainSimplex (chainPad (Fin.cons 0 v)) N i.succ = chainSimplex (chainPad v) N i := by
  simp only [chainSimplex]
  have h : i.succ.castSucc = i.castSucc.succ := by ext; rfl
  rw [h, chainPad_cons_zero, chainPad_cons_zero]

/-- Fully labeled facets omitting color zero cannot lie on any of the other
standard walls when labels are chosen from positive barycentric coordinates. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem selected_facet_first_wall {n N : ℕ} (hN : 0 < N)
    (G : Finset (Fin (n+1) → Fin (N+1)))
    (label : (Fin (n+1) → Fin (N+1)) → Fin (n+2))
    (hpos : ∀ v ∈ G, 0 < chainSimplex (chainPad v) N (label v))
    (hcolors : ∀ i : Fin (n+2), i ≠ 0 → ∃ v ∈ G, label v = i)
    (hw : (∀ v ∈ G, (v 0).val = 0) ∨
      (∀ v ∈ G, (v (Fin.last n)).val = N) ∨
      ∃ i j : Fin (n+1), j.val = i.val + 1 ∧ ∀ v ∈ G, v i = v j) :
    ∀ v ∈ G, (v 0).val = 0 := by
  rcases hw with hfirst | hlast | ⟨i,j,hij,heq⟩
  · exact hfirst
  · obtain ⟨v,hv,hlabel⟩ := hcolors (Fin.last (n+1)) (by simp)
    have hz := (lattice_simplex_last_wall v hN).2 (hlast v hv)
    have hp := hpos v hv
    rw [hlabel, hz] at hp
    exact (lt_irrefl 0 hp).elim
  · have hi : i.val < n := by have := j.isLt; omega
    let k : Fin n := ⟨i.val, hi⟩
    have hik : k.castSucc = i := by apply Fin.ext; rfl
    have hjk : k.succ = j := by apply Fin.ext; simp [k]; omega
    let color : Fin (n+2) := k.succ.castSucc
    have hc : color ≠ 0 := by intro h; have := congrArg Fin.val h; dsimp [color] at this; simp at this
    obtain ⟨v,hv,hlabel⟩ := hcolors color hc
    have he : v k.succ = v k.castSucc := by rw [hjk,hik]; exact (heq v hv).symm
    have hz := (lattice_simplex_inner_wall v hN k).2 he
    have hp := hpos v hv
    rw [hlabel, hz] at hp
    exact (lt_irrefl 0 hp).elim

/-- Positive labels restrict along the first wall by dropping color zero. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem zero_wall_restrict_label (n N : ℕ) (hN : 0 < N)
    (label : (Fin (n+2) → Fin (N+1)) → Fin (n+3))
    (hpos : ∀ v, Monotone v → 0 < chainSimplex (chainPad v) N (label v)) :
    ∃ lower : (Fin (n+1) → Fin (N+1)) → Fin (n+2),
      (∀ v, Monotone v → 0 < chainSimplex (chainPad v) N (lower v)) ∧
      (∀ v, Monotone v → (lower v).succ = label (Fin.cons 0 v)) := by
  classical
  let lower : (Fin (n+1) → Fin (N+1)) → Fin (n+2) := fun v =>
    if h : label (Fin.cons 0 v) ≠ 0 then (label (Fin.cons 0 v)).pred h else 0
  have hn (v : Fin (n+1) → Fin (N+1)) (hm : Monotone v) :
      label (Fin.cons 0 v) ≠ 0 := by
    intro he
    have hp := hpos (Fin.cons 0 v) (monotone_fin_cons_zero v hm)
    have hz := (lattice_simplex_zero_wall (Fin.cons 0 v) hN).2 (by simp)
    rw [he, hz] at hp
    exact (lt_irrefl _ hp)
  refine ⟨lower, ?_, ?_⟩
  · intro v hm
    have hp := hpos (Fin.cons 0 v) (monotone_fin_cons_zero v hm)
    have he : (lower v).succ = label (Fin.cons 0 v) := by
      simp [lower, hn v hm, Fin.succ_pred]
    rw [← he, lattice_simplex_cons_zero] at hp
    exact hp
  · intro v hm
    simp [lower, hn v hm, Fin.succ_pred]

/-- Under a first-wall label correspondence, a lower simplex is fully labeled
exactly when its lift carries every nonzero ambient color. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem zero_wall_full_label_iff (n N : ℕ)
    (label : (Fin (n+2) → Fin (N+1)) → Fin (n+3))
    (lower : (Fin (n+1) → Fin (N+1)) → Fin (n+2))
    (heq : ∀ v, Monotone v → (lower v).succ = label (Fin.cons 0 v))
    (S : Finset (Fin (n+1) → Fin (N+1)))
    (hS : S ∈ boundedChainSimplices N (n+1) Monotone) :
    (∀ i, ∃ v ∈ S, lower v = i) ↔
      (∀ i : Fin (n+3), i ≠ 0 →
        ∃ v ∈ S.image (fun v => Fin.cons (α := fun _ => Fin (N+1)) 0 v), label v = i) := by
  classical
  have hm : ∀ v ∈ S, Monotone v := (boundedChainSimplices_cube N (n+1) Monotone S hS).1
  constructor
  · intro h i hi
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hi
    obtain ⟨v, hv, hl⟩ := h j
    exact ⟨Fin.cons 0 v, Finset.mem_image.mpr ⟨v,hv,rfl⟩, by rw [← heq v (hm v hv), hl]⟩
  · intro h i
    obtain ⟨v, hv, hl⟩ := h i.succ (by simp)
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    refine ⟨w, hw, Fin.succ_injective _ ?_⟩
    rw [heq w (hm w hw), hl]

/-- The zero-dimensional chamber contains exactly one zero-simplex. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem zero_dimensional_chambers (N : ℕ) :
    boundedChainSimplices N 0 (Monotone : (Fin 0 → Fin (N+1)) → Prop) =
      { { (fun i : Fin 0 => Fin.elim0 i) } } := by
  classical
  have hfun : ∀ v : Fin 0 → Fin (N+1), v = (fun i => Fin.elim0 i) := by
    intro v; funext i; exact Fin.elim0 i
  ext S
  simp only [Finset.mem_singleton]
  constructor
  · intro hS
    have hc := boundedChainSimplices_card N 0 Monotone S hS
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨v, hv⟩ := hne
    ext x
    simp only [Finset.mem_singleton]
    constructor
    · intro _; exact hfun x
    · intro hx; rw [hx, ← hfun v]; exact hv
  · intro hS
    subst S
    simp only [boundedChainSimplices, Finset.mem_filter, Finset.mem_univ, true_and]
    let v : Fin 1 → Fin 0 → Fin (N+1) := fun _ i => Fin.elim0 i
    refine ⟨(fun i => Fin.elim0 i), (fun _ => ∅), v, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j hij; simp
    · intro k; have : k = 0 := by apply Fin.ext; have := k.isLt; simp
      subst k; simp
    · intro k i; exact Fin.elim0 i
    · intro k i; exact Fin.elim0 i
    · ext x; simp [v, hfun x]

/-- The unique zero-dimensional cell is fully labeled, and its count is odd. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem zero_dimensional_full_odd (N : ℕ) (label : (Fin 0 → Fin (N+1)) → Fin 1) :
    Odd (((boundedChainSimplices N 0 (Monotone : (Fin 0 → Fin (N+1)) → Prop)).filter
      (fun S => ∀ i, ∃ v ∈ S, label v = i)).card) := by
  classical
  rw [zero_dimensional_chambers]
  have h : ∀ i : Fin 1, label (fun i : Fin 0 => Fin.elim0 i) = i := by
    intro i; apply Fin.ext; have h1 := (label (fun i : Fin 0 => Fin.elim0 i)).isLt
    have h2 := i.isLt; simp only at *; omega
  have he : (finZeroElim : Fin 0 → Fin (N+1)) = (fun i => Fin.elim0 i) := by
    funext i; exact Fin.elim0 i
  have hp : (∀ i : Fin 1, ∃ v ∈ ({(fun i : Fin 0 => Fin.elim0 i)} : Finset _), label v = i) := by
    intro i; exact ⟨_, Finset.mem_singleton_self _, h i⟩
  rw [Finset.filter_eq_self.mpr (by intro S hS; simp only [Finset.mem_singleton] at hS; subst S; exact hp)]
  simp

/-- The first-wall lift is a bijection from fully labeled lower cells onto the
selected incidence-one facets of the higher chamber. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem zero_wall_boundary_card (n N : ℕ) (hN : 0 < N)
    (label : (Fin (n+2) → Fin (N+1)) → Fin (n+3))
    (lower : (Fin (n+1) → Fin (N+1)) → Fin (n+2))
    (hpos : ∀ v, Monotone v → 0 < chainSimplex (chainPad v) N (label v))
    (heq : ∀ v, Monotone v → (lower v).succ = label (Fin.cons 0 v)) :
    ((boundedChainSimplices N (n+1) Monotone).filter
      (fun S => ∀ i, ∃ v ∈ S, lower v = i)).card =
    ((Finset.univ : Finset (Finset (Fin (n+2) → Fin (N+1)))).filter
      (fun F => F.card = n+2 ∧
        ((boundedChainSimplices N (n+2) Monotone).filter (fun T => F ⊆ T)).card = 1 ∧
        ∀ i : Fin (n+3), i ≠ 0 → ∃ v ∈ F, label v = i)).card := by
  classical
  let lift : (Fin (n+1) → Fin (N+1)) → (Fin (n+2) → Fin (N+1)) := fun v => Fin.cons 0 v
  have hlift : Function.Injective lift := by
    intro a b h; funext i; exact congrFun h i.succ
  apply Finset.card_bij (fun S _ => S.image lift)
  · intro S hS
    obtain ⟨hS, hfull⟩ := Finset.mem_filter.mp hS
    obtain ⟨T, hT, hST, hc⟩ := zero_wall_simplex_has_completion (n+1) N hN S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hc, ?_, ?_⟩
    · exact zero_wall_lift_incidence_one (n+1) N hN S hS
    · exact (zero_wall_full_label_iff n N label lower heq S hS).mp hfull
  · intro S hS U hU he
    exact Finset.image_injective hlift he
  · intro F hF
    obtain ⟨_, hcard, hone, hcolors⟩ := Finset.mem_filter.mp hF
    have hp : 0 < ((boundedChainSimplices N (n+2) Monotone).filter (fun T => F ⊆ T)).card := by omega
    obtain ⟨T, hT⟩ := Finset.card_pos.mp hp
    obtain ⟨hT, hFT⟩ := Finset.mem_filter.mp hT
    have hm : ∀ v ∈ F, Monotone v := fun v hv =>
      (boundedChainSimplices_cube N (n+2) Monotone T hT).1 v (hFT hv)
    have hw := actual_incidence_one_standard_wall (n+1) N T F hT hFT hcard hone
    have hz := selected_facet_first_wall hN F label (fun v hv => hpos v (hm v hv)) hcolors hw
    have hz' : ∀ v ∈ F, v 0 = 0 := by
      intro v hv; apply Fin.ext; simpa using hz v hv
    obtain ⟨S, hS, hSF⟩ := zero_wall_facet_converse (n+1) N F T hT hFT hcard hz'
    refine ⟨S, Finset.mem_filter.mpr ⟨hS, ?_⟩, hSF⟩
    apply (zero_wall_full_label_iff n N label lower heq S hS).mpr
    simpa [hSF] using hcolors

/-- For a one-coordinate chamber the selected boundary is the singleton zero vertex. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem one_dimensional_selected_boundary_card (N : ℕ) (hN : 0 < N)
    (label : (Fin 1 → Fin (N+1)) → Fin 2)
    (hpos : ∀ v, Monotone v → 0 < chainSimplex (chainPad v) N (label v)) :
    ((Finset.univ : Finset (Finset (Fin 1 → Fin (N+1)))).filter
      (fun F => F.card = 1 ∧
        ((boundedChainSimplices N 1 Monotone).filter (fun T => F ⊆ T)).card = 1 ∧
        ∀ i : Fin 2, i ≠ 0 → ∃ v ∈ F, label v = i)).card = 1 := by
  classical
  let p : Fin 1 → Fin (N+1) := fun _ => 0
  have hpmono : Monotone p := by intro i j hij; exact le_rfl
  have hpcolor : label p = 1 := by
    have hh := hpos p hpmono
    have hz := (lattice_simplex_zero_wall p hN).2 rfl
    have hn : label p ≠ 0 := by intro h; rw [h, hz] at hh; exact (lt_irrefl _ hh)
    have hv : (label p).val ≠ 0 := by
      intro h; apply hn; apply Fin.ext; simpa using h
    apply Fin.ext
    have ht := (label p).isLt
    simp only [Fin.val_one]
    omega
  let S : Finset (Fin 0 → Fin (N+1)) := {fun i => Fin.elim0 i}
  have hS : S ∈ boundedChainSimplices N 0 Monotone := by
    rw [zero_dimensional_chambers]; simp [S]
  have he : S.image (fun v => Fin.cons (α := fun _ => Fin (N+1)) 0 v) = {p} := by
    simp [S, p]; congr 1; funext i; have hi : i = 0 := by apply Fin.ext; have := i.isLt; simp
    subst i; simp
  have hone : ((boundedChainSimplices N 1 Monotone).filter (fun T => {p} ⊆ T)).card = 1 := by
    have h := zero_wall_lift_incidence_one 0 N hN S hS
    simpa [he] using h
  have hmem : ({p} : Finset (Fin 1 → Fin (N+1))) ∈
      ((Finset.univ : Finset (Finset (Fin 1 → Fin (N+1)))).filter
        (fun F => F.card = 1 ∧
          ((boundedChainSimplices N 1 Monotone).filter (fun T => F ⊆ T)).card = 1 ∧
          ∀ i : Fin 2, i ≠ 0 → ∃ v ∈ F, label v = i)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.card_singleton]
    refine ⟨hone, ?_⟩
    intro i hi
    have hi' : i = 1 := by fin_cases i <;> simp_all
    exact ⟨p, Finset.mem_singleton_self _, hpcolor.trans hi'.symm⟩
  apply Finset.card_eq_one.mpr
  refine ⟨{p}, ?_⟩
  ext F
  simp only [Finset.mem_singleton]
  constructor
  · intro hF
    obtain ⟨_, hcard, honeF, hcolors⟩ := Finset.mem_filter.mp hF
    have hc : 0 < ((boundedChainSimplices N 1 Monotone).filter (fun T => F ⊆ T)).card := by omega
    obtain ⟨T, hT⟩ := Finset.card_pos.mp hc
    obtain ⟨hT, hFT⟩ := Finset.mem_filter.mp hT
    have hm : ∀ v ∈ F, Monotone v := fun v hv =>
      (boundedChainSimplices_cube N 1 Monotone T hT).1 v (hFT hv)
    have hw := actual_incidence_one_standard_wall 0 N T F hT hFT hcard honeF
    have hz := selected_facet_first_wall hN F label (fun v hv => hpos v (hm v hv)) hcolors hw
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      simp only [Finset.mem_singleton]
      funext i
      have hi : i = 0 := by apply Fin.ext; have := i.isLt; simp
      subst i
      apply Fin.ext
      simpa [p] using hz v hv
    · simp [hcard]
  · intro heq; subst F; exact hmem

open Filter
open scoped Topology

/-- Concrete ordered lattice simplex mesh. Every cell lies in the simplex,
and its image has diameter at most 2/N. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem lattice_cell_mesh {n N : ℕ} (hN : 0 < N)
    (T : Finset (Fin (n+1) → Fin (N+1)))
    (hT : T ∈ boundedChainSimplices N (n+1) Monotone) :
    (∀ v ∈ T, (∀ i, 0 ≤ chainSimplex (chainPad v) N i) ∧
      ∑ i, chainSimplex (chainPad v) N i = 1) ∧
    (∀ v ∈ T, ∀ w ∈ T,
      dist (chainSimplex (chainPad v) N) (chainSimplex (chainPad w) N) ≤ 2 / (N : ℝ)) := by
  constructor
  · intro v hv
    exact lattice_chain_simplex v hN ((boundedChainSimplices_cube N (n+1) Monotone T hT).1 v hv)
  · intro v hv w hw
    exact lattice_simplex_dist v w hN (boundedChainSimplices_real_bound N (n+1) Monotone T hT v w hv hw)

/-- A simplex cover supported on positive coordinates yields a Sperner label
on every ordered lattice vertex. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem lattice_cover_label {n N : ℕ} (hN : 0 < N)
    (F : Fin (n+2) → Set (Fin (n+2) → ℝ))
    (hcover : ∀ x : Fin (n+2) → ℝ, (∀ i, 0 ≤ x i) → (∑ i, x i = 1) →
      ∃ i, 0 < x i ∧ x ∈ F i) :
    ∃ label : (Fin (n+1) → Fin (N+1)) → Fin (n+2),
      ∀ v, Monotone v →
        0 < chainSimplex (chainPad v) N (label v) ∧
        chainSimplex (chainPad v) N ∈ F (label v) := by
  classical
  have hex : ∀ v : Fin (n+1) → Fin (N+1), Monotone v →
      ∃ i, 0 < chainSimplex (chainPad v) N i ∧ chainSimplex (chainPad v) N ∈ F i := by
    intro v hv
    obtain ⟨hn,hs⟩ := lattice_chain_simplex v hN hv
    exact hcover _ hn hs
  let label : (Fin (n+1) → Fin (N+1)) → Fin (n+2) := fun v =>
    if hv : Monotone v then Classical.choose (hex v hv) else 0
  refine ⟨label, ?_⟩
  intro v hv
  simpa [label, hv] using Classical.choose_spec (hex v hv)

/-- A compact set has a common point of a finite family of closed sets whenever
there are arbitrarily small nonempty finite sets with a point in every member. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem compact_closed_finite_mesh {X : Type*} [MetricSpace X] {ι : Type*}
    (K : Set X) (hK : IsCompact K) (F : ι → Set X) (hF : ∀ i, IsClosed (F i))
    (ha : ∀ ε : ℝ, 0 < ε → ∃ T : Finset X, T.Nonempty ∧
      (∀ x ∈ T, x ∈ K) ∧ (∀ x ∈ T, ∀ y ∈ T, dist x y < ε) ∧
      (∀ i, ∃ y ∈ T, y ∈ F i)) :
    ∃ x ∈ K, ∀ i, x ∈ F i := by
  classical
  have hex : ∀ n : ℕ, ∃ x ∈ K, ∀ i, ∃ y ∈ F i,
      dist x y < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨T, ⟨x, hx⟩, hK', hd, hF'⟩ := ha (1 / ((n : ℝ) + 1)) (by positivity)
    refine ⟨x, hK' x hx, ?_⟩
    intro i
    obtain ⟨y, hy, hyF⟩ := hF' i
    exact ⟨y, hyF, hd x hx y hy⟩
  choose x hx hy using hex
  choose y hyF hyd using hy
  obtain ⟨z, hz, φ, hφ, hlim⟩ := hK.tendsto_subseq hx
  refine ⟨z, hz, fun i => ?_⟩
  have hylim : Tendsto (fun n : ℕ => y (φ n) i) atTop (𝓝 z) := by
    apply hlim.congr_dist
    apply squeeze_zero (fun n => dist_nonneg) (fun n => le_of_lt (hyd (φ n) i))
    exact tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  exact (hF i).mem_of_tendsto hylim (Filter.Eventually.of_forall fun n => hyF (φ n) i)

/-- Ordered-lattice Sperner, if supplied, yields the full closed KKM theorem
on a standard finite simplex. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem kkm_from_lattice_sperner (n : ℕ)
    (sperner : ∀ N : ℕ, 0 < N →
      ∀ label : (Fin (n+1) → Fin (N+1)) → Fin (n+2),
      (∀ v, Monotone v → 0 < chainSimplex (chainPad v) N (label v)) →
      ∃ T ∈ boundedChainSimplices N (n+1) Monotone,
        ∀ i, ∃ v ∈ T, label v = i)
    (F : Fin (n+2) → Set (Fin (n+2) → ℝ)) (hF : ∀ i, IsClosed (F i))
    (hcover : ∀ x : Fin (n+2) → ℝ, (∀ i, 0 ≤ x i) → (∑ i, x i = 1) →
      ∃ i, 0 < x i ∧ x ∈ F i) :
    ∃ x ∈ stdSimplex ℝ (Fin (n+2)), ∀ i, x ∈ F i := by
  classical
  apply compact_closed_finite_mesh (stdSimplex ℝ (Fin (n+2))) (isCompact_stdSimplex _) F hF
  intro ε hε
  obtain ⟨N,hN⟩ := exists_nat_gt (2 / ε)
  have hNposR : (0 : ℝ) < N := by
    have : 0 ≤ (2 : ℝ) / ε := by positivity
    linarith
  have hNpos : 0 < N := by exact_mod_cast hNposR
  have hmesh : (2 : ℝ) / N < ε := by
    apply (div_lt_iff₀ hNposR).2
    have h := (div_lt_iff₀ hε).1 hN
    nlinarith
  obtain ⟨label, hlabel⟩ := lattice_cover_label hNpos F hcover
  obtain ⟨T,hT,hcolors⟩ := sperner N hNpos label (fun v hv => (hlabel v hv).1)
  let p := fun v : Fin (n+1) → Fin (N+1) => chainSimplex (chainPad v) N
  let U := T.image p
  have hcells := lattice_cell_mesh hNpos T hT
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · obtain ⟨v,hv,_⟩ := hcolors 0
    exact ⟨p v, Finset.mem_image.mpr ⟨v,hv,rfl⟩⟩
  · intro x hx
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
    exact hcells.1 v hv
  · intro x hx y hy
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hy
    exact lt_of_le_of_lt (hcells.2 v hv w hw) hmesh
  · intro i
    obtain ⟨v,hv,hvi⟩ := hcolors i
    refine ⟨p v, Finset.mem_image.mpr ⟨v,hv,rfl⟩, ?_⟩
    have hmono := (boundedChainSimplices_cube N (n+1) Monotone T hT).1 v hv
    simpa [p, hvi] using (hlabel v hmono).2

/-- Closed KKM on a simplex implies its continuous-on fixed point theorem. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem stdSimplex_fixed_of_kkm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (kkm : ∀ (F : ι → Set (ι → ℝ)), (∀ i, IsClosed (F i)) →
      (∀ x : ι → ℝ, (∀ i, 0 ≤ x i) → (∑ i, x i = 1) →
        ∃ i, 0 < x i ∧ x ∈ F i) →
      ∃ x ∈ stdSimplex ℝ ι, ∀ i, x ∈ F i)
    (f : (ι → ℝ) → (ι → ℝ)) (hf : ContinuousOn f (stdSimplex ℝ ι))
    (hm : Set.MapsTo f (stdSimplex ℝ ι) (stdSimplex ℝ ι)) :
    ∃ x ∈ stdSimplex ℝ ι, f x = x := by
  let Δ := stdSimplex ℝ ι
  let F : ι → Set (ι → ℝ) := fun i => {x | x ∈ Δ ∧ f x i ≤ x i}
  have hc : ∀ i, IsClosed (F i) := by
    intro i
    exact (isClosed_stdSimplex ι).isClosed_le ((continuous_apply i).continuousOn.comp hf (Set.mapsTo_univ _ _)) (continuous_apply i).continuousOn
  have hcover : ∀ x : ι → ℝ, (∀ i, 0 ≤ x i) → (∑ i, x i = 1) →
      ∃ i, 0 < x i ∧ x ∈ F i := by
    intro x hn hs
    have hx : x ∈ Δ := ⟨hn,hs⟩
    by_contra h
    push_neg at h
    have hle : ∀ i, x i ≤ f x i := by
      intro i
      by_cases hi : 0 < x i
      · have hh := h i hi
        dsimp [F] at hh
        exact le_of_lt (not_le.mp (fun hle => hh ⟨hx, hle⟩))
      · have hx0 : x i = 0 := le_antisymm (le_of_not_gt hi) (hn i)
        rw [hx0]; exact (hm hx).1 i
    have heq : ∀ i, x i = f x i := by
      intro i
      have hs' : (∑ j, x j) = ∑ j, f x j := by rw [hs, (hm hx).2]
      exact (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun j _ => hle j)).mp hs' i (Finset.mem_univ i)
    have hex : ∃ i, 0 < x i := by
      by_contra hh
      push_neg at hh
      have hz : ∀ i, x i = 0 := fun i => le_antisymm (hh i) (hn i)
      simp only [hz, Finset.sum_const_zero] at hs
      norm_num at hs
    obtain ⟨i,hi⟩ := hex
    have hh := h i hi
    exact hh ⟨hx, (heq i).ge⟩
  obtain ⟨x,hx,hxF⟩ := kkm F hc hcover
  refine ⟨x,hx,funext ?_⟩
  intro i
  have hs : (∑ j, f x j) = ∑ j, x j := by rw [(hm hx).2, hx.2]
  exact (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun j _ => (hxF j).2)).mp hs i (Finset.mem_univ i)

/-- Relabeling a finite simplex preserves simplex membership. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem stdSimplex_relabel {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (x : ι → ℝ) :
    (Homeomorph.piCongrLeft (Y := fun _ : κ => ℝ) e) x ∈ stdSimplex ℝ κ ↔
      x ∈ stdSimplex ℝ ι := by
  constructor
  · intro hx
    constructor
    · intro i
      have h := hx.1 (e i)
      simpa [Homeomorph.piCongrLeft, Equiv.piCongrLeft] using h
    · have h := e.sum_comp ((Homeomorph.piCongrLeft (Y := fun _ : κ => ℝ) e) x)
      calc
        (∑ i, x i) = ∑ j, ((Homeomorph.piCongrLeft (Y := fun _ : κ => ℝ) e) x) j := by
          simpa [Homeomorph.piCongrLeft, Equiv.piCongrLeft] using h
        _ = 1 := hx.2
  · intro hx
    constructor
    · intro j
      have h := hx.1 (e.symm j)
      simpa [Homeomorph.piCongrLeft, Equiv.piCongrLeft] using h
    · have h := e.sum_comp ((Homeomorph.piCongrLeft (Y := fun _ : κ => ℝ) e) x)
      have hh : (∑ i, ((Homeomorph.piCongrLeft (Y := fun _ : κ => ℝ) e) x) (e i)) = 1 := by
        simpa [Homeomorph.piCongrLeft, Equiv.piCongrLeft] using hx.2
      linarith

/-- The simplex fixed-point property transfers along finite reindexing. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem stdSimplex_fixed_relabel {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ)
    (hB : ∀ g : (κ → ℝ) → (κ → ℝ),
      ContinuousOn g (stdSimplex ℝ κ) → Set.MapsTo g (stdSimplex ℝ κ) (stdSimplex ℝ κ) →
      ∃ x ∈ stdSimplex ℝ κ, g x = x)
    (f : (ι → ℝ) → (ι → ℝ)) (hf : ContinuousOn f (stdSimplex ℝ ι))
    (hm : Set.MapsTo f (stdSimplex ℝ ι) (stdSimplex ℝ ι)) :
    ∃ x ∈ stdSimplex ℝ ι, f x = x := by
  let H := Homeomorph.piCongrLeft (Y := fun _ : κ => ℝ) e
  have Hmap : Set.MapsTo H (stdSimplex ℝ ι) (stdSimplex ℝ κ) := by
    intro x hx; exact (stdSimplex_relabel e x).2 hx
  have Hinv : Set.MapsTo H.symm (stdSimplex ℝ κ) (stdSimplex ℝ ι) := by
    intro x hx
    apply (stdSimplex_relabel e (H.symm x)).1
    change H (H.symm x) ∈ stdSimplex ℝ κ
    simpa using hx
  let g := H ∘ f ∘ H.symm
  have hgc : ContinuousOn g (stdSimplex ℝ κ) :=
    H.continuous.continuousOn.comp (hf.comp H.symm.continuous.continuousOn Hinv)
      (hm.comp Hinv)
  have hgm : Set.MapsTo g (stdSimplex ℝ κ) (stdSimplex ℝ κ) := Hmap.comp (hm.comp Hinv)
  obtain ⟨x,hx,hfix⟩ := hB g hgc hgm
  refine ⟨H.symm x,Hinv hx,?_⟩
  apply H.injective
  simpa [g, Function.comp_def] using hfix

/-- Any self-map of the one-point simplex has a fixed point. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem stdSimplex_fin_one_fixed (f : (Fin 1 → ℝ) → (Fin 1 → ℝ))
    (hm : Set.MapsTo f (stdSimplex ℝ (Fin 1)) (stdSimplex ℝ (Fin 1))) :
    ∃ x ∈ stdSimplex ℝ (Fin 1), f x = x := by
  let x : Fin 1 → ℝ := fun _ => 1
  have hx : x ∈ stdSimplex ℝ (Fin 1) := by simp [stdSimplex, x, Fin.sum_univ_one]
  refine ⟨x, hx, ?_⟩
  have hf := (hm hx).2
  rw [Fin.sum_univ_one] at hf
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  exact hf

/-- Ordered lattice Sperner in all positive dimensions implies every nonempty
finite simplex has the continuous-on fixed point property. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem finite_simplex_fixed_of_lattice_sperner
    (sperner : ∀ n N : ℕ, 0 < N →
      ∀ label : (Fin (n+1) → Fin (N+1)) → Fin (n+2),
      (∀ v, Monotone v → 0 < chainSimplex (chainPad v) N (label v)) →
      ∃ T ∈ boundedChainSimplices N (n+1) Monotone,
        ∀ i, ∃ v ∈ T, label v = i)
    (ι : Type*) [Fintype ι] [Nonempty ι]
    (f : (ι → ℝ) → (ι → ℝ)) (hf : ContinuousOn f (stdSimplex ℝ ι))
    (hm : Set.MapsTo f (stdSimplex ℝ ι) (stdSimplex ℝ ι)) :
    ∃ x ∈ stdSimplex ℝ ι, f x = x := by
  let m := Fintype.card ι
  have hmpos : 0 < m := Fintype.card_pos
  have hfin : ∀ g : (Fin m → ℝ) → (Fin m → ℝ),
      ContinuousOn g (stdSimplex ℝ (Fin m)) →
      Set.MapsTo g (stdSimplex ℝ (Fin m)) (stdSimplex ℝ (Fin m)) →
      ∃ x ∈ stdSimplex ℝ (Fin m), g x = x := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmpos)
    rw [hk]
    cases k with
    | zero => intro g hg hgm; exact stdSimplex_fin_one_fixed g hgm
    | succ n =>
      intro g hg hgm
      apply stdSimplex_fixed_of_kkm (kkm_from_lattice_sperner n (sperner n)) g hg hgm
  exact stdSimplex_fixed_relabel (Fintype.equivFin ι) hfin f hf hm

open Set Metric
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- Auxiliary simplex reduction result for the lattice construction.
The proof uses the preceding finite, order, and continuity lemmas as applicable. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem simplex_reduction
    (hB : ∀ (ι : Type u) [Fintype ι] [Nonempty ι] (g : (ι → ℝ) → (ι → ℝ)),
      let Δ : Set (ι → ℝ) := {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}
      ContinuousOn g Δ → MapsTo g Δ Δ → ∃ w ∈ Δ, g w = w)
    {s : Set E} (hne : s.Nonempty) (hc : IsCompact s) (hv : Convex ℝ s)
    {f : E → E} (hf : ContinuousOn f s) (hm : MapsTo f s s) :
    ∃ x ∈ s, f x = x := by
  classical
  have ha : ∀ ε : ℝ, 0 < ε → ∃ x ∈ s, dist (f x) x < ε := by
    intro ε hε
    obtain ⟨t, hts, htf, hcover⟩ := hc.finite_cover_balls (half_pos hε)
    letI : Fintype t := htf.fintype
    have htne : t.Nonempty := by
      obtain ⟨x, hx⟩ := hne
      obtain ⟨y, hy, _⟩ := mem_iUnion₂.mp (hcover hx)
      exact ⟨y, hy⟩
    letI : Nonempty t := htne.to_subtype
    let U : t → Set E := fun i => ball (i : E) (ε / 2)
    have hu : s ⊆ ⋃ i : t, U i := by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover hx)
      exact mem_iUnion.mpr ⟨⟨y, hy⟩, hxy⟩
    obtain ⟨p, hp⟩ := PartitionOfUnity.exists_isSubordinate_of_locallyFinite
      hc.isClosed U (fun _ => isOpen_ball) (locallyFinite_of_finite _) hu
    let Δ : Set (t → ℝ) := {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}
    let a : (t → ℝ) → E := fun w => ∑ i : t, w i • (i : E)
    have hac : Continuous a := continuous_finset_sum _ (fun i _ => (continuous_apply i).smul continuous_const)
    have ham : MapsTo a Δ s := by
      intro w hw
      apply hv.sum_mem
      · intro i _; exact hw.1 i
      · exact hw.2
      · intro i _; exact hts i.property
    let g : (t → ℝ) → (t → ℝ) := fun w i => p i (f (a w))
    have hgc : ContinuousOn g Δ := by
      apply continuousOn_pi.mpr
      intro i
      exact (p i).continuous.continuousOn.comp (hf.comp hac.continuousOn ham) (mapsTo_univ _ _)
    have hgm : MapsTo g Δ Δ := by
      intro w hw
      constructor
      · intro i; exact p.nonneg i _
      · simpa only [g, finsum_eq_sum_of_fintype] using p.sum_eq_one (hm (ham hw))
    obtain ⟨w, hw, hfix⟩ := hB t g hgc hgm
    refine ⟨a w, ham hw, ?_⟩
    have hpw : ∀ i, p i (f (a w)) = w i := by
      intro i
      exact congrFun hfix i
    have hw' : (∑ i : t, p i (f (a w))) = 1 := by
      simpa only [finsum_eq_sum_of_fintype] using p.sum_eq_one (hm (ham hw))
    have hmem : (∑ i : t, p i (f (a w)) •
        (if p i (f (a w)) = 0 then f (a w) else (i : E))) ∈ closedBall (f (a w)) (ε / 2) := by
      apply (convex_closedBall _ _).sum_mem
      · intro i hi; exact p.nonneg i _
      · exact hw'
      · intro i hi
        split_ifs with h
        · exact mem_closedBall_self (half_pos hε).le
        · have hh : f (a w) ∈ U i := hp i (subset_closure h)
          exact mem_closedBall.mpr (le_of_lt (by simpa [U, dist_comm] using hh))
    have heq : (∑ i : t, p i (f (a w)) •
        (if p i (f (a w)) = 0 then f (a w) else (i : E))) = a w := by
      dsimp [a]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← hpw i]
      split_ifs with h
      · change p i (f (a w)) = 0 at h; simp only [a] at h ⊢; simp [h]
      · rfl
    rw [heq, mem_closedBall] at hmem
    exact lt_of_le_of_lt (by simpa [dist_comm] using hmem) (half_lt_self hε)
  obtain ⟨x, hx, hmin⟩ := hc.exists_isMinOn hne (continuous_dist.continuousOn.comp (hf.prodMk continuousOn_id) (mapsTo_univ _ _))
  have hz : dist (f x) x = 0 := by
    by_contra h
    have hp : 0 < dist (f x) x := lt_of_le_of_ne dist_nonneg (Ne.symm h)
    obtain ⟨y, hy, hy'⟩ := ha _ hp
    exact (not_lt_of_ge (hmin hy)) hy'
  exact ⟨x, hx, dist_eq_zero.mp hz⟩

/-- Schauder's theorem reduced to the concrete ordered-lattice Sperner lemma. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem schauder_of_lattice_sperner
    (sperner : ∀ n N : ℕ, 0 < N →
      ∀ label : (Fin (n+1) → Fin (N+1)) → Fin (n+2),
      (∀ v, Monotone v → 0 < chainSimplex (chainPad v) N (label v)) →
      ∃ T ∈ boundedChainSimplices N (n+1) Monotone,
        ∀ i, ∃ v ∈ T, label v = i)
    {s : Set E} (hne : s.Nonempty) (hc : IsCompact s) (hv : Convex ℝ s)
    {f : E → E} (hf : ContinuousOn f s) (hm : Set.MapsTo f s s) :
    ∃ x ∈ s, f x = x := by
  apply simplex_reduction ?_ hne hc hv hf hm
  intro ι _ _ g
  dsimp only
  intro hg hgm
  exact finite_simplex_fixed_of_lattice_sperner sperner ι g hg hgm

 /-- Auxiliary even card of fixed point free involution result for the lattice construction.
 The proof uses the preceding finite, order, and continuity lemmas as applicable. -/
 @[blueprint "SchauderFixedPointTheorem.MainTheorem"]
 theorem even_card_of_fixed_point_free_involution {α : Type*} [Fintype α]
    (f : α → α) (hf : Function.Involutive f) (hne : ∀ x, f x ≠ x) :
    Even (Fintype.card α) := by
  classical
  let e : Equiv.Perm α := ⟨f, f, hf, hf⟩
  have htwo : e ^ 2 = 1 := by
    ext x
    simpa [e, pow_two, Equiv.Perm.mul_apply] using hf x
  have hs : e.support = Finset.univ := by
    ext x
    simp [e, hne x]
  have h := Equiv.Perm.two_dvd_card_support htwo
  rw [hs, Finset.card_univ] at h
  exact even_iff_two_dvd.mpr h

 /-- Auxiliary Eligible result for the lattice construction.
 The proof uses the preceding finite, order, and continuity lemmas as applicable. -/
 @[blueprint "SchauderFixedPointTheorem.MainTheorem"]
 def Eligible {V I : Type*} (lab : V → I) (t : I) (v : V) : Prop :=
  (∀ w, w ≠ v → lab w ≠ t) ∧ ∀ i, i ≠ t → ∃! w, w ≠ v ∧ lab w = i

 /-- Auxiliary eligible odd full result for the lattice construction.
 The proof uses the preceding finite, order, and continuity lemmas as applicable. -/
 @[blueprint "SchauderFixedPointTheorem.MainTheorem"]
 theorem eligible_odd_full {V I : Type*} [Fintype V] (lab : V → I) (t : I)
    [DecidablePred (Eligible lab t)]
    (hodd : Odd (Fintype.card {v // Eligible lab t v})) :
    Function.Surjective lab := by
  classical
  by_contra hn
  have hnot : ∀ v, lab v ≠ t := by
    intro v hv
    have hd : Nonempty {v // Eligible lab t v} := by
      apply Fintype.card_pos_iff.mp
      obtain ⟨k, hk⟩ := hodd
      omega
    obtain ⟨⟨x, hx⟩⟩ := hd
    have hvx : v = x := by
      by_contra h; exact hx.1 v h hv
    apply hn
    intro i
    by_cases hi : i = t
    · exact ⟨v, hv.trans hi.symm⟩
    · obtain ⟨w, hw, _⟩ := hx.2 i hi
      exact ⟨w, hw.2⟩
  let twin : {v // Eligible lab t v} → {v // Eligible lab t v} := fun x => by
    let y := Classical.choose (x.2.2 (lab x.1) (hnot x.1))
    have hy := (Classical.choose_spec (x.2.2 (lab x.1) (hnot x.1))).1
    have hyuniq := (Classical.choose_spec (x.2.2 (lab x.1) (hnot x.1))).2
    refine ⟨y, ?_⟩
    constructor
    · intro w hw
      exact hnot w
    · intro i hi
      by_cases hix : i = lab x.1
      · refine ⟨x.1, ⟨Ne.symm hy.1, hix.symm⟩, ?_⟩
        intro z hz
        by_cases hzx : z = x.1
        · exact hzx
        · have : z = y := hyuniq z ⟨hzx, hz.2.trans hix⟩
          exact False.elim (hz.1 this)
      · obtain ⟨z, hz, hzuniq⟩ := x.2.2 i hi
        have hzy : z ≠ y := by
          intro h; subst z; exact hix (hz.2.symm.trans hy.2)
        refine ⟨z, ⟨hzy, hz.2⟩, ?_⟩
        intro w hw
        have hwx : w ≠ x.1 := by
          intro h; subst w; exact hix hw.2.symm
        exact hzuniq w ⟨hwx, hw.2⟩
  have htwin : ∀ x, twin x ≠ x ∧ lab (twin x).1 = lab x.1 := by
    intro x
    have hy := (Classical.choose_spec (x.2.2 (lab x.1) (hnot x.1))).1
    constructor
    · intro h
      exact hy.1 (congrArg Subtype.val h)
    · exact hy.2
  have hinv : Function.Involutive twin := by
    intro x
    apply Subtype.ext
    have hx := (twin x).2.2 (lab x.1) (hnot x.1)
    obtain ⟨y, hy, hu⟩ := hx
    have h1 : x.1 = y := hu x.1 ⟨fun h => (htwin x).1 (Subtype.ext h.symm), rfl⟩
    have h2 : (twin (twin x)).1 = y := hu _ ⟨fun h => (htwin (twin x)).1 (Subtype.ext h), (htwin (twin x)).2.trans (htwin x).2⟩
    exact h2.trans h1.symm
  have heven := even_card_of_fixed_point_free_involution twin hinv (fun x => (htwin x).1)
  exact (Nat.not_even_iff_odd.mpr hodd) heven

/-- The incidence form of the local Sperner parity step. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem full_of_odd_deletion_incidence {V I B : Type*} [Fintype V] [Fintype B]
    (lab : V → I) (t : I) (R : B → Prop) [DecidablePred R]
    [DecidablePred (Eligible lab t)]
    (faceEquiv : {b // R b} ≃ {v // Eligible lab t v})
    (hodd : Odd ((Finset.univ.filter R).card)) : Function.Surjective lab := by
  apply eligible_odd_full lab t
  have hcard : (Finset.univ.filter R).card = Fintype.card {v // Eligible lab t v} := by
    rw [← Fintype.card_congr faceEquiv]
    exact (Fintype.card_subtype R).symm
  rwa [← hcard]

/-- A full labeling of equally many vertices and colors has exactly one
eligible deletion (the vertex of the omitted color). -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem eligible_card_one_of_surjective {V I : Type*} [Fintype V] [Fintype I]
    (lab : V → I) (t : I) [DecidablePred (Eligible lab t)]
    (hcard : Fintype.card V = Fintype.card I)
    (hsurj : Function.Surjective lab) :
    Fintype.card {v // Eligible lab t v} = 1 := by
  classical
  have hinj : Function.Injective lab := ((Fintype.bijective_iff_surjective_and_card lab).mpr ⟨hsurj, hcard⟩).1
  obtain ⟨v,hv⟩ := hsurj t
  have hel : Eligible lab t v := by
    constructor
    · intro w hw hwt
      exact hw (hinj (hwt.trans hv.symm))
    · intro i hi
      obtain ⟨w, hw⟩ := hsurj i
      refine ⟨w, ⟨?_, hw⟩, ?_⟩
      · intro h; subst w; exact hi (hw.symm.trans hv)
      · intro z hz; exact hinj (hz.2.trans hw.symm)
  have huniq : ∀ x : {v // Eligible lab t v}, x = ⟨v,hel⟩ := by
    intro ⟨x,hx⟩
    apply Subtype.ext
    by_contra h
    exact hx.1 v (Ne.symm h) hv
  exact Fintype.card_eq_one_iff.mpr ⟨⟨v,hel⟩, huniq⟩

/-- Under equal cardinality, odd eligible deletion count is equivalent to a
fully labelled simplex. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem eligible_odd_iff_full {V I : Type*} [Fintype V] [Fintype I]
    (lab : V → I) (t : I) [DecidablePred (Eligible lab t)]
    (hcard : Fintype.card V = Fintype.card I) :
    Odd (Fintype.card {v // Eligible lab t v}) ↔ Function.Surjective lab := by
  classical
  constructor
  · exact eligible_odd_full lab t
  · intro h
    rw [eligible_card_one_of_surjective lab t hcard h]
    decide

/-- A set of n vertices covering n permitted colors has exactly one vertex of
 each permitted color and no forbidden color. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem finite_cover_except_one_unique {V I : Type*} [Fintype V] [Fintype I]
    (lab : V → I) (t : I) (hcard : Fintype.card V + 1 = Fintype.card I)
    (hcover : ∀ i, i ≠ t → ∃ v, lab v = i) :
    (∀ v, lab v ≠ t) ∧ ∀ i, i ≠ t → ∃! v, lab v = i := by
  classical
  have hnot : ∀ v, lab v ≠ t := by
    intro v hv
    have hs : Function.Surjective lab := by
      intro i
      by_cases hi : i = t
      · exact ⟨v, hv.trans hi.symm⟩
      · exact hcover i hi
    have hle := Fintype.card_le_of_surjective lab hs
    omega
  let f : V → {i : I // i ≠ t} := fun v => ⟨lab v, hnot v⟩
  have hs : Function.Surjective f := by
    intro ⟨i,hi⟩
    obtain ⟨v,hv⟩ := hcover i hi
    exact ⟨v, Subtype.ext hv⟩
  have htarget : Fintype.card {i : I // i ≠ t} = Fintype.card I - 1 := by
    have h := Fintype.card_subtype_compl (fun i : I => i = t)
    have heq : Fintype.card {i : I // i = t} = 1 := by
      apply Fintype.card_eq_one_iff.mpr
      exact ⟨⟨t,rfl⟩, fun i => Subtype.ext i.2⟩
    simpa only [heq] using h
  have hfcard : Fintype.card V = Fintype.card {i : I // i ≠ t} := by rw [htarget]; omega
  have hinj : Function.Injective f := ((Fintype.bijective_iff_surjective_and_card f).mpr ⟨hs,hfcard⟩).1
  refine ⟨hnot, ?_⟩
  intro i hi
  obtain ⟨v,hv⟩ := hcover i hi
  refine ⟨v,hv,?_⟩
  intro w hw
  apply hinj
  exact Subtype.ext (hw.trans hv.symm)

/-- Coverage by all colors other than the omitted one is exactly eligibility
of a deleted vertex when the simplex has one vertex per color. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem deletion_coverage_iff_eligible {V I : Type*} [Fintype V] [Fintype I]
    (lab : V → I) (t : I) (hcard : Fintype.card V = Fintype.card I) (v : V) :
    (∀ i, i ≠ t → ∃ w, w ≠ v ∧ lab w = i) ↔ Eligible lab t v := by
  classical
  constructor
  · intro h
    have hc : Fintype.card {w : V // w ≠ v} + 1 = Fintype.card I := by
      have ht := Fintype.card_subtype_compl (fun w : V => w = v)
      have hs : Fintype.card {w : V // w = v} = 1 := by
        apply Fintype.card_eq_one_iff.mpr
        exact ⟨⟨v,rfl⟩, fun x => Subtype.ext x.2⟩
      have hv : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
      rw [hs] at ht
      change Fintype.card {w : V // w ≠ v} = Fintype.card V - 1 at ht
      omega
    have hh : ∀ i, i ≠ t → ∃ w : {w : V // w ≠ v}, lab w = i := by
      intro i hi
      obtain ⟨w, hw, he⟩ := h i hi
      exact ⟨⟨w,hw⟩,he⟩
    obtain ⟨hn,hu⟩ := finite_cover_except_one_unique (fun w : {w : V // w ≠ v} => lab w) t hc hh
    constructor
    · intro w hw; exact hn ⟨w,hw⟩
    · intro i hi
      obtain ⟨w, hw, huniq⟩ := hu i hi
      refine ⟨w.1, ⟨w.2, hw⟩, ?_⟩
      intro z hz
      exact congrArg Subtype.val (huniq ⟨z,hz.1⟩ hz.2)
  · intro h i hi
    obtain ⟨w,hw,_⟩ := h.2 i hi
    exact ⟨w,hw⟩

/-- Codimension-one subsets of a finite set correspond to their deleted vertex. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
noncomputable def facetDeletionEquiv {V : Type*} [DecidableEq V] (T : Finset V) :
    {v // v ∈ T} ≃ {F : Finset V // F ⊆ T ∧ F.card + 1 = T.card} := by
  classical
  let f : {v // v ∈ T} → {F : Finset V // F ⊆ T ∧ F.card + 1 = T.card} :=
    fun v => ⟨T.erase v.1, Finset.erase_subset _ _, Finset.card_erase_add_one v.2⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b hab
    apply Subtype.ext
    by_contra hne
    have hm : a.1 ∈ T.erase b.1 := Finset.mem_erase.mpr ⟨hne, a.2⟩
    have he := congrArg Subtype.val hab
    change T.erase a.1 = T.erase b.1 at he
    rw [← he] at hm
    exact (Finset.notMem_erase _ _) hm
  · intro ⟨F,hsub,hcard⟩
    have hd : (T \ F).card = 1 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
      omega
    obtain ⟨v,hv⟩ := Finset.card_eq_one.mp hd
    have hvm : v ∈ T \ F := hv ▸ Finset.mem_singleton_self v
    have hvT := (Finset.mem_sdiff.mp hvm).1
    have hvF := (Finset.mem_sdiff.mp hvm).2
    refine ⟨⟨v,hvT⟩, ?_⟩
    apply Subtype.ext
    change T.erase v = F
    ext w
    simp only [Finset.mem_erase]
    constructor
    · intro ⟨hwv, hwT⟩
      by_contra hwF
      have : w ∈ T \ F := Finset.mem_sdiff.mpr ⟨hwT,hwF⟩
      rw [hv, Finset.mem_singleton] at this
      exact hwv this
    · intro hwF
      exact ⟨fun he => hvF (he ▸ hwF), hsub hwF⟩

/-- The facets carrying every non-omitted color correspond to eligible
vertex deletions of a simplex. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
noncomputable def selectedFacetEquiv {V I : Type*} [Fintype V] [Fintype I]
    (T : Finset V) (lab : V → I) (t : I) (hcard : T.card = Fintype.card I) :
    {v : {v // v ∈ T} // Eligible (fun w => lab w.1) t v} ≃
    {F : {F : Finset V // F ⊆ T ∧ F.card + 1 = T.card} //
      ∀ i, i ≠ t → ∃ w ∈ F.1, lab w = i} := by
  classical
  apply Equiv.subtypeEquiv (facetDeletionEquiv T)
  intro v
  have hc : Fintype.card {v // v ∈ T} = Fintype.card I := by
    rw [Fintype.card_coe, hcard]
  rw [← deletion_coverage_iff_eligible (fun w : {v // v ∈ T} => lab w.1) t hc v]
  change (∀ i, i ≠ t → ∃ w : {v // v ∈ T}, w ≠ v ∧ lab w.1 = i) ↔
    (∀ i, i ≠ t → ∃ w ∈ T.erase v.1, lab w = i)
  constructor
  · intro h i hi
    obtain ⟨w,hw,he⟩ := h i hi
    exact ⟨w.1, Finset.mem_erase.mpr ⟨fun heq => hw (Subtype.ext heq), w.2⟩, he⟩
  · intro h i hi
    obtain ⟨w,hw,he⟩ := h i hi
    obtain ⟨hwv,hwT⟩ := Finset.mem_erase.mp hw
    exact ⟨⟨w,hwT⟩, fun h => hwv (congrArg Subtype.val h), he⟩


/-- The selected facets of a simplex have odd count iff it is fully labeled. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem selected_facets_odd_iff_full {V I : Type*} [Fintype V] [Fintype I]
    (T : Finset V) (lab : V → I) (t : I) (hcard : T.card = Fintype.card I) : by
    classical
    exact Odd (Fintype.card {F : {F : Finset V // F ⊆ T ∧ F.card + 1 = T.card} //
      ∀ i, i ≠ t → ∃ w ∈ F.1, lab w = i}) ↔ (∀ i, ∃ v ∈ T, lab v = i) := by
  classical
  have hc : Fintype.card {v // v ∈ T} = Fintype.card I := by
    rw [Fintype.card_coe, hcard]
  have he : Fintype.card {F : {F : Finset V // F ⊆ T ∧ F.card + 1 = T.card} //
      ∀ i, i ≠ t → ∃ w ∈ F.1, lab w = i} =
      Fintype.card {v : {v // v ∈ T} // Eligible (fun w => lab w.1) t v} :=
    (Fintype.card_congr (selectedFacetEquiv T lab t hcard)).symm
  rw [he, eligible_odd_iff_full _ t hc]
  constructor
  · intro h i
    obtain ⟨v,hv⟩ := h i
    exact ⟨v.1,v.2,hv⟩
  · intro h i
    obtain ⟨v,hv,hi⟩ := h i
    exact ⟨⟨v,hv⟩,hi⟩

/-- Finset-filter form of local selected-facet parity. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem selected_facet_filter_odd_iff_full {V I : Type*} [Fintype V] [Fintype I]
    (T : Finset V) (lab : V → I) (t : I) (hcard : T.card = Fintype.card I) : by
    classical
    exact Odd ((Finset.univ.filter (fun F : Finset V =>
      (F ⊆ T ∧ F.card + 1 = T.card) ∧ ∀ i, i ≠ t → ∃ w ∈ F, lab w = i)).card) ↔
      (∀ i, ∃ v ∈ T, lab v = i) := by
  classical
  let p : Finset V → Prop := fun F => F ⊆ T ∧ F.card + 1 = T.card
  let q : Finset V → Prop := fun F => ∀ i, i ≠ t → ∃ w ∈ F, lab w = i
  have he : Fintype.card {F : {F : Finset V // p F} // q F.1} =
      ((Finset.univ : Finset (Finset V)).filter (fun F => p F ∧ q F)).card := by
    rw [Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter p q)]
    exact Fintype.card_subtype _
  have h := selected_facets_odd_iff_full T lab t hcard
  change Odd (Fintype.card {F : {F : Finset V // p F} // q F.1}) ↔ _ at h
  change Odd (((Finset.univ : Finset (Finset V)).filter (fun F => p F ∧ q F)).card) ↔ _
  rwa [← he]
open Finset
open scoped BigOperators

/-- Auxiliary incidence odd parity result for the lattice construction.
The proof uses the preceding finite, order, and continuity lemmas as applicable. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem incidence_odd_parity {A B : Type*} [Fintype A] [Fintype B]
    (R : A → B → Prop) [DecidableRel R] :
    Odd ((univ.filter fun a => Odd ((univ.filter fun b => R a b).card)).card) ↔
    Odd ((univ.filter fun b => Odd ((univ.filter fun a => R a b).card)).card) := by
  rw [← Finset.odd_sum_iff_odd_card_odd, ← Finset.odd_sum_iff_odd_card_odd]
  simp only [card_eq_sum_ones, sum_filter]
  rw [sum_comm]


/-- Counting selected facet-simplex incidences transfers parity from selected
odd-incidence facets to fully labelled simplices. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem finite_sperner_parity {V I : Type*} [Fintype V] [Fintype I]
    (K : Finset (Finset V)) (lab : V → I) (t : I)
    (hcard : ∀ T ∈ K, T.card = Fintype.card I) : by
    classical
    exact Odd ((K.filter (fun T => ∀ i, ∃ v ∈ T, lab v = i)).card) ↔
      Odd (((Finset.univ : Finset (Finset V)).filter (fun F =>
        (∀ i, i ≠ t → ∃ v ∈ F, lab v = i) ∧
        Odd ((K.filter (fun T => F ⊆ T ∧ F.card + 1 = T.card)).card))).card) := by
  classical
  let R : Finset V → Finset V → Prop := fun T F =>
    T ∈ K ∧ (F ⊆ T ∧ F.card + 1 = T.card) ∧ (∀ i, i ≠ t → ∃ v ∈ F, lab v = i)
  have hr : (Finset.univ.filter (fun T => Odd ((Finset.univ.filter (fun F => R T F)).card))) =
      K.filter (fun T => ∀ i, ∃ v ∈ T, lab v = i) := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases ht : T ∈ K
    · have he : (Finset.univ.filter (fun F => R T F)) =
        (Finset.univ.filter (fun F : Finset V =>
          (F ⊆ T ∧ F.card + 1 = T.card) ∧ ∀ i, i ≠ t → ∃ v ∈ F, lab v = i)) := by
        ext F; simp [R, ht]
      rw [he, selected_facet_filter_odd_iff_full T lab t (hcard T ht)]
      simp [ht]
    · have he : (Finset.univ.filter (fun F => R T F)) = ∅ := by ext F; simp [R, ht]
      simp [ht, he]
  have hc : (Finset.univ.filter (fun F => Odd ((Finset.univ.filter (fun T => R T F)).card))) =
      (Finset.univ.filter (fun F => (∀ i, i ≠ t → ∃ v ∈ F, lab v = i) ∧
        Odd ((K.filter (fun T => F ⊆ T ∧ F.card + 1 = T.card)).card))) := by
    ext F
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hl : ∀ i, i ≠ t → ∃ v ∈ F, lab v = i
    · have he : (Finset.univ.filter (fun T => R T F)) =
          K.filter (fun T => F ⊆ T ∧ F.card + 1 = T.card) := by
        ext T
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, R]
        exact ⟨fun h => ⟨h.1,h.2.1⟩, fun h => ⟨h.1,h.2,hl⟩⟩
      rw [he]
      exact ⟨fun h => ⟨hl,h⟩, And.right⟩
    · have he : (Finset.univ.filter (fun T => R T F)) = ∅ := by
        ext T
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, R]
        exact fun h => hl h.2.2
      rw [he]
      simp only [Finset.card_empty, Nat.not_odd_zero, false_iff]
      exact fun h => hl h.1
  have h := incidence_odd_parity R
  rwa [hr, hc] at h

/-- If all facet incidences are one or two, odd incidence is exactly a
cardinality-d facet with one incidence. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem odd_facet_incidence_filter {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V]
    (K : Finset (Finset V)) (d : ℕ) (lab : V → I) (t : I)
    (hcard : ∀ T ∈ K, T.card = d+1)
    (hbound : ∀ T ∈ K, ∀ F, F ⊆ T → F.card = d →
      ((K.filter (fun U => F ⊆ U)).card ≤ 2)) : by
    classical
    exact (Finset.univ.filter (fun F : Finset V =>
      (∀ i, i ≠ t → ∃ v ∈ F, lab v = i) ∧
      Odd ((K.filter (fun T => F ⊆ T ∧ F.card+1 = T.card)).card))) =
      (Finset.univ.filter (fun F : Finset V => F.card = d ∧
      (K.filter (fun T => F ⊆ T)).card = 1 ∧
      ∀ i, i ≠ t → ∃ v ∈ F, lab v = i)) := by
  classical
  ext F
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hlabel,hodd⟩
    have hp : 0 < (K.filter (fun T => F ⊆ T ∧ F.card+1 = T.card)).card := by
      obtain ⟨k,hk⟩ := hodd; omega
    obtain ⟨T,hT⟩ := Finset.card_pos.mp hp
    obtain ⟨hT,hFT,hFc⟩ := Finset.mem_filter.mp hT
    have hfd : F.card = d := by have := hcard T hT; omega
    have he : K.filter (fun T => F ⊆ T ∧ F.card+1 = T.card) =
        K.filter (fun T => F ⊆ T) := by
      ext U; simp only [Finset.mem_filter]
      constructor
      · exact fun h => ⟨h.1,h.2.1⟩
      · intro h; exact ⟨h.1,h.2,by rw [hfd,hcard U h.1]⟩
    rw [he] at hodd
    have hb := hbound T hT F hFT hfd
    have hone : (K.filter (fun T => F ⊆ T)).card = 1 := by
      obtain ⟨k,hk⟩ := hodd; omega
    exact ⟨hfd,hone,hlabel⟩
  · rintro ⟨hfd,hone,hlabel⟩
    have he : K.filter (fun T => F ⊆ T ∧ F.card+1 = T.card) =
        K.filter (fun T => F ⊆ T) := by
      ext U; simp only [Finset.mem_filter]
      constructor
      · exact fun h => ⟨h.1,h.2.1⟩
      · intro h; exact ⟨h.1,h.2,by rw [hfd,hcard U h.1]⟩
    refine ⟨hlabel, ?_⟩
    rw [he, hone]
    decide

/-- Finite Sperner parity with incidence-one boundary. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem finite_sperner_boundary {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V]
    (K : Finset (Finset V)) (d : ℕ) (lab : V → I) (t : I)
    (hcard : ∀ T ∈ K, T.card = d+1)
    (hcolors : Fintype.card I = d+1)
    (hbound : ∀ T ∈ K, ∀ F, F ⊆ T → F.card = d →
      ((K.filter (fun U => F ⊆ U)).card ≤ 2)) : by
    classical
    exact Odd ((K.filter (fun T => ∀ i, ∃ v ∈ T, lab v = i)).card) ↔
      Odd ((Finset.univ.filter (fun F : Finset V => F.card = d ∧
      (K.filter (fun T => F ⊆ T)).card = 1 ∧
      ∀ i, i ≠ t → ∃ v ∈ F, lab v = i)).card) := by
  classical
  have hp := finite_sperner_parity K lab t (by intro T hT; rw [hcolors]; exact hcard T hT)
  have hf := odd_facet_incidence_filter K d lab t hcard hbound
  have hh (F : Finset V) :
      ((∀ i, i ≠ t → ∃ v ∈ F, lab v = i) ∧
        Odd ((K.filter (fun T => F ⊆ T ∧ F.card+1 = T.card)).card)) ↔
      (F.card = d ∧ (K.filter (fun T => F ⊆ T)).card = 1 ∧
        ∀ i, i ≠ t → ∃ v ∈ F, lab v = i) := by
    have h := congrArg (fun X : Finset (Finset V) => F ∈ X) hf
    apply iff_of_eq
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using h
  convert hp using 1
  constructor <;> intro ho
  · convert ho using 1
    congr 1
    ext F
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    convert hh F using 1 <;> constructor <;> rintro ⟨hl, ho⟩ <;> refine ⟨hl, ?_⟩ <;> convert ho using 1 <;> congr 1 <;> ext T <;> simp
  · convert ho using 1
    congr 1
    ext F
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    convert (hh F).symm using 1 <;> constructor <;> rintro ⟨hl, ho⟩ <;> refine ⟨hl, ?_⟩ <;> convert ho using 1 <;> congr 1 <;> ext T <;> simp

/-- In each chamber, full cells and selected boundary facets have equal parity. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem lattice_sperner_parity (n N : ℕ)
    (label : (Fin (n+1) → Fin (N+1)) → Fin (n+2)) : by
    classical
    exact Odd (((boundedChainSimplices N (n+1) Monotone).filter
      (fun T => ∀ i, ∃ v ∈ T, label v = i)).card) ↔
    Odd (((Finset.univ : Finset (Finset (Fin (n+1) → Fin (N+1)))).filter
      (fun F => F.card = n+1 ∧
        ((boundedChainSimplices N (n+1) Monotone).filter (fun T => F ⊆ T)).card = 1 ∧
        ∀ i : Fin (n+2), i ≠ 0 → ∃ v ∈ F, label v = i)).card) := by
  classical
  have hc : ∀ T ∈ boundedChainSimplices N (n+1) (Monotone : (Fin (n+1) → Fin (N+1)) → Prop), T.card = n+1+1 := by
    intro T hT; exact boundedChainSimplices_card N (n+1) Monotone T hT
  have hb : ∀ T ∈ boundedChainSimplices N (n+1) (Monotone : (Fin (n+1) → Fin (N+1)) → Prop), ∀ F, F ⊆ T → F.card = n+1 →
      (((boundedChainSimplices N (n+1) Monotone).filter (fun U => F ⊆ U)).card ≤ 2) := by
    intro T hT F hFT hF
    simpa using (actual_facet_incidence_bounds N Monotone T F (by simp) (by simpa using hT) hFT (by simpa using hF)).2
  have hp := finite_sperner_boundary (boundedChainSimplices N (n+1) Monotone) (n+1) label 0 hc (by simp) hb
  convert hp using 1 <;> constructor <;> intro ho <;> convert ho using 1 <;> congr 1 <;> ext F <;> simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- The number of fully labeled chamber simplices is odd in every dimension. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem lattice_sperner_odd (n N : ℕ) (hN : 0 < N)
    (label : (Fin (n+1) → Fin (N+1)) → Fin (n+2))
    (hpos : ∀ v, Monotone v → 0 < chainSimplex (chainPad v) N (label v)) : by
    classical
    exact Odd (((boundedChainSimplices N (n+1) Monotone).filter
      (fun T => ∀ i, ∃ v ∈ T, label v = i)).card) := by
  induction n with
  | zero =>
    apply (lattice_sperner_parity 0 N label).mpr
    rw [one_dimensional_selected_boundary_card N hN label hpos]
    decide
  | succ n ih =>
    apply (lattice_sperner_parity (n+1) N label).mpr
    obtain ⟨lower, hlpos, heq⟩ := zero_wall_restrict_label n N hN label hpos
    rw [← zero_wall_boundary_card n N hN label lower hpos heq]
    exact ih lower hlpos

/-- Concrete ordered-lattice Sperner theorem. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem lattice_sperner (n N : ℕ) (hN : 0 < N)
    (label : (Fin (n+1) → Fin (N+1)) → Fin (n+2))
    (hpos : ∀ v, Monotone v → 0 < chainSimplex (chainPad v) N (label v)) :
    ∃ T ∈ boundedChainSimplices N (n+1) Monotone,
      ∀ i, ∃ v ∈ T, label v = i := by
  classical
  have h := lattice_sperner_odd n N hN label hpos
  have hp : 0 < ((boundedChainSimplices N (n+1) Monotone).filter
      (fun T => ∀ i, ∃ v ∈ T, label v = i)).card := by
    obtain ⟨k, hk⟩ := h; omega
  obtain ⟨T,hT⟩ := Finset.card_pos.mp hp
  exact ⟨T, (Finset.mem_filter.mp hT).1, (Finset.mem_filter.mp hT).2⟩
