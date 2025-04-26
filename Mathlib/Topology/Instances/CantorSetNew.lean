import Mathlib

theorem cantorSet_eq : cantorSet =
    {x | ∃ (a : ℕ → Fin 3), (∀ i, a i ≠ 1) ∧ x = ∑' i, ((a i).val : ℝ) * (1/3)^(i + 1)} := by
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · sorry
  · simp at h
    obtain ⟨a, ha1, ha2⟩ := h
    subst ha2
    simp [cantorSet]
    intro j
    induction j with
    | zero =>
      simp
      sorry
    | succ j ih =>
      simp
      sorry

noncomputable def cantorSet_homeo : cantorSet ≃ₜ (ℕ → Bool) where
  toFun := fun ⟨x, h⟩ =>
    let a := (cantorSet_eq ▸ h).choose
    fun i ↦ if a i = 0 then false else true
  invFun (x : ℕ → Bool) :=
    let a : ℕ → Fin 3 := fun i ↦ if x i then 2 else 0
    let x : ℝ := ∑' i, ((a i).val : ℝ) * (1/3)^(i + 1)
    have hx : x ∈ cantorSet := by
      simp [cantorSet_eq, x]
      use a
      refine ⟨?_, by rfl⟩
      intro i
      simp [a]
      split_ifs <;> simp
    ⟨x, hx⟩
  left_inv := by
    intro ⟨x, hx⟩
    simp
    generalize_proofs _ _ h
    have ha := h.choose_spec
    set a := h.choose
    have : ∀ i, (if a i = 0 then 0 else 2) = a i := by
      intro i
      split_ifs with h_if
      · exact h_if.symm
      · have := ha.left i
        omega
    simp [this, ha.right]
  right_inv := by
    intro b
    ext j
    simp
    generalize_proofs _ _ h
    have ha := h.choose_spec
    set a := h.choose
    -- here I need uniqness of representation above
    cases hb : b j with
    | false =>
      sorry
    | true =>
      sorry
  continuous_toFun := by
    apply continuous_pi
    intro i
    simp
    rw [continuous_discrete_rng]
    intro b
    sorry
  continuous_invFun := by
    sorry

noncomputable def fromBinary (b : ℕ → Bool) : unitInterval :=
  let x : ℝ := ∑' i, (if b i then 1 else 0) * (1 / 2)^(i + 1)
  have hx : x ∈ Set.Icc 0 1 := by
    sorry
  ⟨x, hx⟩

theorem fromBinary_continuous : Continuous fromBinary := by
  sorry

theorem fromBinary_surjective : Function.Surjective fromBinary := by
  sorry

noncomputable def cantorSet_product : cantorSet ≃ₜ (ℕ → cantorSet) := by
  sorry

noncomputable def cantorToHilbert (x : cantorSet) : (ℕ → unitInterval) :=
  fun i ↦ fromBinary (cantorSet_homeo (cantorSet_product x i))

theorem cantorToHilbert_continuous : Continuous cantorToHilbert := by
  unfold cantorToHilbert
  apply continuous_pi
  intro i
  apply fromBinary_continuous.comp
  fun_prop

theorem cantorToHilbert_surjective : Function.Surjective cantorToHilbert := by
  sorry

open Classical in
noncomputable def embedHilbert (X : Type) [PseudoMetricSpace X] [CompactSpace X] :
    X → (ℕ → unitInterval) :=
  if h : Nonempty X then
    let s := TopologicalSpace.denseSeq X
    fun x i =>
      let d := dist x (s i)
      let diam := Metric.diam (Set.univ : Set X)
      have hd1 : d ≤ diam := by
        simp [diam]
        apply Metric.dist_le_diam_of_mem
        · rwa [← Metric.compactSpace_iff_isBounded_univ]
        · simp
        · simp
      have hd2 : (d / diam) ∈ unitInterval := by
        simp
        constructor
        · positivity
        · apply div_le_one_of_le₀ hd1
          positivity
      ⟨_, hd2⟩
  else
    fun x i ↦ 0

theorem embed_continuous {X : Type} [PseudoMetricSpace X] [CompactSpace X] :
    Continuous (embedHilbert X) := by
  simp [embedHilbert]
  split_ifs <;> fun_prop

theorem embed_injective {X : Type} [MetricSpace X] [CompactSpace X] :
    Function.Injective (embedHilbert X) := by
  intro x y hxy
  simp [embedHilbert] at hxy
  split_ifs at hxy with h
  swap
  · simp at h
    exfalso
    exact h.false x
  suffices dist x y = 0 from eq_of_dist_eq_zero this
  simp at hxy
  apply congrFun at hxy
  simp at hxy
  set diam := Metric.diam (Set.univ : Set X)
  by_cases h_diam : diam = 0
  · have : dist x y ≤ diam := by
      apply Metric.dist_le_diam_of_mem (by rwa [← Metric.compactSpace_iff_isBounded_univ]) <;> simp
    linarith [dist_nonneg (x := x) (y := y)]
  simp_rw [div_left_inj' h_diam] at hxy
  have h_dense := TopologicalSpace.denseRange_denseSeq X
  simp [DenseRange] at h_dense
  by_contra! h
  set s := TopologicalSpace.denseSeq X
  obtain ⟨i, hx⟩ : ∃ i, dist x (s i) < dist x y / 3 := by
    simpa using h_dense.exists_dist_lt x (ε := dist x y / 3) (by positivity)
  have hy : dist (s i) y < dist x y / 3 := by
    rwa [dist_comm, ← hxy]
  have := dist_triangle x (s i) y
  linarith [dist_nonneg (x := x) (y := y)]

noncomputable def projectCantor (X : Type) [MetricSpace X] [CompactSpace X] : cantorSet → X :=
  sorry

theorem projectCantor_continuous {X : Type} [MetricSpace X] [CompactSpace X] :
    Continuous (projectCantor X) := by
  sorry

theorem projectCantor_surjective {X : Type} [MetricSpace X] [CompactSpace X] :
    Function.Surjective (projectCantor X) := by
  sorry
