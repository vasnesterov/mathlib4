import Mathlib

noncomputable def reprReal (x : ℝ) (b : ℕ) [NeZero b] : ℕ → Fin b :=
  fun i ↦ (⌊x * b^(i + 1)⌋ % b : ℤ)

example : reprReal (1/4) 3 0 = 0 := by
  simp [reprReal]
  norm_num

example : reprReal (1/4) 3 1 = 2 := by
  simp [reprReal]
  norm_num

noncomputable def ofDigitsTerm {b : ℕ} [NeZero b] (digits : ℕ → Fin b) : ℕ → ℝ :=
  fun i ↦ (digits i) * (b⁻¹ : ℝ)^(i + 1)

theorem ofDigitsTerm_nonneg {b : ℕ} [NeZero b] {digits : ℕ → Fin b} {n : ℕ} :
    0 ≤ ofDigitsTerm digits n := by
  simp [ofDigitsTerm]
  positivity

theorem ofDigitsTerm_le {b : ℕ} [NeZero b] {digits : ℕ → Fin b} {n : ℕ} (hb : 0 < b) :
    ofDigitsTerm digits n ≤ (b - 1) * (b⁻¹ : ℝ)^(n + 1) := by
  simp [ofDigitsTerm]
  gcongr
  rw [← Nat.cast_pred hb]
  norm_cast
  omega

-- todo : do we need this?
theorem ofDigitsTerm_lt {b : ℕ} [NeZero b] {digits : ℕ → Fin b} {n : ℕ} (hb : 0 < b) :
    ofDigitsTerm digits n < (b⁻¹ : ℝ)^n := by
  calc
    _ ≤ _ := ofDigitsTerm_le hb
    _ < _ := by
      rw [pow_succ]
      move_mul [(b⁻¹ : ℝ)^n]
      apply mul_lt_of_lt_one_left
      · positivity
      sorry

theorem ofDigitsTerm_Summable {b : ℕ} [NeZero b] (hb : 1 < b) {digits : ℕ → Fin b} :
    Summable (ofDigitsTerm digits) := by
  have h1 := summable_geometric_of_lt_one (r := (b⁻¹ : ℝ)) (by simp)
    (by rify at hb; exact inv_lt_one_of_one_lt₀ hb)
  apply Summable.mul_left (a := (b : ℝ)) at h1
  replace h1 : Summable fun i ↦ b * (b : ℝ)⁻¹ ^ (i + 1) := by
    sorry
  apply Summable.of_nonneg_of_le _ _ h1
  · intros
    exact ofDigitsTerm_nonneg
  intro i
  -- todo: refactor with above
  simp [ofDigitsTerm]
  gcongr
  simp

lemma ofDigits_partial_sum_gt {x : ℝ} {b : ℕ} [NeZero b] (hb : 1 < b) (n : ℕ) :
    x - (b⁻¹ : ℝ)^n < ∑ i ∈ Finset.range n, ofDigitsTerm (reprReal x b) i := by
  sorry

lemma ofDigits_partial_sum_le {x : ℝ} {b : ℕ} [NeZero b] (hb : 1 < b) (n : ℕ) :
    ∑ i ∈ Finset.range n, ofDigitsTerm (reprReal x b) i ≤ x := by
  sorry

theorem ofDigits_HasSum (x : ℝ) (b : ℕ) [NeZero b] (hb : 1 < b) :
    HasSum (ofDigitsTerm (reprReal x b)) x := by
  rw [hasSum_iff_tendsto_nat_of_summable_norm]
  swap
  · conv => arg 1; ext i; simp; rw [abs_of_nonneg (by simp [ofDigitsTerm]; positivity)]
    exact ofDigitsTerm_Summable hb
  rw [← tendsto_sub_nhds_zero_iff]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n ↦ -(b⁻¹ : ℝ)^n) (h := 0)
  · rw [show (0 : ℝ) = -0 by simp]
    apply Filter.Tendsto.neg
    apply tendsto_pow_atTop_nhds_zero_of_abs_lt_one
    rw [abs_of_nonneg (by positivity)]
    rify at hb
    exact inv_lt_one_of_one_lt₀ hb
  · apply tendsto_const_nhds
  · intro n
    simp
    have := ofDigits_partial_sum_gt (x := x) hb n
    simp at this
    linarith
  · intro n
    simp
    apply ofDigits_partial_sum_le hb

noncomputable def ofDigits {b : ℕ} [NeZero b] (digits : ℕ → Fin b) : ℝ :=
  ∑' n, ofDigitsTerm digits n

theorem ofDigits_nonneg {b : ℕ} [NeZero b] {digits : ℕ → Fin b} : 0 ≤ ofDigits digits := by
  simp [ofDigits]
  apply tsum_nonneg
  intro i
  exact ofDigitsTerm_nonneg

theorem ofDigits_le_one {b : ℕ} [NeZero b] {digits : ℕ → Fin b} : ofDigits digits ≤ 1 := by
  simp [ofDigits]
  sorry
  -- apply Summable.tsum_mono

theorem reprReal_ofDigits (b : ℕ) [NeZero b] (x : ℝ) (hb : 1 < b) :
    ofDigits (reprReal x b) = x := by
  simp [ofDigits]
  rw [← Summable.hasSum_iff]
  · exact ofDigits_HasSum x b hb
  · exact ofDigitsTerm_Summable hb

theorem cantorRepr_unique (a b : ℕ → Fin 3) (x : ℝ)
    (ha1 : HasSum (ofDigitsTerm a) x)
    (ha2 : ∀ n, a n ≠ 1)
    (hb1 : HasSum (ofDigitsTerm b) x)
    (hb2 : ∀ n, b n ≠ 1) :
    a = b := by
  by_contra! h
  replace h : ∃ n0, a n0 ≠ b n0 := by
    contrapose! h
    exact funext h
  let n0 := Nat.find h
  have h1 : ∀ n < n0, a n = b n := by
    intro n hn
    simpa using Nat.find_min h hn
  have h2 : a n0 ≠ b n0 := by
    simpa using Nat.find_spec h
  generalize n0 = n1 at h1 h2
  clear h n0
  wlog h3 : a n1 = 0 ∧ b n1 = 2 generalizing a b
  · replace h3 : a n1 = 2 ∧ b n1 = 0 := by
      specialize ha2 n1
      specialize hb2 n1
      generalize a n1 = u at *
      generalize b n1 = v at *
      fin_cases u <;> fin_cases v <;> simp at ha2 hb2 h2 h3 ⊢
    apply this b a hb1 hb2 ha1 ha2 (by intro n hn; symm; exact h1 n hn) h2.symm (by rwa [and_comm])
  obtain ⟨h3, h4⟩ := h3
  clear h2
  rw [← hasSum_nat_add_iff' n1] at ha1 hb1
  have : ∑ i ∈ Finset.range n1, ofDigitsTerm b i =
      ∑ i ∈ Finset.range n1, ofDigitsTerm a i := by
    apply Finset.sum_congr rfl
    intro n hn
    simp [ofDigitsTerm]
    congr
    symm
    apply h1
    simpa using hn
  rw [this] at hb1
  generalize x - ∑ i ∈ Finset.range n1, ofDigitsTerm a i = y at ha1 hb1
  have hy_ge := sum_le_hasSum {0} (by intros; exact ofDigitsTerm_nonneg) hb1
  simp [h4, ofDigitsTerm] at hy_ge
  rw [← hasSum_nat_add_iff' 1] at ha1
  simp at ha1
  conv at ha1 => arg 2; simp [ofDigitsTerm, h3]
  let geom (n : ℕ) : ℝ := 2 * (3⁻¹) ^ (n + 1 + n1 + 1)
  have h_geom : HasSum geom ((3⁻¹)^(n1 + 1)) := by
    simp [geom, pow_succ', pow_add]
    ring_nf
    have := hasSum_geometric_of_lt_one (r := (3⁻¹ : ℝ)) (by norm_num) (by norm_num)
    apply HasSum.mul_right (3⁻¹ ^ n1 * (2 / 9)) at this
    convert this using 1
    · ext n
      ring
    · ring
  have := hasSum_mono ha1 h_geom
    (by intro n; simp [geom]; convert ofDigitsTerm_le (show 0 < 3 by norm_num) <;> simp; norm_num)
  simp at this
  replace this := hy_ge.trans this
  simp at this

theorem cantorRepr_mem_cantorSet (a : ℕ → Fin 3) (x : ℝ)
    (h1 : HasSum (ofDigitsTerm a) x)
    (h2 : ∀ n, a n ≠ 1) : x ∈ cantorSet := by
  simp [cantorSet]
  intro i
  induction i generalizing a x with
  | zero =>
    simp
    constructor
    · apply h1.nonneg
      intros
      exact ofDigitsTerm_nonneg
    let geom (n : ℕ) : ℝ := 2 * (3⁻¹)^(n + 1)
    have h_geom : HasSum geom 1 := by
      simp [geom, pow_add]
      ring_nf
      have := hasSum_geometric_of_lt_one (r := (3⁻¹ : ℝ)) (by norm_num) (by norm_num)
      apply HasSum.mul_right (2 / 3) at this
      convert this using 1
      norm_num
    exact hasSum_mono h1 h_geom
      (by intro n; simp [geom]; convert ofDigitsTerm_le (show 0 < 3 by norm_num) <;> simp; norm_num)
  | succ i ih =>
    simp [preCantorSet]
    have h3 := h2 0
    replace h3 : a 0 = 0 ∨ a 0 = 2 := by
      generalize a 0 = v at *
      fin_cases v <;> simp at h3 ⊢
    rcases h3 with h3 | h3
    · left
      use 3 * x
      simp
      apply ih (fun n ↦ a (n + 1)) _ _ (by solve_by_elim)
      rw [← hasSum_nat_add_iff' 1] at h1
      simp [h3] at h1
      conv at h1 => arg 2; simp [ofDigitsTerm, h3]
      apply HasSum.mul_right 3 at h1
      convert h1 using 1
      · ext n
        simp [ofDigitsTerm]
        ring
      · ring
    · right
      -- copy-paste from above
      use 3 * x - 2
      simp
      apply ih (fun n ↦ a (n + 1)) _ _ (by solve_by_elim)
      rw [← hasSum_nat_add_iff' 1] at h1
      simp [h3] at h1
      conv at h1 => arg 2; simp [ofDigitsTerm, h3]
      apply HasSum.mul_right 3 at h1
      convert h1 using 1
      · ext n
        simp [ofDigitsTerm]
        ring
      · ring

theorem cantorRepr_mem_cantorSet' (a : ℕ → Fin 3) (h : ∀ n, a n ≠ 1) : ofDigits a ∈ cantorSet := by
  apply cantorRepr_mem_cantorSet a _ _ h
  apply Summable.hasSum
  apply ofDigitsTerm_Summable
  norm_num

open Classical in
noncomputable def cantorToDigits (x : ℝ) (n : ℕ) : Fin 3 :=
  if 3 * x ∈ preCantorSet n then
    0
  else
    2

theorem cantorToDigits_ne_one {x : ℝ} {n : ℕ} : cantorToDigits x n ≠ 1 := by
  simp [cantorToDigits]
  split_ifs <;> simp

theorem ofDigits_cantorToDigits {x : ℝ} (hx : x ∈ cantorSet) : ofDigits (cantorToDigits x) = x := by
  simp [ofDigits]
  rw [HasSum.tsum_eq]
  rw [hasSum_iff_tendsto_nat_of_summable_norm]
  swap
  · conv => arg 1; ext i; simp; rw [abs_of_nonneg (by simp [ofDigitsTerm])]
    exact ofDigitsTerm_Summable (show 1 < 3 by norm_num)
  sorry

noncomputable def cantorSet_equiv : cantorSet ≃ (ℕ → Bool) where
  toFun := fun ⟨x, h⟩ ↦ fun i ↦ if cantorToDigits x i = 0 then 0 else 1
  invFun (x : ℕ → Bool) :=
    let a : ℕ → Fin 3 := fun i ↦ if x i then 2 else 0
    let x : ℝ := ofDigits a
    have hx : x ∈ cantorSet := by
      simp [x]
      apply cantorRepr_mem_cantorSet'
      intro n
      simp [a]
      split_ifs <;> simp
    ⟨x, hx⟩
  left_inv := by
    intro ⟨x, hx⟩
    simp
    convert ofDigits_cantorToDigits hx
    rename_i i
    split_ifs with h_if
    · simp at h_if
      have : cantorToDigits x i ≠ 1 := cantorToDigits_ne_one
      generalize cantorToDigits x i = u at *
      fin_cases u <;> simp at h_if this ⊢
    · simp at h_if
      rw [h_if]
  right_inv := by
    intro b
    simp [cantorToDigits]
    ext i
    split_ifs with h1 h2
    · sorry
    · simp at h2
    · omega
    · sorry

instance : CompactSpace cantorSet := by
  rw [← isCompact_iff_compactSpace]
  exact isCompact_cantorSet

noncomputable def cantorSet_homeo : cantorSet ≃ₜ (ℕ → Bool) :=
  Continuous.homeoOfEquivCompactToT2 (f := cantorSet_equiv)
  (by
    apply continuous_pi
    intro i
    simp [cantorSet_equiv]
    rw [continuous_discrete_rng]
    suffices ∀ (b : Bool), IsClosed ((fun (a : cantorSet) ↦ if cantorToDigits a i = 0 then 0 else 1) ⁻¹' {b}) by
      sorry -- finite discrete topology
    intro b
    cases b
    · have : ((fun a ↦ if cantorToDigits (↑a) i = 0 then 0 else 1) ⁻¹' {false} : Set cantorSet) =
        ({x | cantorToDigits x i = 0} : Set cantorSet) := by
        ext x
        simp
        intro
        rfl
      rw [this]
      clear this
      simp [cantorToDigits]
      have : ({x | (3 : ℝ) * x ∈ preCantorSet i} : Set cantorSet) =
          Subtype.val ⁻¹' {x | (3 : ℝ) * x ∈ preCantorSet i} := by
        ext x
        simp
      rw [this]
      clear this
      apply IsClosed.preimage continuous_subtype_val
      have : {x | 3 * x ∈ preCantorSet i} = (fun x ↦ 3⁻¹ * x) '' (preCantorSet i) := by
        ext x
        simp
        constructor
        · intro h
          use 3 * x
          simp [h]
        · intro ⟨y, h1, h2⟩
          rw [← h2]
          convert h1
          ring
      rw [this]
      clear this
      suffices IsClosed (preCantorSet i) by
        sorry
      exact isClosed_preCantorSet i
    · have : ((fun a ↦ if cantorToDigits (↑a) i = 0 then 0 else 1) ⁻¹' {true} : Set cantorSet) =
        ({x | cantorToDigits x i = 2} : Set cantorSet) := by
        ext x
        simp
        have := @cantorToDigits_ne_one x i
        generalize cantorToDigits x i = u at this
        constructor
        · intro ⟨h, _⟩
          fin_cases u <;> simp at this h ⊢
        · intro h
          refine ⟨?_, rfl⟩
          fin_cases u <;> simp at this h ⊢
      rw [this]
      clear this
      simp [cantorToDigits]
      have : ({x | (3 : ℝ) * x ∉ preCantorSet i} : Set cantorSet) =
          ({x | (3 : ℝ) * x - 2 ∈ preCantorSet i} : Set cantorSet) := by
        ext ⟨x, h1⟩
        simp [cantorSet] at h1
        specialize h1 (i + 1)
        simp at h1
        simp
        clear * - h1 -- TODO: why does simp duplicates hypothesis?
        constructor
        · intro h2
          rcases h1 with ⟨y, h1, hx⟩ | ⟨y, h1, hx⟩ <;> subst hx
          · ring_nf at h2
            contradiction
          · ring_nf
            exact h1
        · intro h2
          sorry -- use that 3 * x - 2 in [0, 1]
      rw [this]
      clear this
      have : ({x | (3 : ℝ) * x - 2 ∈ preCantorSet i} : Set cantorSet) =
          Subtype.val ⁻¹' {x | (3 : ℝ) * x - 2 ∈ preCantorSet i} := by
        ext x
        simp
      rw [this]
      clear this
      apply IsClosed.preimage continuous_subtype_val
      have : {x | 3 * x - 2 ∈ preCantorSet i} = (fun x ↦ 3⁻¹ * (x + 2)) '' (preCantorSet i) := by
        ext x
        simp
        constructor
        · intro h
          use 3 * x - 2
          simp [h]
        · intro ⟨y, h1, h2⟩
          rw [← h2]
          convert h1
          ring
      rw [this]
      clear this
      suffices IsClosed (preCantorSet i) by
        sorry
      exact isClosed_preCantorSet i
  )

noncomputable def fromBinary (b : ℕ → Bool) : unitInterval :=
  let x : ℝ := ofDigits (finTwoEquiv.symm ∘ b)
  have hx : x ∈ Set.Icc 0 1 := by
    simp [x]
    constructor
    · exact ofDigits_nonneg
    · exact ofDigits_le_one
  ⟨x, hx⟩

theorem fromBinary_continuous : Continuous fromBinary := by
  sorry

theorem fromBinary_surjective : Function.Surjective fromBinary := by
  intro x
  use finTwoEquiv ∘ (reprReal x 2)
  simp [fromBinary, ← Function.comp_assoc, reprReal_ofDigits]

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

/- Peano curve -/

lemma unitInterval_eq_closedBall : unitInterval = Metric.closedBall 2⁻¹ 2⁻¹ := by
  ext x
  simp [dist, abs_le']
  norm_num
  rw [and_comm]

instance : TietzeExtension unitInterval := by
  rw [unitInterval_eq_closedBall]
  apply Metric.instTietzeExtensionClosedBall ℝ
  norm_num

lemma long_peano_curve : ∃ f : C(ℝ, unitInterval × unitInterval), Set.univ = f '' cantorSet  := by
  let g : C(cantorSet, unitInterval × unitInterval) :=
    ⟨projectCantor (unitInterval × unitInterval), by apply projectCantor_continuous⟩
  obtain ⟨f, hf⟩ := ContinuousMap.exists_restrict_eq isClosed_cantorSet g
  use f
  have hg : Function.Surjective g := by
    simp [g]
    exact projectCantor_surjective
  ext y
  simp
  obtain ⟨x, hx⟩ := hg y
  use x
  have := ContinuousMap.restrict_apply f cantorSet x
  simp [← this, hf, hx]

lemma peano_curve :
    ∃ f : C(unitInterval, unitInterval × unitInterval), Function.Surjective f := by
  obtain ⟨f, hf⟩ := long_peano_curve
  let g := ContinuousMap.restrict unitInterval f
  use g
  intro y
  rw [Set.ext_iff] at hf
  specialize hf y
  simp at hf
  obtain ⟨x, hx1, hx2⟩ := hf
  use ⟨x, by simp [cantorSet] at hx1; specialize hx1 0; simpa using hx1⟩
  simp [g, hx2]
