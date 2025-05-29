import Mathlib

theorem preCantorSet_Antitone : Antitone preCantorSet := by
  intro n m h
  simp only [Set.le_eq_subset]
  induction m, h using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    trans preCantorSet m
    swap
    · exact ih
    clear * -
    simp only [preCantorSet_succ, Set.union_subset_iff]
    induction m with
    | zero =>
      simp only [preCantorSet_zero]
      constructor <;> intro x <;> simp only [Set.mem_image, Set.mem_Icc, forall_exists_index,
        and_imp] <;> intro y <;> intros <;> constructor <;> linarith
    | succ m ih =>
      simp only [preCantorSet_succ, Set.union_subset_iff, Set.image_union]
      constructor
      · constructor <;> apply Set.subset_union_of_subset_left
        · exact Set.image_mono ih.left
        · exact Set.image_mono ih.right
      · constructor <;> apply Set.subset_union_of_subset_right
        · exact Set.image_mono ih.left
        · exact Set.image_mono ih.right

theorem cantorSet_eq_union_small_cantorSets :
    cantorSet = (· / 3) '' cantorSet ∪ (fun x ↦ (2 + x) / 3) '' cantorSet := by
  simp [cantorSet]
  rw [Set.image_iInter, Set.image_iInter]
  rotate_left
  · change Function.Bijective ((fun x ↦ x / 3) ∘ (fun x ↦ 2 + x))
    apply Function.Bijective.comp
    · apply mulRight_bijective₀ 3⁻¹
      norm_num
    · exact AddGroup.addLeft_bijective 2
  · apply mulRight_bijective₀ 3⁻¹
    norm_num
  rw [← Set.iInter_union_of_antitone]
  rotate_left
  · apply Monotone.comp_antitone Set.monotone_image preCantorSet_Antitone
  · apply Monotone.comp_antitone Set.monotone_image preCantorSet_Antitone
  change ⋂ n, preCantorSet n = ⋂ n, preCantorSet (n + 1)
  symm
  apply Antitone.iInter_nat_add preCantorSet_Antitone

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
-- theorem ofDigitsTerm_lt {b : ℕ} [NeZero b] {digits : ℕ → Fin b} {n : ℕ} (hb : 0 < b) :
--     ofDigitsTerm digits n < (b⁻¹ : ℝ)^n := by
--   calc
--     _ ≤ _ := ofDigitsTerm_le hb
--     _ < _ := by
--       rw [pow_succ]
--       move_mul [(b⁻¹ : ℝ)^n]
--       apply mul_lt_of_lt_one_left
--       · positivity
--       sorry

theorem ofDigitsTerm_Summable {b : ℕ} [NeZero b] (hb : 1 < b) {digits : ℕ → Fin b} :
    Summable (ofDigitsTerm digits) := by
  have h1 := summable_geometric_of_lt_one (r := (b⁻¹ : ℝ)) (by simp)
    (by rify at hb; exact inv_lt_one_of_one_lt₀ hb)
  apply Summable.mul_left (a := (b : ℝ)) at h1
  replace h1 : Summable fun i ↦ b * (b : ℝ)⁻¹ ^ (i + 1) := by
    simp_rw [pow_succ', ← mul_assoc, mul_comm (b : ℝ), mul_assoc]
    exact Summable.mul_left _ h1
  apply Summable.of_nonneg_of_le _ _ h1
  · intros
    exact ofDigitsTerm_nonneg
  intro i
  -- todo: refactor with above
  simp [ofDigitsTerm]
  gcongr
  simp

lemma ofDigits_partial_sum_ge {x : ℝ} {b : ℕ} [NeZero b] (hb : 1 < b) (hx : x ∈ Set.Icc 0 1)
    {n : ℕ} :
    x - (b⁻¹ : ℝ)^n ≤ ∑ i ∈ Finset.range n, ofDigitsTerm (reprReal x b) i := by
  simp at hx
  obtain ⟨hx1, hx2⟩ := hx
  -- induction n does not help
  sorry

lemma ofDigits_partial_sum_le {x : ℝ} {b : ℕ} [NeZero b] (hb : 1 < b) {n : ℕ}
    (hx : x ∈ Set.Icc 0 1) :
    ∑ i ∈ Finset.range n, ofDigitsTerm (reprReal x b) i ≤ x := by
  simp at hx
  obtain ⟨hx1, hx2⟩ := hx
  -- induction n does not help
  sorry

theorem ofDigits_HasSum (x : ℝ) (b : ℕ) [NeZero b] (hb : 1 < b) (hx : x ∈ Set.Icc 0 1) :
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
    have := ofDigits_partial_sum_ge hb hx (n := n)
    simp at this
    linarith
  · intro n
    simp
    exact ofDigits_partial_sum_le hb hx

noncomputable def ofDigits {b : ℕ} [NeZero b] (digits : ℕ → Fin b) : ℝ :=
  ∑' n, ofDigitsTerm digits n

theorem ofDigits_nonneg {b : ℕ} [NeZero b] {digits : ℕ → Fin b} : 0 ≤ ofDigits digits := by
  simp [ofDigits]
  apply tsum_nonneg
  intro i
  exact ofDigitsTerm_nonneg

theorem ofDigits_le_one {b : ℕ} [inst_neZero : NeZero b] {digits : ℕ → Fin b}  :
    ofDigits digits ≤ 1 := by
  by_cases hb : ¬(1 < b)
  · interval_cases b
    · simp at inst_neZero
    simp [ofDigits, ofDigitsTerm]
  push_neg at hb
  have hb_inv_nonneg : 0 ≤ (b⁻¹ : ℝ) := by simp
  have hb_inv_lt_one : (b⁻¹ : ℝ) < 1 := by
    rify at hb
    exact inv_lt_one_of_one_lt₀ hb
  simp [ofDigits]
  let g (i : ℕ) : ℝ := (1 - (b⁻¹ : ℝ)) * (b⁻¹ : ℝ)^i
  have hg_summable : Summable g := by
    apply Summable.mul_left
    apply summable_geometric_of_lt_one (by simp)
      (by rify at hb; exact inv_lt_one_of_one_lt₀ hb)
  convert Summable.tsum_mono (ofDigitsTerm_Summable hb) hg_summable _
  · simp [g, tsum_mul_left, ← inv_pow]
    rw [tsum_geometric_of_lt_one hb_inv_nonneg hb_inv_lt_one, mul_inv_cancel₀]
    linarith
  · intro i
    simp [g]
    convert ofDigitsTerm_le (by linarith) using 1
    rw [pow_succ, inv_pow]
    move_mul [((b : ℝ)^i)⁻¹]
    congr
    rw [sub_mul, mul_inv_cancel₀]
    · simp
    · rify at hb
      linarith

theorem reprReal_ofDigits (b : ℕ) [NeZero b] (x : ℝ) (hb : 1 < b) (hx : x ∈ Set.Icc 0 1) :
    ofDigits (reprReal x b) = x := by
  simp [ofDigits]
  rw [← Summable.hasSum_iff]
  · exact ofDigits_HasSum x b hb hx
  · exact ofDigitsTerm_Summable hb

theorem cantorRepr_HasSum_unique {a b : ℕ → Fin 3} {x : ℝ}
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
    apply this hb1 hb2 ha1 ha2 (by intro n hn; symm; exact h1 n hn) h2.symm (by rwa [and_comm])
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

theorem cantorRepr_ofDigits_unique {a b : ℕ → Fin 3}
    (ha : ∀ n, a n ≠ 1)
    (hb : ∀ n, b n ≠ 1)
    (h : ofDigits a = ofDigits b) :
    a = b := by
  set x := ofDigits a
  have ha2 : HasSum (ofDigitsTerm a) x := by
    simp [x, ofDigits]
    apply Summable.hasSum
    apply ofDigitsTerm_Summable
    norm_num
  have hb2 : HasSum (ofDigitsTerm b) x := by
    simp [h, ofDigits]
    apply Summable.hasSum
    apply ofDigitsTerm_Summable
    norm_num
  apply cantorRepr_HasSum_unique ha2 ha hb2 hb

theorem cantorRepr_HasSum_mem_cantorSet {a : ℕ → Fin 3} {x : ℝ}
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
      apply ih (a := fun n ↦ a (n + 1)) _ (by solve_by_elim)
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
      apply ih (a := fun n ↦ a (n + 1)) _ (by solve_by_elim)
      rw [← hasSum_nat_add_iff' 1] at h1
      simp [h3] at h1
      conv at h1 => arg 2; simp [ofDigitsTerm, h3]
      apply HasSum.mul_right 3 at h1
      convert h1 using 1
      · ext n
        simp [ofDigitsTerm]
        ring
      · ring

theorem cantorRepr_ofDigits_mem_cantorSet {a : ℕ → Fin 3}
    (h : ∀ n, a n ≠ 1) : ofDigits a ∈ cantorSet := by
  have : HasSum (ofDigitsTerm a) (ofDigits a) := by
    simp [ofDigits]
    apply Summable.hasSum
    apply ofDigitsTerm_Summable
    norm_num
  exact cantorRepr_HasSum_mem_cantorSet this h

/-- Generates the first digit and scales x back to [0, 1]. -/
noncomputable def cantorStep (x : ℝ) : ℝ :=
  if x ∈ Set.Icc 0 (1/3) then
    3 * x
  else
    3 * x - 2

theorem cantorStep_mem_cantorSet {x : ℝ} (hx : x ∈ cantorSet) : cantorStep x ∈ cantorSet := by
  simp only [cantorStep]
  rw [cantorSet_eq_union_small_cantorSets] at hx
  simp at hx
  split_ifs with h
  · rcases hx with ⟨y, hy, hx⟩ | ⟨y, hy, hx⟩
    · rw [← hx]
      ring_nf
      exact hy
    · rw [← hx] at h
      apply cantorSet_subset_unitInterval at hy
      simp at h hy
      linarith
  · rcases hx with ⟨y, hy, hx⟩ | ⟨y, hy, hx⟩
    · rw [← hx] at h
      apply cantorSet_subset_unitInterval at hy
      absurd h
      simp only [one_div, Set.mem_Icc, not_and] at hy ⊢
      constructor <;> linarith
    · rw [← hx]
      ring_nf
      exact hy

noncomputable def cantorSequence (x : ℝ) : Stream' ℝ :=
  Stream'.iterate cantorStep x

theorem cantorSequence_mem_cantorSet {x : ℝ} (hx : x ∈ cantorSet) {n : ℕ} :
    (cantorSequence x).get n ∈ cantorSet := by
  induction n with
  | zero => simpa [cantorSequence]
  | succ n ih =>
    simp [cantorSequence, Stream'.get_succ_iterate'] at ih ⊢
    exact cantorStep_mem_cantorSet ih

noncomputable def cantorToBinary (x : ℝ) : Stream' Bool :=
  (cantorSequence x).map fun x ↦
    if x ∈ Set.Icc 0 (1/3) then
      false
    else
      true

noncomputable def cantorToDigits (x : ℝ) : Stream' (Fin 3) :=
  (cantorToBinary x).map (fun b ↦ cond b 2 0)

theorem one_notMem_cantorToDigits {x : ℝ} : 1 ∉ cantorToDigits x := by
  simp [cantorToDigits]
  intro h
  apply Stream'.exists_of_mem_map at h
  obtain ⟨b, _, h⟩ := h
  cases b <;> simp at h

theorem cantorToDigits_ne_one {x : ℝ} {n : ℕ} : (cantorToDigits x).get n ≠ 1 := by
  simp only [cantorToDigits]
  intro h
  symm at h
  apply Stream'.mem_of_get_eq at h
  apply one_notMem_cantorToDigits h

theorem partial_diff_eq_cantorSequence {x : ℝ} {n : ℕ} :
    (x - ∑ i ∈ Finset.range n, ofDigitsTerm (cantorToDigits x).get i) * 3^n
      = (cantorSequence x).get n := by
  induction n with
  | zero =>
    simp [cantorSequence]
  | succ n ih =>
    calc
      _ = 3 * (((x - ∑ i ∈ Finset.range n, ofDigitsTerm (cantorToDigits x).get i) * 3 ^ n) -
          3^n * ofDigitsTerm (cantorToDigits x).get n) := by
        rw [pow_succ, Finset.sum_range_succ]
        ring
      _ = 3 * ((cantorSequence x).get n - 3^n * ofDigitsTerm (cantorToDigits x).get n) := by
        rw [ih]
      _ = _ := by
        simp [cantorSequence]
        conv => rhs; simp [Stream'.get_succ_iterate']
        simp only [cantorToDigits, cantorToBinary, cantorSequence, ofDigitsTerm, Stream'.get_map]
        set y := (Stream'.iterate cantorStep x).get n
        split_ifs with h_if <;> simp only [cantorStep, h_if] <;> simp
        rw [pow_succ, mul_inv]
        set a := (3 : ℝ) ^ n
        ring_nf
        rw [mul_inv_cancel₀ (by simp [a])]
        ring

theorem ofDigits_cantorToDigits_partial_sum_le {x : ℝ} (hx : x ∈ cantorSet) {n : ℕ} :
    ∑ i ∈ Finset.range n, ofDigitsTerm (cantorToDigits x) i ≤ x := by
  have := partial_diff_eq_cantorSequence (x := x) (n := n)
  have h_mem := cantorSequence_mem_cantorSet hx (n := n)
  rw [← this] at h_mem
  apply cantorSet_subset_unitInterval at h_mem
  simp only [Set.mem_Icc] at h_mem
  simpa using h_mem.left

theorem ofDigits_cantorToDigits_partial_sum_ge {x : ℝ} (hx : x ∈ cantorSet) {n : ℕ} :
    x - (3⁻¹ : ℝ)^n ≤ ∑ i ∈ Finset.range n, ofDigitsTerm (cantorToDigits x) i := by
  have := partial_diff_eq_cantorSequence (x := x) (n := n)
  have h_mem := cantorSequence_mem_cantorSet hx (n := n)
  rw [← this] at h_mem
  apply cantorSet_subset_unitInterval at h_mem
  simp only [Set.mem_Icc] at h_mem
  apply And.right at h_mem
  rw [← mul_le_mul_right (show 0 < (3 : ℝ)^n by positivity), sub_mul, inv_pow,
    inv_mul_cancel₀ (by simp)]
  linarith!

theorem ofDigits_cantorToDigits {x : ℝ} (hx : x ∈ cantorSet) :
    ofDigits (cantorToDigits x).get = x := by
  simp [ofDigits]
  rw [HasSum.tsum_eq]
  rw [hasSum_iff_tendsto_nat_of_summable_norm]
  swap
  · conv => arg 1; ext i; simp; rw [abs_of_nonneg (by simp [ofDigitsTerm])]
    exact ofDigitsTerm_Summable (show 1 < 3 by norm_num)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n ↦ x - (3⁻¹ : ℝ)^n) (h := fun _ ↦ x)
  · rw [← tendsto_sub_nhds_zero_iff]
    simp only [sub_sub_cancel_left]
    rw [show 0 = -(0 : ℝ) by simp]
    apply Filter.Tendsto.neg
    apply tendsto_pow_atTop_nhds_zero_of_abs_lt_one
    rw [abs_lt]
    constructor <;> norm_num
  · exact tendsto_const_nhds
  · intro n
    dsimp only
    exact ofDigits_cantorToDigits_partial_sum_ge hx
  · intro n
    dsimp only
    exact ofDigits_cantorToDigits_partial_sum_le hx

noncomputable def cantorSet_equiv : cantorSet ≃ (ℕ → Bool) where
  toFun := fun ⟨x, h⟩ ↦ (cantorToBinary x).get
  invFun (x : ℕ → Bool) :=
    let a : ℕ → Fin 3 := fun i ↦ if x i then 2 else 0
    let x : ℝ := ofDigits a
    have hx : x ∈ cantorSet := by
      simp [x]
      apply cantorRepr_ofDigits_mem_cantorSet
      intro n
      simp [a]
      split_ifs <;> simp
    ⟨x, hx⟩
  left_inv := by
    intro ⟨x, hx⟩
    simp
    convert ofDigits_cantorToDigits hx
    simp [cantorToDigits]
  right_inv := by
    intro b
    simp
    set x := ofDigits (b := 3) fun i ↦ if b i = true then 2 else 0
    have hx : x ∈ cantorSet := by
      apply cantorRepr_ofDigits_mem_cantorSet
      intro n
      split_ifs <;> simp
    have := ofDigits_cantorToDigits hx
    conv at this => rhs; unfold x
    apply cantorRepr_ofDigits_unique at this
    rotate_left
    · exact fun n ↦ cantorToDigits_ne_one
    · intro n
      split_ifs <;> simp
    ext n
    apply congrFun at this
    specialize this n
    simp [cantorToDigits] at this
    split_ifs at this with h1 h2 <;> simp at this
    · simp [h1, h2]
    · rename_i h2
      simp [h1, h2]

instance : CompactSpace cantorSet := by
  rw [← isCompact_iff_compactSpace]
  exact isCompact_cantorSet

lemma preCantorSet_subset_unitInterval {n : ℕ} : preCantorSet n ⊆ Set.Icc 0 1 := by
  rw [← preCantorSet_zero]
  apply preCantorSet_Antitone (by simp)

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
      rw [← Topology.IsClosedEmbedding.isClosed_iff_image_isClosed]
      swap
      · sorry
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
        · intro h2 h3
          apply preCantorSet_subset_unitInterval at h2
          apply preCantorSet_subset_unitInterval at h3
          simp at h2 h3
          linarith
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
      rw [← Topology.IsClosedEmbedding.isClosed_iff_image_isClosed]
      swap
      · sorry
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
