module

public import Legacy.TorusEndpoint.FiniteAtomMonotonicity
public import Legacy.TorusEndpoint.CertifiedExp
public import Legacy.TorusEndpoint.EndpointNormalization
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

@[expose] public section

/-! Finite-atom mass bounds and the positive third-axis coefficient estimate.
The finite alphabet is deduplicated; repeated entries in a list do not create
extra words in the actual coefficient. No full three-dimensional cap is asserted. -/

open scoped BigOperators
open Legacy.TorusEndpoint.FiniteCone Legacy.TorusEndpoint.FiniteAtomCoefficients

namespace Legacy.TorusEndpoint.D3AxisCoefficient

noncomputable def exactWords {α : Type*} (s : Finset α) : ℕ → Finset (List α)
  | 0 => {[]}
  | n + 1 => by
    classical
    exact s.biUnion (fun x => (exactWords s n).image (List.cons x))

theorem mem_exactWords {α : Type*} (s : Finset α) (n : ℕ) (xs : List α) :
    xs ∈ exactWords s n ↔ xs.length = n ∧ ∀ x ∈ xs, x ∈ s := by
  classical
  induction n generalizing xs with
  | zero => cases xs <;> simp [exactWords]
  | succ n ih =>
    cases xs with
    | nil => simp [exactWords]
    | cons x xs =>
      simp [exactWords, ih, List.length_cons, and_assoc, and_left_comm, and_comm]

theorem exactWords_disjoint_heads {α : Type*} [DecidableEq α] (s : Finset α) (n : ℕ) :
    Set.PairwiseDisjoint (↑s) (fun x => (exactWords s n).image (List.cons x)) := by
  classical
  intro x _ y _ hxy
  apply Finset.disjoint_left.mpr
  intro xs hx hy
  obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hx
  obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hy
  have h := hu.trans hv.symm
  exact hxy (List.cons.inj h).1

theorem exactWords_product_sum {α : Type*} (s : Finset α) (a : α → ℝ) (n : ℕ) :
    (∑ xs ∈ exactWords s n, (xs.map a).prod) = (∑ x ∈ s, a x) ^ n := by
  classical
  induction n with
  | zero => simp [exactWords]
  | succ n ih =>
    rw [exactWords, Finset.sum_biUnion (exactWords_disjoint_heads s n)]
    calc
      _ = ∑ x ∈ s, a x * (∑ xs ∈ exactWords s n, (xs.map a).prod) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_image]
        · simp [Finset.mul_sum]
        · intro u _ v _ h
          exact (List.cons.inj h).2
      _ = _ := by simp only [ih, ← Finset.sum_mul, pow_succ, mul_comm]

theorem exactWords_weight_sum {d : ℕ} (s : Finset (Vec d)) (a : Vec d → ℝ) (n : ℕ) :
    (∑ xs ∈ exactWords s n, wordWeight a 1 xs) = scalarExpTerm (∑ x ∈ s, a x) n := by
  classical
  calc
    _ = scalarExpTerm 1 n * ∑ xs ∈ exactWords s n, (xs.map a).prod := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro xs hx
      rw [wordWeight, (mem_exactWords s n xs).mp hx |>.1]
    _ = _ := by rw [exactWords_product_sum]; simp [scalarExpTerm, div_eq_mul_inv, mul_comm]

theorem exactWords_disjoint_lengths {α : Type*} (s : Finset α) (N : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.range N)) (exactWords s) := by
  intro n _ m _ hnm
  apply Finset.disjoint_left.mpr
  intro xs hn hm
  exact hnm (((mem_exactWords s n xs).mp hn).1.symm.trans
    ((mem_exactWords s m xs).mp hm).1)

/-- For a nonzero output, its complete coefficient together with the empty
word is bounded by all finite words up to the valid separator length bound. -/
theorem coefficient_le_exp_mass_sub_one {d : ℕ}
    (atoms : List (Vec d)) (w : Vec d) (a : Vec d → ℝ) (k : Vec d)
    (hw : ∀ x ∈ atoms, 0 < eval w x) (ha : ∀ x ∈ atoms, 0 ≤ a x) (hk : k ≠ 0) :
    coefficient atoms w a 1 k ≤ Real.exp (∑ x ∈ atoms.toFinset, a x) - 1 := by
  classical
  let s := atoms.toFinset
  let N := (eval w k).toNat
  let allWords := (Finset.range (N + 1)).biUnion (exactWords s)
  have hsubset : insert [] (decompositions atoms w k) ⊆ allWords := by
    intro xs hxs
    apply Finset.mem_biUnion.mpr
    rcases Finset.mem_insert.mp hxs with he | hm
    · subst xs
      exact ⟨0, Finset.mem_range.mpr (Nat.succ_pos _), (mem_exactWords s 0 []).mpr (by simp)⟩
    · obtain ⟨hmem, hsum⟩ := (mem_decompositions_iff atoms w k hw xs).mp hm
      have hb := length_le_eval_sum w xs (fun x hx => hw x (hmem x hx))
      rw [hsum] at hb
      refine ⟨xs.length, Finset.mem_range.mpr ?_, (mem_exactWords s xs.length xs).mpr ?_⟩
      · dsimp [N]
        omega
      · exact ⟨rfl, fun x hx => List.mem_toFinset.mpr (hmem x hx)⟩
  have hzero : [] ∉ decompositions atoms w k := by
    intro he
    have hs := ((mem_decompositions_iff atoms w k hw []).mp he).2
    exact hk hs.symm
  have hsum : 1 + coefficient atoms w a 1 k ≤
      ∑ xs ∈ allWords, wordWeight a 1 xs := by
    have hleft : 1 + coefficient atoms w a 1 k =
        ∑ xs ∈ insert [] (decompositions atoms w k), wordWeight a 1 xs := by
      rw [Finset.sum_insert hzero, wordWeight_nil]
      rfl
    rw [hleft]
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro xs hx _
    obtain ⟨n, _, hn⟩ := Finset.mem_biUnion.mp hx
    exact wordWeight_nonneg a (by norm_num) xs (fun x hx =>
      ha x (List.mem_toFinset.mp (((mem_exactWords s n xs).mp hn).2 x hx)))
  have htotal : (∑ xs ∈ allWords, wordWeight a 1 xs) =
      ∑ n ∈ Finset.range (N + 1), scalarExpTerm (∑ x ∈ s, a x) n := by
    rw [show allWords = (Finset.range (N + 1)).biUnion (exactWords s) from rfl,
      Finset.sum_biUnion (exactWords_disjoint_lengths s (N + 1))]
    apply Finset.sum_congr rfl
    intro n _
    exact exactWords_weight_sum s a n
  rw [htotal] at hsum
  have hS : 0 ≤ ∑ x ∈ s, a x :=
    Finset.sum_nonneg (fun x hx => ha x (List.mem_toFinset.mp hx))
  have h := hsum.trans (scalarExpTerm_partial_sum_le_exp hS (N + 1))
  dsimp [s] at h
  linarith

theorem reciprocal_cube_step (x : ℝ) (hx : 0 < x) :
    1 / (x + 1) ^ 3 ≤ 1 / (2 * x ^ 2) - 1 / (2 * (x + 1) ^ 2) := by
  have hx1 : x + 1 ≠ 0 := ne_of_gt (by linarith)
  have heq : (1 / (2 * x ^ 2) - 1 / (2 * (x + 1) ^ 2)) - 1 / (x + 1) ^ 3 =
      (3 * x + 1) / (2 * x ^ 2 * (x + 1) ^ 3) := by
    field_simp
    ring
  apply sub_nonneg.mp
  rw [heq]
  positivity

theorem reciprocal_cube_tail_bound (N : ℕ) :
    (∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 3) ^ 3) ≤
      1 / 8 - 1 / (2 * ((N : ℝ) + 2) ^ 2) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have h := reciprocal_cube_step ((N : ℝ) + 2) (by positivity)
    have he : (N : ℝ) + 2 + 1 = (N : ℝ) + 3 := by ring
    rw [he] at h
    have he' : ((N + 1 : ℕ) : ℝ) + 2 = (N : ℝ) + 3 := by push_cast; ring
    rw [he']
    linarith

theorem reciprocal_cube_range_bound (N : ℕ) :
    (∑ n ∈ Finset.range (N + 3), 1 / (n : ℝ) ^ 3) ≤ (5 : ℝ) / 4 := by
  rw [Nat.add_comm N 3, Finset.sum_range_add]
  have htail := reciprocal_cube_tail_bound N
  have hnonneg : 0 ≤ 1 / (2 * ((N : ℝ) + 2) ^ 2) := by positivity
  have h := htail.trans (sub_le_self _ hnonneg)
  norm_num [Finset.sum_range_succ] at ⊢
  simp only [one_div] at h
  simp only [add_comm (3 : ℝ)]
  linarith

theorem reciprocal_cube_finset_bound (s : Finset ℕ) :
    (∑ n ∈ s, 1 / (n : ℝ) ^ 3) ≤ (5 : ℝ) / 4 := by
  have hs : s ⊆ Finset.range (s.sup id + 3) := by
    intro n hn
    apply Finset.mem_range.mpr
    have h : n ≤ s.sup id := Finset.le_sup (f := id) hn
    omega
  exact (Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => by positivity)).trans
    (reciprocal_cube_range_bound (s.sup id))

theorem exp_five_eighths_lt_two : Real.exp ((5 : ℝ) / 8) < 2 := by
  have h := (CertifiedExp.point_enclosure ((5 : ℚ) / 8) 4 (by norm_num) (by norm_num)).2
  have hc : ((CertifiedExp.taylor ((5 : ℚ) / 8) 4 +
      CertifiedExp.remainder ((5 : ℚ) / 8) 4 : ℚ) : ℝ) < 2 := by
    norm_num [CertifiedExp.taylor, CertifiedExp.remainder, Finset.sum_range_succ]
  have h' : Real.exp ((5 : ℝ) / 8) ≤ ((CertifiedExp.taylor ((5 : ℚ) / 8) 4 +
      CertifiedExp.remainder ((5 : ℚ) / 8) 4 : ℚ) : ℝ) := by simpa using h
  exact h'.trans_lt hc

/-- The actual third-axis frequency, with a natural coordinate. -/
def axis (n : ℕ) : Frequency 3 := ![0, 0, (n : ℤ)]

theorem frequencyRadius_axis (n : ℕ) : frequencyRadius (axis n) = (n : ℝ) := by
  simp [frequencyRadius, axis, Fin.sum_univ_succ]

theorem endpointSigma_three : endpointSigma 3 = 4 * Real.pi := by
  have hg : Real.Gamma ((3 : ℝ) / 2) = Real.sqrt Real.pi / 2 := by
    convert Real.Gamma_nat_add_one_add_half 0 using 1 <;> norm_num
  have hp : Real.pi ^ ((3 : ℝ) / 2) = Real.pi * Real.sqrt Real.pi := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add Real.pi_pos,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hs : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  unfold endpointSigma
  norm_num only [Nat.cast_ofNat]
  rw [hg, hp]
  field_simp
  ring

theorem endpointCoupling_three : endpointCoupling 3 = 3 / (2 * Real.pi) := by
  unfold endpointCoupling
  rw [endpointSigma_three]
  norm_num
  ring

theorem endpointAtomWeight_axis (n : ℕ) :
    endpointAtomWeight 3 (axis n) = (3 / (2 * Real.pi)) * (1 / (n : ℝ) ^ 3) := by
  unfold endpointAtomWeight
  rw [frequencyRadius_axis, endpointCoupling_three]
  ring

/-- Every finite set of axis frequencies has mass strictly below 5/8.
This is proved directly; no zeta value or numerical hypothesis is assumed. -/
theorem endpoint_axis_mass_lt_five_eighths (s : Finset ℕ) :
    (∑ n ∈ s, endpointAtomWeight 3 (axis n)) < (5 : ℝ) / 8 := by
  simp_rw [endpointAtomWeight_axis]
  rw [← Finset.mul_sum]
  have hp : 0 ≤ (3 : ℝ) / (2 * Real.pi) := by positivity
  calc
    _ ≤ (3 / (2 * Real.pi)) * (5 / 4) :=
      mul_le_mul_of_nonneg_left (reciprocal_cube_finset_bound s) hp
    _ = 15 / (8 * Real.pi) := by ring
    _ < 5 / 8 := by
      apply (div_lt_iff₀ (mul_pos (by norm_num) Real.pi_pos)).mpr
      nlinarith [Real.pi_gt_three]

theorem endpoint_axis_atom_mass_lt_five_eighths (atoms : List (Frequency 3))
    (haxis : ∀ k ∈ atoms, ∃ n : ℕ, 0 < n ∧ k = axis n) :
    (∑ k ∈ atoms.toFinset, endpointAtomWeight 3 k) < (5 : ℝ) / 8 := by
  classical
  let idx : Frequency 3 → ℕ := fun k => (k 2).toNat
  have hrec : ∀ k ∈ atoms.toFinset, axis (idx k) = k := by
    intro k hk
    obtain ⟨n, _, rfl⟩ := haxis k (List.mem_toFinset.mp hk)
    simp [idx, axis]
  have hinj : Set.InjOn idx (↑atoms.toFinset : Set (Frequency 3)) := by
    intro k hk l hl hkl
    exact (hrec k hk).symm.trans ((congrArg axis hkl).trans (hrec l hl))
  have heq : (∑ k ∈ atoms.toFinset, endpointAtomWeight 3 k) =
      ∑ n ∈ atoms.toFinset.image idx, endpointAtomWeight 3 (axis n) := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hrec k hk]
  rw [heq]
  exact endpoint_axis_mass_lt_five_eighths _

theorem endpoint_axis_atoms_coefficient_lt_one
    (atoms : List (Frequency 3)) (w k : Frequency 3)
    (hw : ∀ x ∈ atoms, 0 < eval w x)
    (haxis : ∀ x ∈ atoms, ∃ n : ℕ, 0 < n ∧ x = axis n) (hk : k ≠ 0) :
    coefficient atoms w (endpointAtomWeight 3) 1 k < 1 := by
  have ha : ∀ x ∈ atoms, 0 ≤ endpointAtomWeight 3 x := by
    intro x _
    exact div_nonneg (endpointCoupling_pos (by norm_num : 0 < 3)).le
      (pow_nonneg (frequencyRadius_nonneg x) _)
  have hc := coefficient_le_exp_mass_sub_one atoms w (endpointAtomWeight 3) k hw ha hk
  have hm := endpoint_axis_atom_mass_lt_five_eighths atoms haxis
  have he := (Real.exp_lt_exp.mpr hm).trans exp_five_eighths_lt_two
  linarith

theorem sumVec_coordinate {d : ℕ} (xs : List (Vec d)) (j : Fin d) :
    sumVec xs j = (xs.map (fun x => x j)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sumVec, add, ih]

theorem coordinate_zero_of_nonneg_sum_zero {d : ℕ}
    (xs : List (Vec d)) (j : Fin d)
    (hpos : ∀ x ∈ xs, 0 ≤ x j) (hsum : sumVec xs j = 0) :
    ∀ x ∈ xs, x j = 0 := by
  rw [sumVec_coordinate] at hsum
  intro x hx
  apply List.all_zero_of_le_zero_le_of_sum_eq_zero (l := xs.map (fun x => x j)) ?_
    hsum (List.mem_map.mpr ⟨x, hx, rfl⟩)
  intro y hy
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
  exact hpos z hz

/-- For a positive-cone word with an axis output, its first two coordinates
vanish in every letter separately. No cancellation across positive leading
coordinates is possible. -/
theorem axis_word_zero_coordinates (xs : List (Frequency 3)) (n : ℕ)
    (hpos : ∀ x ∈ xs, LexPositive x) (hsum : sumVec xs = axis n) :
    ∀ x ∈ xs, x 0 = 0 ∧ x 1 = 0 := by
  have hsum0 : sumVec xs 0 = 0 := by rw [hsum]; simp [axis]
  have h0 := coordinate_zero_of_nonneg_sum_zero xs 0
    (fun x hx => positive_head_nonneg (hpos x hx)) hsum0
  have hsum1 : sumVec xs 1 = 0 := by rw [hsum]; simp [axis]
  have h1pos : ∀ x ∈ xs, 0 ≤ x 1 := by
    intro x hx
    have ht := positive_head_nonneg (positive_tail_of_head_zero (hpos x hx) (h0 x hx))
    exact ht
  have h1 := coordinate_zero_of_nonneg_sum_zero xs 1 h1pos hsum1
  exact fun x hx => ⟨h0 x hx, h1 x hx⟩

theorem positive_with_zero_coordinates_is_axis (k : Frequency 3)
    (hpos : LexPositive k) (h0 : k 0 = 0) (h1 : k 1 = 0) :
    ∃ n : ℕ, 0 < n ∧ k = axis n := by
  have h2 : 0 < k 2 := by
    obtain ⟨j, hj, _⟩ := hpos
    fin_cases j <;> simp_all
  refine ⟨(k 2).toNat, Int.pos_iff_toNat_pos.mp h2, ?_⟩
  funext j
  fin_cases j <;> simp [axis, h0, h1, Int.toNat_of_nonneg h2.le]

def axisAtoms (atoms : List (Frequency 3)) : List (Frequency 3) :=
  atoms.filter (fun k => decide (k 0 = 0 ∧ k 1 = 0))

theorem axisAtoms_subset (atoms : List (Frequency 3)) :
    ∀ k ∈ axisAtoms atoms, k ∈ atoms := by
  intro k hk
  exact (List.mem_filter.mp hk).1

theorem axisAtoms_are_positive_axis (atoms : List (Frequency 3))
    (hpos : ∀ k ∈ atoms, LexPositive k) :
    ∀ k ∈ axisAtoms atoms, ∃ n : ℕ, 0 < n ∧ k = axis n := by
  intro k hk
  have hm := List.mem_filter.mp hk
  have hc : k 0 = 0 ∧ k 1 = 0 := by simpa using hm.2
  exact positive_with_zero_coordinates_is_axis k (hpos k hm.1) hc.1 hc.2

/-- Exact equality of the full finite decomposition sets on the axis.
This is a structural restriction, not an estimate discarding positive terms. -/
theorem axis_decompositions_filter (atoms : List (Frequency 3)) (w : Frequency 3)
    (hw : ∀ x ∈ atoms, 0 < eval w x) (hpos : ∀ x ∈ atoms, LexPositive x) (n : ℕ) :
    decompositions atoms w (axis n) = decompositions (axisAtoms atoms) w (axis n) := by
  classical
  have hw' : ∀ x ∈ axisAtoms atoms, 0 < eval w x :=
    fun x hx => hw x (axisAtoms_subset atoms x hx)
  ext xs
  rw [mem_decompositions_iff atoms w (axis n) hw,
    mem_decompositions_iff (axisAtoms atoms) w (axis n) hw']
  constructor
  · rintro ⟨hm, hs⟩
    have hc := axis_word_zero_coordinates xs n (fun x hx => hpos x (hm x hx)) hs
    refine ⟨?_, hs⟩
    intro x hx
    exact List.mem_filter.mpr ⟨hm x hx, by simpa using hc x hx⟩
  · rintro ⟨hm, hs⟩
    exact ⟨fun x hx => axisAtoms_subset atoms x (hm x hx), hs⟩

theorem axis_coefficient_filter (atoms : List (Frequency 3)) (w : Frequency 3)
    (a : Frequency 3 → ℝ) (q : ℝ)
    (hw : ∀ x ∈ atoms, 0 < eval w x) (hpos : ∀ x ∈ atoms, LexPositive x) (n : ℕ) :
    coefficient atoms w a q (axis n) = coefficient (axisAtoms atoms) w a q (axis n) := by
  unfold coefficient
  rw [axis_decompositions_filter atoms w hw hpos n]

/-- The actual d=3 endpoint coefficient is strictly below one on every
positive third-axis output, for arbitrary finite positive-cone alphabets.
All constants and the axis restriction are proved in this module. -/
theorem endpoint_positive_axis_coefficient_lt_one
    (atoms : List (Frequency 3)) (w : Frequency 3)
    (hw : ∀ x ∈ atoms, 0 < eval w x) (hpos : ∀ x ∈ atoms, LexPositive x)
    (n : ℕ) (hn : 0 < n) :
    coefficient atoms w (endpointAtomWeight 3) 1 (axis n) < 1 := by
  rw [axis_coefficient_filter atoms w (endpointAtomWeight 3) 1 hw hpos n]
  apply endpoint_axis_atoms_coefficient_lt_one (axisAtoms atoms) w (axis n)
    (fun x hx => hw x (axisAtoms_subset atoms x hx)) (axisAtoms_are_positive_axis atoms hpos)
  intro he
  have h := congrFun he 2
  simp [axis] at h
  omega

end Legacy.TorusEndpoint.D3AxisCoefficient
