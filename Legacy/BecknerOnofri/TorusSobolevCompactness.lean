import Legacy.BecknerOnofri.TorusSobolevCoefficients

/-! Actual critical Fourier Sobolev balls on the unit torus have compact
closure in L². Weighted summability is part of Sobolev membership. -/

noncomputable section
open Set Filter MeasureTheory Legacy.TorusEndpoint
open scoped BigOperators Topology ENNReal

namespace Legacy.BecknerOnofri.TorusSobolev

def weightedSquare {d : ℕ} (u : Coefficients (Frequency d)) (k : Frequency d) : ℝ :=
  frequencyRadius k ^ d * ‖u k‖ ^ 2

def coefficientEnergy {d : ℕ} (u : Coefficients (Frequency d)) : ℝ := ∑' k, weightedSquare u k

def coefficientBall (d : ℕ) (B : ℝ) : Set (Coefficients (Frequency d)) :=
  {u | u 0 = 0 ∧ Summable (weightedSquare u) ∧ coefficientEnergy u ≤ B}

theorem weightedSquare_nonneg {d : ℕ} (u : Coefficients (Frequency d)) (k : Frequency d) :
    0 ≤ weightedSquare u k := mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (sq_nonneg _)

theorem coordinate_abs_le_radius {d : ℕ} (k : Frequency d) (i : Fin d) :
    |(k i : ℝ)| ≤ frequencyRadius k := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (fun j _ => sq_nonneg (k j : ℝ)) (Finset.mem_univ i))

theorem radius_one_le {d : ℕ} {k : Frequency d} (hk : k ≠ 0) : 1 ≤ frequencyRadius k := by
  have hr := GreenMultiplierSummability.radiusSq_one_le hk
  change 1 ≤ Real.sqrt (GreenMultiplierSummability.radiusSq k)
  exact (Real.le_sqrt (by norm_num) (by linarith)).mpr (by simpa using hr)

theorem radius_outside_box {d N : ℕ} (k : Frequency d)
    (hk : k ∉ SobolevLattice.latticeBox d N) : (N : ℝ) ≤ frequencyRadius k := by
  classical
  rw [SobolevLattice.mem_latticeBox] at hk
  push Not at hk
  obtain ⟨i, hi⟩ := hk
  have hc : (N : ℝ) < (k i).natAbs := by exact_mod_cast hi
  have habs : ((k i).natAbs : ℝ) = |(k i : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  exact (habs ▸ hc).le.trans (coordinate_abs_le_radius k i)

theorem coefficient_norm_sq_le_energy {d : ℕ} (u : Coefficients (Frequency d))
    (hzero : u 0 = 0) (hs : Summable (weightedSquare u)) : ‖u‖ ^ 2 ≤ coefficientEnergy u := by
  rw [norm_sq_eq_tsum]
  apply Summable.tsum_le_tsum _ (summable_sq u) hs
  intro k
  by_cases hk : k = 0
  · simp [hk, hzero, weightedSquare]
  · exact le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ (radius_one_le hk))

/-- The requested radial tail estimate, with all convergence proved. -/
theorem radial_tail_le {d : ℕ} (u : Coefficients (Frequency d))
    (hs : Summable (weightedSquare u)) {R : ℝ} (hR : 0 < R) :
    (∑' k, {k : Frequency d | R < frequencyRadius k}.indicator (fun k => ‖u k‖ ^ 2) k) ≤
      coefficientEnergy u / R^d := by
  classical
  rw [coefficientEnergy, ← tsum_div_const]
  apply Summable.tsum_le_tsum _ ((summable_sq u).indicator _) (hs.div_const _)
  intro k
  by_cases hk : R < frequencyRadius k
  · rw [indicator_of_mem (s := {k : Frequency d | R < frequencyRadius k}) hk]
    apply (le_div_iff₀ (pow_pos hR d)).mpr
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR.le hk.le d) (sq_nonneg _)
      |>.trans_eq (mul_comm _ _)
  · rw [indicator_of_notMem (s := {k : Frequency d | R < frequencyRadius k}) hk]
    exact div_nonneg (weightedSquare_nonneg u k) (pow_pos hR d).le

theorem projection_tail_le {d : ℕ} (u : Coefficients (Frequency d))
    (hs : Summable (weightedSquare u)) (s : Finset (Frequency d)) {R : ℝ} (hR : 0 < R)
    (houtside : ∀ k ∉ s, R ≤ frequencyRadius k) :
    ‖u - finiteProjection s u‖ ^ 2 ≤ coefficientEnergy u / R^d := by
  classical
  rw [norm_sq_eq_tsum, coefficientEnergy, ← tsum_div_const]
  apply Summable.tsum_le_tsum _ (summable_sq _) (hs.div_const _)
  intro k
  rw [lp.coeFn_sub, Pi.sub_apply, finiteProjection_apply]
  by_cases hk : k ∈ s
  · simp only [if_pos hk, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact div_nonneg (weightedSquare_nonneg u k) (pow_pos hR d).le
  · rw [if_neg hk, sub_zero]
    apply (le_div_iff₀ (pow_pos hR d)).mpr
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR.le (houtside k hk) d)
      (sq_nonneg _)).trans_eq (mul_comm _ _)

theorem coefficientBall_totallyBounded {d : ℕ} (hd : 0 < d) {B : ℝ} (hB : 0 ≤ B) :
    TotallyBounded (coefficientBall d B) := by
  apply totallyBounded_of_uniform_finite_tail _ (Real.sqrt B)
  · intro u hu
    exact (Real.le_sqrt (norm_nonneg _) hB).mpr
      ((coefficient_norm_sq_le_energy u hu.1 hu.2.1).trans hu.2.2)
  · intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (B / ε^2 + 1)
    have hN1 : (1 : ℝ) ≤ N := by have := div_nonneg hB (sq_nonneg ε); linarith
    have hN0 : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN1
    refine ⟨SobolevLattice.latticeBox d N, ?_⟩
    intro u hu
    have ht := projection_tail_le u hu.2.1 (SobolevLattice.latticeBox d N)
      hN0 (radius_outside_box (N := N))
    have hpow : (N : ℝ) ≤ (N : ℝ)^d := le_self_pow₀ hN1 hd.ne'
    have hdiv : coefficientEnergy u / (N : ℝ)^d ≤ B / N :=
      (div_le_div_of_nonneg_right hu.2.2 (pow_pos hN0 d).le).trans
        (div_le_div_of_nonneg_left hB hN0 hpow)
    have hsmall : B / (N : ℝ) < ε^2 := by
      apply (div_lt_iff₀ hN0).mpr
      have h' : B / ε^2 < (N : ℝ) := by linarith
      have := (div_lt_iff₀ (sq_pos_of_pos hε)).mp h'
      nlinarith
    have hsq := ht.trans hdiv
    nlinarith [norm_nonneg (u - finiteProjection (SobolevLattice.latticeBox d N) u)]

theorem mem_coefficientBall_iff {d : ℕ} (B : ℝ) (u : Coefficients (Frequency d)) :
    u ∈ coefficientBall d B ↔ u 0 = 0 ∧
      ∀ s : Finset (Frequency d), ∑ k ∈ s, weightedSquare u k ≤ B := by
  constructor
  · rintro ⟨hz, hs, hB⟩
    exact ⟨hz, fun s => (hs.sum_le_tsum s (fun k _ => weightedSquare_nonneg u k)).trans hB⟩
  · rintro ⟨hz, hs⟩
    exact ⟨hz, summable_of_sum_le (weightedSquare_nonneg u) hs,
      Real.tsum_le_of_sum_le (weightedSquare_nonneg u) hs⟩

theorem weightedSquare_continuous {d : ℕ} (k : Frequency d) :
    Continuous (fun u : Coefficients (Frequency d) => weightedSquare u k) :=
  (((lp.lipschitzWith_one_eval 2 k).continuous.norm).pow 2).const_mul _

theorem coefficientBall_isClosed (d : ℕ) (B : ℝ) : IsClosed (coefficientBall d B) := by
  have he : coefficientBall d B = {u : Coefficients (Frequency d) | u 0 = 0} ∩
      ⋂ s : Finset (Frequency d), {u | ∑ k ∈ s, weightedSquare u k ≤ B} := by
    ext u
    simp only [mem_coefficientBall_iff, mem_inter_iff, mem_setOf_eq, mem_iInter]
  rw [he]
  apply IsClosed.inter (isClosed_eq ((lp.lipschitzWith_one_eval 2 0).continuous) continuous_const)
  apply isClosed_iInter
  intro s
  apply isClosed_le _ continuous_const
  exact continuous_finsetSum _ (fun k hk => weightedSquare_continuous k)

/-- The mean-zero critical Sobolev coefficient ball is genuinely compact in ell². -/
theorem coefficientBall_isCompact {d : ℕ} (hd : 0 < d) {B : ℝ} (hB : 0 ≤ B) :
    IsCompact (coefficientBall d B) :=
  (coefficientBall_totallyBounded hd hB).isCompact_of_isComplete
    (coefficientBall_isClosed d B).isComplete

abbrev TorusL2 (d : ℕ) := Lp ℂ 2 (torusMeasure d)

/-- Mathlib's actual Fourier Hilbert basis, as a unitary map on the normalized torus. -/
def fourierIsometry (d : ℕ) : TorusL2 d ≃ₗᵢ[ℂ] Coefficients (Frequency d) :=
  UnitAddTorus.mFourierBasis.repr

theorem fourierIsometry_apply (d : ℕ) (u : TorusL2 d) (k : Frequency d) :
    fourierIsometry d u k = UnitAddTorus.mFourierCoeff u k :=
  UnitAddTorus.mFourierBasis_repr u k

/-- Standard mean-zero critical H^(d/2) membership. Divergent weighted spectra
are excluded explicitly. The frequencies use the unit-torus convention. -/
def CriticalSobolev {d : ℕ} (u : TorusL2 d) : Prop :=
  fourierIsometry d u 0 = 0 ∧ Summable (weightedSquare (fourierIsometry d u))

def criticalEnergy {d : ℕ} (u : TorusL2 d) : ℝ := coefficientEnergy (fourierIsometry d u)

def sobolevBall (d : ℕ) (B : ℝ) : Set (TorusL2 d) :=
  {u | CriticalSobolev u ∧ criticalEnergy u ≤ B}

theorem sobolevBall_isCompact {d : ℕ} (hd : 0 < d) {B : ℝ} (hB : 0 ≤ B) :
    IsCompact (sobolevBall d B) := by
  have he : sobolevBall d B = (fourierIsometry d).symm '' coefficientBall d B := by
    ext u
    constructor
    · rintro ⟨⟨hz, hs⟩, hE⟩
      exact ⟨fourierIsometry d u, ⟨hz, hs, hE⟩, (fourierIsometry d).symm_apply_apply u⟩
    · rintro ⟨v, hv, rfl⟩
      change (fourierIsometry d ((fourierIsometry d).symm v) 0 = 0 ∧
        Summable (weightedSquare (fourierIsometry d ((fourierIsometry d).symm v)))) ∧
        coefficientEnergy (fourierIsometry d ((fourierIsometry d).symm v)) ≤ B
      simpa only [LinearIsometryEquiv.apply_symm_apply] using ⟨⟨hv.1, hv.2.1⟩, hv.2.2⟩
  rw [he]
  exact (coefficientBall_isCompact hd hB).image (fourierIsometry d).symm.continuous

/-- Every energy-bounded mean-zero critical Sobolev sequence has an L²
convergent subsequence, whose limit retains the same weighted energy bound. -/
theorem exists_L2_convergent_subsequence {d : ℕ} (hd : 0 < d) {B : ℝ} (hB : 0 ≤ B)
    (u : ℕ → TorusL2 d) (hu : ∀ n, CriticalSobolev (u n) ∧ criticalEnergy (u n) ≤ B) :
    ∃ v : TorusL2 d, CriticalSobolev v ∧ criticalEnergy v ≤ B ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 v) := by
  obtain ⟨v, hv, φ, hφ, hlim⟩ := (sobolevBall_isCompact hd hB).isSeqCompact
    (fun n => hu n)
  exact ⟨v, hv.1, hv.2, φ, hφ, hlim⟩

#print axioms radial_tail_le
#print axioms coefficientBall_isCompact
#print axioms sobolevBall_isCompact
#print axioms exists_L2_convergent_subsequence

end Legacy.BecknerOnofri.TorusSobolev
