import BecknerOnofri.OnsetCompactness

/-! Quantitative polynomial Wiener estimates for actual Euler optimizers. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace BecknerOnofri.OnsetWienerBounds
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open TorusSobolev SubcriticalAttainment SubcriticalEuler WienerFourier WeightedWiener RadialWiener

def radialSize {d : ℕ} (m : ℕ) (a : Frequency d → ℂ) : ℝ :=
  ∑' k, radialWeight m k * ‖a k‖

theorem radialSize_nonneg {d : ℕ} (m : ℕ) (a : Frequency d → ℂ) : 0 ≤ radialSize m a :=
  tsum_nonneg (fun k => mul_nonneg ((radialWeight_isWeight m).nonneg k) (norm_nonneg _))

/-- The actual weighted exponential series has the usual Banach-algebra
exponential bound, proved directly from the positive convolution majorant. -/
theorem exponential_weighted_sum_le {d : ℕ} {w : Frequency d → ℝ} (hw : IsWeight w)
    (a : Frequency d → ℂ) (ha : Summable (fun k => w k * ‖a k‖)) :
    (∑' k, w k * ‖exponentialCoefficients a k‖) ≤ Real.exp (∑' k, w k * ‖a k‖) := by
  have hs := exponential_joint_norm_summable a (summable_norm hw ha)
  have hsW := exponential_joint_summable hw a ha
  have hp (k) : 0 ≤ w k * ‖a k‖ := mul_nonneg (hw.nonneg k) (norm_nonneg _)
  have hmajor := fourierExponential_hasSum (fun k => w k * ‖a k‖) ha hp
  rw [← hmajor.tsum_eq]
  apply Summable.tsum_le_tsum _ (exponential_summable hw a ha) hmajor.summable
  intro k
  calc
    _ ≤ w k * ∑' n, ‖(n.factorial : ℂ)⁻¹ * convolutionPower a n k‖ :=
      mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (hs.prod_symm.prod_factor k)) (hw.nonneg k)
    _ = ∑' n, w k * ‖(n.factorial : ℂ)⁻¹ * convolutionPower a n k‖ := tsum_mul_left.symm
    _ ≤ fourierExponential (fun k => w k * ‖a k‖) k := by
      apply Summable.tsum_le_tsum _ (hsW.prod_symm.prod_factor k)
        ((fourierExponential_joint_summable _ ha hp).prod_symm.prod_factor k)
      intro n
      simp only [Prod.swap, norm_mul, norm_inv, Complex.norm_natCast]
      calc
        _ = (n.factorial : ℝ)⁻¹ * (w k * ‖convolutionPower a n k‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (power_le hw a ha n k) (by positivity)

theorem gibbs_radialSize_le {d : ℕ} (u : TorusL2 d) (m : ℕ)
    (hu : RadialSummable (fourierIsometry d u) m) (hr : RealPotential u)
    (hZ : 1 ≤ partition u) :
    radialSize m (densityFourier (gibbsValue u)) ≤ Real.exp (radialSize m (fourierIsometry d u)) := by
  have hu0 := summable_norm (radialWeight_isWeight m) hu
  have hn : ‖(partition u : ℂ)‖ = partition u := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have he : radialSize m (densityFourier (gibbsValue u)) =
      (∑' k, radialWeight m k * ‖exponentialCoefficients (fourierIsometry d u) k‖) / partition u := by
    unfold radialSize gibbsValue
    simp only [normalized_real_exp_coefficient u hu0 hr, norm_div, hn, ← mul_div_assoc,
      tsum_div_const]
  rw [he]
  apply (div_le_self (tsum_nonneg (fun k =>
    mul_nonneg ((radialWeight_isWeight m).nonneg k) (norm_nonneg _))) hZ).trans
  exact exponential_weighted_sum_le (radialWeight_isWeight m) _ hu

theorem elliptic_radialSize_le {d : ℕ} {a b : Frequency d → ℂ} {c : ℝ} (hc : 0 < c)
    (ha0 : a 0 = 0)
    (he : ∀ k, k ≠ 0 → b k = ((c * frequencyRadius k^d : ℝ) : ℂ) * a k)
    (m : ℕ) (hb : RadialSummable b m) :
    radialSize (m+d) a ≤ ((2:ℝ)^d/c) * radialSize m b := by
  rw [radialSize, radialSize, ← tsum_mul_left]
  apply Summable.tsum_le_tsum _ (elliptic_step hc ha0 he m hb) (hb.mul_left _)
  intro k
  by_cases hk : k = 0
  · simp only [hk, ha0, norm_zero, mul_zero]
    exact mul_nonneg (by positivity) (mul_nonneg ((radialWeight_isWeight m).nonneg 0) (norm_nonneg _))
  · have hr := radius_one_le hk
    have hr0 := frequencyRadius_nonneg k
    have hp : (1+frequencyRadius k)^d ≤ (2:ℝ)^d * frequencyRadius k^d := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by linarith) (by linarith) d
    have hnorm : ‖b k‖ = c * frequencyRadius k^d * ‖a k‖ := by
      rw [he k hk, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    change (1+frequencyRadius k)^(m+d)*‖a k‖ ≤
      ((2:ℝ)^d/c)*((1+frequencyRadius k)^m*‖b k‖)
    rw [hnorm, pow_add]
    calc
      _ ≤ ((1+frequencyRadius k)^m*((2:ℝ)^d*frequencyRadius k^d))*‖a k‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp (by positivity)) (norm_nonneg _)
      _ = _ := by field_simp

theorem maximizer_partition_ge_one {d : ℕ} {b Ab A : ℝ}
    (hR : RoughExponentialBound d b Ab) (hA : 0 ≤ A) {u : TorusL2 d} (hu : Admissible u)
    (hmax : ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u) : 1 ≤ partition u := by
  have hz : 0 ≤ functional A u := by simpa using hmax 0 (admissible_zero d)
  have hn : 0 ≤ Real.log (partition u) := by
    unfold functional at hz
    linarith [mul_nonneg hA (energy_nonneg u)]
  exact (Real.one_le_exp_iff.mpr hn).trans_eq (Real.exp_log (partition_pos hR hu))

theorem maximizer_radialSize_step_le {d : ℕ} (hd : 0 < d) {b Ab A : ℝ}
    (hR : RoughExponentialBound d b Ab) (hA : (1/4:ℝ) ≤ A) {u : TorusL2 d} (hu : Admissible u)
    (hmax : ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u) (m : ℕ) :
    radialSize (m+d) (fourierIsometry d u) ≤
      (2:ℝ)^(d+1) * Real.exp (radialSize m (fourierIsometry d u)) := by
  have hA0 : 0 < A := by linarith
  have hs := maximizer_radialSummable hd hR hA0 hu hmax m
  have hg := gibbs_radialSummable u m hs hu.1 (partition u)
  have h := elliptic_radialSize_le (by positivity : 0 < 2*A) hu.2.1
    (fun _ hk => maximizer_fourier_equation hR hu hmax hk) m hg
  have hsize := gibbs_radialSize_le u m hs hu.1 (maximizer_partition_ge_one hR hA0.le hu hmax)
  have hc : (2:ℝ)^d/(2*A) ≤ (2:ℝ)^(d+1) := by
    apply (div_le_iff₀ (by positivity : 0 < 2*A)).mpr
    rw [pow_succ]
    nlinarith [pow_pos (by norm_num : (0:ℝ)<2) d]
  exact h.trans ((mul_le_mul_of_nonneg_left hsize (by positivity)).trans
    (mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le))

open GibbsL2Continuity GreenMultiplierSummability

def complexGibbsLp {d : ℕ} {b Ab B : ℝ} (hR : RoughExponentialBound d b Ab)
    (u : EnergyBall d B) : TorusL2 d :=
  Complex.ofRealCLM.compLpL 2 (torusMeasure d) (gibbsLp hR u)

theorem complexGibbsLp_fourier {d : ℕ} {b Ab B : ℝ} (hR : RoughExponentialBound d b Ab)
    (u : EnergyBall d B) (k : Frequency d) :
    fourierIsometry d (complexGibbsLp hR u) k = densityFourier (gibbsValue u.val) k := by
  rw [fourierIsometry_apply]
  apply integral_congr_ae
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL (gibbsLp hR u), gibbsLp_ae hR u] with x hx hg
  change UnitAddTorus.mFourier (-k) x * (complexGibbsLp hR u x) =
    UnitAddTorus.mFourier (-k) x * (gibbsValue u.val x : ℂ)
  rw [show complexGibbsLp hR u x = (gibbsLp hR u x : ℂ) from hx, hg]

theorem green_pairing_size_le {d : ℕ} (f : TorusL2 d) :
    (∑' k, ‖(greenMultiplier d k : ℂ) * fourierIsometry d f k‖) ≤
      ((∑' k, greenMultiplier d k ^ 2) + ‖f‖ ^ 2) / 2 := by
  have hsG := summable_greenMultiplier_sq d
  have hsF := summable_sq (fourierIsometry d f)
  have hsP : Summable (fun k => ‖(greenMultiplier d k : ℂ) * fourierIsometry d f k‖) := by
    simpa only [fourierIsometry_apply] using GreenPairing.summable_green_pairing_norm f
  calc
    _ ≤ ∑' k, (greenMultiplier d k ^ 2 + ‖fourierIsometry d f k‖ ^ 2) / 2 := by
      apply Summable.tsum_le_tsum _ hsP ((hsG.add hsF).div_const 2)
      intro k
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      nlinarith [sq_nonneg (|greenMultiplier d k| - ‖fourierIsometry d f k‖),
        sq_abs (greenMultiplier d k)]
    _ = _ := by
      rw [tsum_div_const, hsG.tsum_add hsF, ← norm_sq_eq_tsum, (fourierIsometry d).norm_map]

theorem exists_uniform_radialSize_zero_bound {d : ℕ} (hd : 0 < d) {b Ab B : ℝ}
    (hb : 0 < b) (hR : RoughExponentialBound d b Ab) (hB : 0 ≤ B) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (A : ℝ) (u : TorusL2 d), (1/4:ℝ) ≤ A →
      u ∈ realSobolevBall d B →
      (∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u) →
      radialSize 0 (fourierIsometry d u) ≤ M := by
  letI : CompactSpace (EnergyBall d B) :=
    isCompact_iff_compactSpace.mp (realSobolevBall_isCompact hd hB)
  have hc : Continuous (complexGibbsLp hR : EnergyBall d B → TorusL2 d) :=
    (Complex.ofRealCLM.compLpL 2 (torusMeasure d)).continuous.comp (gibbsLp_continuous hb hR)
  obtain ⟨K, hK, hBound⟩ := (isCompact_range hc).isBounded.exists_pos_norm_le
  let G : ℝ := ∑' k : Frequency d, greenMultiplier d k ^ 2
  have hG : 0 ≤ G := tsum_nonneg (fun k => sq_nonneg _)
  have hSigma : 0 < endpointSigma d := endpointSigma_pos hd
  let M := 2 * endpointSigma d * (G + K^2) / 2
  refine ⟨M, by dsimp [M]; positivity, ?_⟩
  intro A u hA huB hmax
  have hA0 : 0 < A := by linarith
  have hu : Admissible u := ⟨huB.2, huB.1.1⟩
  let uB : EnergyBall d B := ⟨u, huB⟩
  let F := complexGibbsLp hR uB
  have hF : ‖F‖ ≤ K := hBound F ⟨uB, rfl⟩
  have hcoef : endpointSigma d/(2*A) ≤ 2 * endpointSigma d := by
    apply (div_le_iff₀ (by positivity : 0 < 2*A)).mpr
    nlinarith
  have he : radialSize 0 (fourierIsometry d u) =
      (endpointSigma d/(2*A)) * ∑' k, ‖(greenMultiplier d k : ℂ) * fourierIsometry d F k‖ := by
    unfold radialSize
    simp only [radialWeight, pow_zero, one_mul, maximizer_fourier_green_formula hd hR hA0 hu hmax,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity : 0 ≤ endpointSigma d/(2*A))]
    simp only [F, complexGibbsLp_fourier hR uB, uB, tsum_mul_left]
  rw [he]
  have hg := green_pairing_size_le F
  calc
    _ ≤ (endpointSigma d/(2*A)) * ((G + ‖F‖^2)/2) :=
      mul_le_mul_of_nonneg_left hg (by positivity)
    _ ≤ (2 * endpointSigma d) * ((G + K^2)/2) := by
      apply mul_le_mul hcoef
      · gcongr
      · positivity
      · positivity
    _ = M := by dsimp [M]; ring

/-- Every fixed polynomial Wiener moment is uniformly bounded for all actual
global maximizers in a fixed critical-energy ball. -/
theorem exists_uniform_radialSize_bound {d : ℕ} (hd : 0 < d) {b Ab B : ℝ}
    (hb : 0 < b) (hR : RoughExponentialBound d b Ab) (hB : 0 ≤ B) (m : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (A : ℝ) (u : TorusL2 d), (1/4:ℝ) ≤ A →
      u ∈ realSobolevBall d B →
      (∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u) →
      radialSize m (fourierIsometry d u) ≤ M := by
  have hmultiple (n : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ (A : ℝ) (u : TorusL2 d), (1/4:ℝ) ≤ A →
      u ∈ realSobolevBall d B →
      (∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u) →
      radialSize (n*d) (fourierIsometry d u) ≤ M := by
    induction n with
    | zero => simpa only [zero_mul] using exists_uniform_radialSize_zero_bound hd hb hR hB
    | succ n ih =>
      obtain ⟨M, hM, hbound⟩ := ih
      refine ⟨(2:ℝ)^(d+1) * Real.exp M, by positivity, ?_⟩
      intro A u hA huB hmax
      have hu : Admissible u := ⟨huB.2, huB.1.1⟩
      rw [Nat.succ_mul]
      exact (maximizer_radialSize_step_le hd hR hA hu hmax (n*d)).trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hbound A u hA huB hmax)) (by positivity))
  obtain ⟨M, hM, hbound⟩ := hmultiple m
  refine ⟨M, hM, ?_⟩
  intro A u hA huB hmax
  have hu : Admissible u := ⟨huB.2, huB.1.1⟩
  have hmn : m ≤ m*d := by simpa using Nat.mul_le_mul_left m hd
  have hs := maximizer_radialSummable hd hR (by linarith : 0 < A) hu hmax (m*d)
  apply le_trans ?_ (hbound A u hA huB hmax)
  apply Summable.tsum_le_tsum _ (radialSummable_mono hmn hs) hs
  intro k
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact pow_le_pow_right₀ (by linarith [frequencyRadius_nonneg k]) hmn

#print axioms exponential_weighted_sum_le
#print axioms maximizer_radialSize_step_le
#print axioms exists_uniform_radialSize_bound
end BecknerOnofri.OnsetWienerBounds
