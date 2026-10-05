import Legacy.BecknerOnofri.SubcriticalPrimalDual
import Legacy.BecknerOnofri.SobolevLatticeBoxes
import Legacy.BecknerOnofri.WienerRepresentative

/-! Actual finite Fourier inverse potentials for arbitrary probability densities.
No L2 assumption on the density is used. -/
noncomputable section
open Set MeasureTheory Filter Classical
open scoped Topology BigOperators ComplexConjugate
namespace Legacy.BecknerOnofri.EndpointDensityFinitePotential
open Legacy.TorusEndpoint TorusSobolev SubcriticalAttainment SobolevDensityPairing

abbrev box (d N : ℕ) := SobolevLattice.latticeBox d N

theorem neg_mem_box {d N : ℕ} (k : Frequency d) : -k ∈ box d N ↔ k ∈ box d N := by
  simp only [SobolevLattice.mem_latticeBox, Pi.neg_apply, Int.natAbs_neg]

def inverseCoefficient {d : ℕ} (r : ProbabilityDensity d) (t : ℝ) (k : Frequency d) : ℂ :=
  (if k=0 then 0 else (t/frequencyRadius k^d : ℝ) : ℂ)*densityFourier r.value k

def coefficient {d : ℕ} (r : ProbabilityDensity d) (t : ℝ) (N : ℕ) (k : Frequency d) : ℂ :=
  if k ∈ box d N then inverseCoefficient r t k else 0

theorem coefficient_norm_summable {d : ℕ} (r : ProbabilityDensity d) (t : ℝ) (N : ℕ) :
    Summable (fun k => ‖coefficient r t N k‖) := by
  apply summable_of_ne_finset_zero (s := box d N)
  intro k hk
  simp [coefficient,hk]

theorem coefficient_neg {d : ℕ} (r : ProbabilityDensity d) (t : ℝ) (N : ℕ) (k : Frequency d) :
    coefficient r t N (-k) = conj (coefficient r t N k) := by
  by_cases hN : k ∈ box d N <;> by_cases hk : k=0 <;>
    simp [coefficient,neg_mem_box,inverseCoefficient,neg_eq_zero,hN,hk,densityFourier_neg]

def finiteFunction {d : ℕ} (r : ProbabilityDensity d) (t : ℝ) (N : ℕ) : Torus d → ℂ :=
  absoluteFourierSeries (coefficient r t N)

theorem finiteFunction_continuous {d : ℕ} (r : ProbabilityDensity d) (t : ℝ) (N : ℕ) :
    Continuous (finiteFunction r t N) :=
  absoluteFourierSeries_continuous _ (coefficient_norm_summable r t N)

theorem finiteFunction_real {d : ℕ} (r : ProbabilityDensity d) (t : ℝ) (N : ℕ) (x : Torus d) :
    (finiteFunction r t N x).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  change conj (∑' k, coefficient r t N k*UnitAddTorus.mFourier k x) = _
  rw [Complex.conj_tsum]
  calc
    _ = ∑' k : Frequency d, coefficient r t N (-k)*UnitAddTorus.mFourier (-k) x := by
      apply tsum_congr
      intro k
      rw [map_mul, coefficient_neg, UnitAddTorus.mFourier_neg]
    _ = _ := (Equiv.neg (Frequency d)).tsum_eq (fun k => coefficient r t N k*UnitAddTorus.mFourier k x)

theorem finiteFunction_memLp {d : ℕ} (r : ProbabilityDensity d) (t : ℝ) (N : ℕ) :
    MemLp (finiteFunction r t N) 2 (torusMeasure d) :=
  (finiteFunction_continuous r t N).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def finitePotential {d : ℕ} (r : ProbabilityDensity d) (t : ℝ) (N : ℕ) : TorusL2 d :=
  (finiteFunction_memLp r t N).toLp (finiteFunction r t N)

theorem finitePotential_ae {d : ℕ} (r : ProbabilityDensity d) (t : ℝ) (N : ℕ) :
    finitePotential r t N =ᵐ[torusMeasure d] finiteFunction r t N :=
  (finiteFunction_memLp r t N).coeFn_toLp

theorem finitePotential_fourier {d : ℕ} (r : ProbabilityDensity d) (t : ℝ) (N : ℕ) (k : Frequency d) :
    fourierIsometry d (finitePotential r t N) k = coefficient r t N k := by
  rw [fourierIsometry_apply]
  exact (WienerFourier.fourierCoeff_congr_ae (finitePotential_ae r t N) k).trans
    (absoluteFourierSeries_coefficient _ (coefficient_norm_summable r t N) k)

theorem weightedSquare_eq {d : ℕ} (r : ProbabilityDensity d) (t : ℝ) (N : ℕ) (k : Frequency d) :
    weightedSquare (fourierIsometry d (finitePotential r t N)) k =
      if k ∈ box d N then t^2*fullDensityTerm r k else 0 := by
  unfold weightedSquare
  rw [finitePotential_fourier]
  by_cases hN : k ∈ box d N
  · rw [if_pos hN]
    by_cases hk : k=0
    · simp [coefficient,inverseCoefficient,hk,fullDensityTerm]
    · have hw : frequencyRadius k^d ≠ 0 := (pow_pos (frequencyRadius_pos hk) _).ne'
      simp only [coefficient,if_pos hN,inverseCoefficient,if_neg hk,fullDensityTerm,
        norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs,div_pow]
      field_simp
  · simp [coefficient,hN]

theorem finitePotential_admissible {d : ℕ} (r : ProbabilityDensity d) (t : ℝ) (N : ℕ) :
    Admissible (finitePotential r t N) := by
  refine ⟨?_,?_,?_⟩
  · filter_upwards [finitePotential_ae r t N] with x hx
    rw [hx]
    exact finiteFunction_real r t N x
  · simp [finitePotential_fourier,coefficient,inverseCoefficient]
  · apply summable_of_ne_finset_zero (s := box d N)
    intro k hk
    simp only [weightedSquare_eq,if_neg hk]

def partialEnergy {d : ℕ} (r : ProbabilityDensity d) (N : ℕ) : ℝ :=
  ∑ k ∈ box d N, fullDensityTerm r k

theorem finitePotential_energy {d : ℕ} (r : ProbabilityDensity d) (t : ℝ) (N : ℕ) :
    criticalEnergy (finitePotential r t N) = t^2*partialEnergy r N := by
  simp only [criticalEnergy,coefficientEnergy,weightedSquare_eq]
  rw [tsum_eq_sum (s := box d N) (fun k hk => if_neg hk)]
  simp only [partialEnergy, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [if_pos hk]

theorem finiteFunction_eq_sum {d : ℕ} (r : ProbabilityDensity d) (t : ℝ) (N : ℕ) (x : Torus d) :
    finiteFunction r t N x = ∑ k ∈ box d N, coefficient r t N k*UnitAddTorus.mFourier k x := by
  apply tsum_eq_sum
  intro k hk
  simp [coefficient,hk]

theorem complex_pair_integrable {d : ℕ} (r : ProbabilityDensity d) (t : ℝ) (N : ℕ) :
    Integrable (fun x => finiteFunction r t N x*(r.value x : ℂ)) (torusMeasure d) := by
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn (finiteFunction_continuous r t N).continuousOn
  exact r.integrable.ofReal.bdd_mul (finiteFunction_continuous r t N).aestronglyMeasurable
    (ae_of_all _ (fun x => hB x (mem_univ x)))

theorem complex_pair_integral {d : ℕ} (r : ProbabilityDensity d) (t : ℝ) (N : ℕ) :
    (∫ x, finiteFunction r t N x*(r.value x : ℂ) ∂torusMeasure d) = (t*partialEnergy r N : ℂ) := by
  have hi (k : Frequency d) : Integrable (fun x => coefficient r t N k*
      (UnitAddTorus.mFourier k x*(r.value x : ℂ))) (torusMeasure d) := by
    simpa only [neg_neg] using (densityFourier_integrable r (-k)).const_mul (coefficient r t N k)
  simp_rw [finiteFunction_eq_sum, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum (box d N) (fun k _ => hi k)]
  simp only [integral_const_mul]
  have he (k : Frequency d) : (∫ x, UnitAddTorus.mFourier k x*(r.value x : ℂ) ∂torusMeasure d) =
      densityFourier r.value (-k) := by simp only [densityFourier,neg_neg]
  simp_rw [he]
  rw [partialEnergy, Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hkN
  by_cases hk : k=0
  · simp [coefficient,inverseCoefficient,hk,fullDensityTerm]
  · simp only [coefficient,if_pos hkN,inverseCoefficient,if_neg hk,densityFourier_neg,fullDensityTerm]
    rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring

theorem finitePotential_pair_integrable {d : ℕ} (r : ProbabilityDensity d) (t : ℝ) (N : ℕ) :
    Integrable (fun x => r.value x*(finitePotential r t N x).re) (torusMeasure d) := by
  apply (complex_pair_integrable r t N).re.congr
  filter_upwards [finitePotential_ae r t N] with x hx
  simp [hx,mul_comm]

theorem finitePotential_pairing {d : ℕ} (r : ProbabilityDensity d) (t : ℝ) (N : ℕ) :
    (∫ x, r.value x*(finitePotential r t N x).re ∂torusMeasure d) = t*partialEnergy r N := by
  calc
    _ = ∫ x, (finiteFunction r t N x*(r.value x : ℂ)).re ∂torusMeasure d := by
      apply integral_congr_ae
      filter_upwards [finitePotential_ae r t N] with x hx
      simp [hx,mul_comm]
    _ = _ := by
      change (∫ x, RCLike.re (finiteFunction r t N x*(r.value x : ℂ)) ∂torusMeasure d) = _
      rw [integral_re (complex_pair_integrable r t N),complex_pair_integral]
      simp

theorem fullTerm_nonnegative {d : ℕ} (r : ProbabilityDensity d) (k : Frequency d) :
    0 ≤ fullDensityTerm r k := by
  unfold fullDensityTerm
  split_ifs
  · exact le_rfl
  · exact div_nonneg (sq_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) _)

theorem fullTerm_hasSum {d : ℕ} (r : ProbabilityDensity d)
    (hQ : Summable (densitySpectralTerm r)) : HasSum (fullDensityTerm r) (fourierEnergy r) := by
  have hsupp : Function.support (fullDensityTerm r) ⊆ {k : Frequency d | k ≠ 0} := by
    intro k hk hk0
    subst k
    simp [fullDensityTerm] at hk
  apply (hasSum_subtype_iff_of_support_subset hsupp).1
  exact hQ.hasSum.congr_fun (fun k => by simp only [Function.comp_def,fullDensityTerm,if_neg k.property,densitySpectralTerm])

theorem box_tendsto (d : ℕ) : Tendsto (box d) atTop atTop := by
  apply tendsto_atTop.mpr
  intro S
  let N := S.sup (fun k => Finset.univ.sup (fun i : Fin d => (k i).natAbs))
  filter_upwards [eventually_ge_atTop N] with n hn
  intro k hk
  rw [SobolevLattice.mem_latticeBox]
  intro i
  have h1 : (k i).natAbs ≤ Finset.univ.sup (fun j : Fin d => (k j).natAbs) :=
    Finset.le_sup (f := fun j : Fin d => (k j).natAbs) (Finset.mem_univ i)
  have h2 : Finset.univ.sup (fun j : Fin d => (k j).natAbs) ≤ N :=
    Finset.le_sup (f := fun k : Frequency d => Finset.univ.sup (fun j : Fin d => (k j).natAbs)) hk
  exact h1.trans (h2.trans hn)

theorem partialEnergy_tendsto {d : ℕ} (r : ProbabilityDensity d)
    (hQ : Summable (densitySpectralTerm r)) :
    Tendsto (partialEnergy r) atTop (𝓝 (fourierEnergy r)) :=
  (fullTerm_hasSum r hQ).comp (box_tendsto d)

theorem partialEnergy_le {d : ℕ} (r : ProbabilityDensity d)
    (hQ : Summable (densitySpectralTerm r)) (N : ℕ) : partialEnergy r N ≤ fourierEnergy r := by
  rw [← (fullTerm_hasSum r hQ).tsum_eq]
  exact Summable.sum_le_tsum (box d N) (fun k _ => fullTerm_nonnegative r k) (fullTerm_hasSum r hQ).summable

theorem finitePotential_mem_ball {d : ℕ} (r : ProbabilityDensity d)
    (hQ : Summable (densitySpectralTerm r)) (t : ℝ) (N : ℕ) :
    finitePotential r t N ∈ realSobolevBall d (t^2*fourierEnergy r) := by
  have hu := finitePotential_admissible r t N
  refine ⟨⟨hu.2,?_⟩,hu.1⟩
  rw [finitePotential_energy]
  exact mul_le_mul_of_nonneg_left (partialEnergy_le r hQ N) (sq_nonneg t)

#print axioms finitePotential_admissible
#print axioms finitePotential_energy
#print axioms finitePotential_pairing
#print axioms partialEnergy_tendsto
end Legacy.BecknerOnofri.EndpointDensityFinitePotential
