import Legacy.BecknerOnofri.SubcriticalGibbs
import Legacy.TorusEndpoint.GreenKernelReal

/-! Actual real Fourier perturbations and exact finite-mode Sobolev energy variations. -/
noncomputable section
open MeasureTheory Legacy.TorusEndpoint Filter
open scoped BigOperators ComplexConjugate ENNReal
namespace Legacy.BecknerOnofri.SubcriticalEuler
open TorusSobolev SubcriticalAttainment

theorem summable_weightedSquare_add_single {d : ℕ} (c : Coefficients (Frequency d))
    (hc : Summable (weightedSquare c)) (k : Frequency d) (z : ℂ) :
    Summable (weightedSquare (c+lp.single 2 k z)) := by
  classical
  apply hc.congr_cofinite
  filter_upwards [eventually_cofinite_ne k] with j hj
  simp [weightedSquare, lp.single_apply, Pi.single_eq_of_ne hj]

theorem energy_add_single {d : ℕ} (c : Coefficients (Frequency d))
    (hc : Summable (weightedSquare c)) (k : Frequency d) (z : ℂ) :
    coefficientEnergy (c+lp.single 2 k z) = coefficientEnergy c +
      frequencyRadius k^d*(‖c k+z‖^2-‖c k‖^2) := by
  classical
  have hs := summable_weightedSquare_add_single c hc k z
  have he : (fun j => if j=k then 0 else weightedSquare (c+lp.single 2 k z) j) =
      (fun j => if j=k then 0 else weightedSquare c j) := by
    funext j
    by_cases hj : j=k
    · simp [hj]
    · simp [hj, weightedSquare, lp.single_apply]
  unfold coefficientEnergy
  rw [hs.tsum_eq_add_tsum_ite k, hc.tsum_eq_add_tsum_ite k, he]
  simp only [weightedSquare, lp.coeFn_add, Pi.add_apply, lp.single_apply, Pi.single_eq_same]
  ring

def characterLp {d : ℕ} (k : Frequency d) : TorusL2 d := UnitAddTorus.mFourierBasis k

def mode {d : ℕ} (k : Frequency d) (z : ℂ) : TorusL2 d :=
  z • characterLp k + conj z • characterLp (-k)

theorem fourier_mode {d : ℕ} (k : Frequency d) (z : ℂ) :
    fourierIsometry d (mode k z) = lp.single 2 k z + lp.single 2 (-k) (conj z) := by
  classical
  have hb (j : Frequency d) : fourierIsometry d (characterLp j) = lp.single 2 j 1 := by
    exact (UnitAddTorus.mFourierBasis (d := Fin d)).repr_self j
  unfold mode
  rw [map_add, map_smul, map_smul, hb, hb]
  simp only [← lp.single_smul, smul_eq_mul, mul_one]

theorem mode_coe {d : ℕ} (k : Frequency d) (z : ℂ) :
    (fun x => mode k z x) =ᵐ[torusMeasure d]
      (fun x => z*UnitAddTorus.mFourier k x+conj z*UnitAddTorus.mFourier (-k) x) := by
  have hb (j : Frequency d) : (fun x => characterLp j x) =ᵐ[torusMeasure d]
      (fun x => UnitAddTorus.mFourier j x) := by
    unfold characterLp
    rw [UnitAddTorus.coe_mFourierBasis]
    exact ContinuousMap.coeFn_toLp (torusMeasure d) (UnitAddTorus.mFourier j)
  filter_upwards [Lp.coeFn_add (z • characterLp k)
      (conj z • characterLp (-k)),
    Lp.coeFn_smul z (characterLp k : TorusL2 d),
    Lp.coeFn_smul (conj z) (characterLp (-k) : TorusL2 d), hb k, hb (-k)]
    with x hadd hsm hsn hk hn
  change (mode k z) x = (z • characterLp k : TorusL2 d) x +
    (conj z • characterLp (-k) : TorusL2 d) x at hadd
  change (z • characterLp k : TorusL2 d) x = z*(characterLp k : TorusL2 d) x at hsm
  change (conj z • characterLp (-k) : TorusL2 d) x = conj z*(characterLp (-k) : TorusL2 d) x at hsn
  rw [hadd, hsm, hsn, hk, hn]

theorem mode_real {d : ℕ} (k : Frequency d) (z : ℂ) : RealPotential (mode k z) := by
  filter_upwards [mode_coe k z] with x hx
  rw [hx, UnitAddTorus.mFourier_neg]
  simp only [← map_mul, Complex.add_im, Complex.conj_im]
  ring

theorem mode_criticalSobolev {d : ℕ} {k : Frequency d} (hk : k ≠ 0) (z : ℂ) :
    CriticalSobolev (mode k z) := by
  classical
  rw [CriticalSobolev, fourier_mode]
  constructor
  · simp [lp.single_apply, hk]
  · have hzero : Summable (weightedSquare (0 : Coefficients (Frequency d))) := by
      have he : weightedSquare (0 : Coefficients (Frequency d)) = (fun _ => 0) := by
        funext j
        change frequencyRadius j^d*‖(0:ℂ)‖^2=0
        simp
      rw [he]
      exact summable_zero
    simpa only [zero_add] using summable_weightedSquare_add_single _
      (summable_weightedSquare_add_single 0 hzero k z) (-k) (conj z)

theorem realPotential_star_eq {d : ℕ} {u : TorusL2 d} (hu : RealPotential u) : star u = u := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star u, hu] with x hx him
  rw [hx]
  apply Complex.ext <;> simp [him]

theorem fourier_real_symmetry {d : ℕ} {u : TorusL2 d} (hu : RealPotential u) (k : Frequency d) :
    fourierIsometry d u (-k) = conj (fourierIsometry d u k) := by
  have hh := GreenKernelReal.fourierCoeff_star u (-k)
  rw [realPotential_star_eq hu, neg_neg] at hh
  simpa only [fourierIsometry_apply] using hh

def perturb {d : ℕ} (u : TorusL2 d) (k : Frequency d) (z : ℂ) (t : ℝ) : TorusL2 d :=
  u + (t : ℂ) • mode k z

theorem fourier_perturb {d : ℕ} (u : TorusL2 d) (k : Frequency d) (z : ℂ) (t : ℝ) :
    fourierIsometry d (perturb u k z t) =
      fourierIsometry d u + lp.single 2 k ((t : ℂ)*z) + lp.single 2 (-k) ((t : ℂ)*conj z) := by
  classical
  unfold perturb
  rw [map_add, map_smul, fourier_mode, smul_add]
  simp only [← lp.single_smul, smul_eq_mul, add_assoc]

theorem perturb_coe {d : ℕ} (u : TorusL2 d) (k : Frequency d) (z : ℂ) (t : ℝ) :
    (fun x => perturb u k z t x) =ᵐ[torusMeasure d]
      (fun x => u x+(t : ℂ)*mode k z x) := by
  filter_upwards [Lp.coeFn_add u ((t : ℂ) • mode k z), Lp.coeFn_smul (t : ℂ) (mode k z)] with x ha hs
  simp only [perturb, ha, hs, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

theorem perturb_admissible {d : ℕ} {u : TorusL2 d} (hu : Admissible u)
    {k : Frequency d} (hk : k ≠ 0) (z : ℂ) (t : ℝ) : Admissible (perturb u k z t) := by
  classical
  constructor
  · filter_upwards [perturb_coe u k z t, hu.1, mode_real k z] with x hx hi hm
    simp only [hx, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hi, hm]
    ring
  · rw [CriticalSobolev, fourier_perturb]
    constructor
    · simp [hu.2.1, lp.single_apply, hk]
    · exact summable_weightedSquare_add_single _ (summable_weightedSquare_add_single _ hu.2.2 k _) (-k) _

theorem energy_perturb {d : ℕ} {u : TorusL2 d} (hu : Admissible u)
    {k : Frequency d} (hk : k ≠ 0) (z : ℂ) (t : ℝ) :
    criticalEnergy (perturb u k z t) = criticalEnergy u +
      4*t*frequencyRadius k^d*((fourierIsometry d u k)*conj z).re +
      2*t^2*frequencyRadius k^d*‖z‖^2 := by
  classical
  have hnk : -k ≠ k := fun he => hk (neg_eq_self.mp he)
  unfold criticalEnergy
  rw [fourier_perturb, energy_add_single _ (summable_weightedSquare_add_single _ hu.2.2 k _),
    energy_add_single _ hu.2.2, frequencyRadius_neg]
  simp only [lp.coeFn_add, Pi.add_apply, lp.single_apply, Pi.single_eq_of_ne hnk, add_zero]
  rw [fourier_real_symmetry hu.1]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

#print axioms energy_perturb
#print axioms perturb_admissible
end Legacy.BecknerOnofri.SubcriticalEuler
