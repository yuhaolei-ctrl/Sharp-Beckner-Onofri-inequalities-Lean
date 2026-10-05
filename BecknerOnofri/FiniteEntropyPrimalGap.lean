module

public import BecknerOnofri.FiniteEntropyDualGap

@[expose] public section

/-! Fourier square completion and the literal potential-side gap identity. -/
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace BecknerOnofri.FiniteEntropyGreen
open Legacy.TorusEndpoint Legacy.BecknerOnofri TorusSobolev
open SubcriticalAttainment SubcriticalEuler SubcriticalPrimalDual SobolevDensityPairing

lemma complex_square_completion (z v : ℂ) (t w : ℝ) (hw : w ≠ 0) :
    w*‖z-((t/w : ℝ):ℂ)*v‖^2 =
      w*‖z‖^2+t^2*(‖v‖^2/w)-2*t*(conj z*v).re := by
  simp only [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,Complex.sub_re,
    Complex.sub_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.conj_re,Complex.conj_im,mul_zero,zero_mul,sub_zero,add_zero]
  field_simp
  <;> ring

lemma square_completion {d : ℕ} (hd : 0 < d) (u : TorusL2 d) (hu : Admissible u)
    (r : ProbabilityDensity d) (hr : r.FiniteEntropy)
    (hr2 : MemLp r.value 2 (torusMeasure d)) (t : ℝ) :
    criticalEnergy (u-(t:ℂ) • potentialLp hd r hr) =
      criticalEnergy u+t^2*fourierEnergy r-
        2*t*(∫ x,r.value x*(u x).re ∂torusMeasure d) := by
  have hs := (hu.2.2.hasSum.add ((fullTerm_hasSum hd r hr).mul_left (t^2))).sub
    ((hasSum_pairing u r hr2).mul_left (2*t))
  have he (k : Frequency d) :
      weightedSquare (fourierIsometry d (u-(t:ℂ) • potentialLp hd r hr)) k =
        weightedSquare (fourierIsometry d u) k+t^2*fullDensityTerm r k-
          2*t*(conj (fourierIsometry d u k)*densityFourier r.value k).re := by
    simp only [weightedSquare,map_sub,map_smul,lp.coeFn_sub,lp.coeFn_smul,
      Pi.sub_apply,Pi.smul_apply,smul_eq_mul,potentialLp_fourier]
    by_cases hk : k = 0
    · simp [hk,weightedSquare,hu.2.1,fullDensityTerm]
    · have hw : frequencyRadius k^d ≠ 0 := (pow_pos (frequencyRadius_pos hk) d).ne'
      simp only [weightedSquare,fullDensityTerm,if_neg hk]
      have hmul : (t:ℂ)*((1/frequencyRadius k^d:ℝ):ℂ)*densityFourier r.value k =
          ((t/frequencyRadius k^d:ℝ):ℂ)*densityFourier r.value k := by push_cast; ring
      rw [← mul_assoc,hmul]
      exact complex_square_completion _ _ _ _ hw
  have ht := hs.congr_fun (fun k => he k)
  exact ht.tsum_eq

/-- Gibbs equality followed by the exact Fourier square completion. -/
theorem primal_gap_identity {d : ℕ} (hd : 0 < d) {b Ab A : ℝ}
    (hR : RoughExponentialBound d b Ab) (hA : 0 < A)
    (u : TorusL2 d) (hu : Admissible u) :
    functional A u = densityFunctional A (gibbsDensity hR hu) -
      A*criticalEnergy (u-dualPotential hd A (gibbsDensity hR hu)
        (gibbsDensity_finiteEntropy hR hu)) := by
  have hs := square_completion hd u hu (gibbsDensity hR hu)
    (gibbsDensity_finiteEntropy hR hu) (gibbsValue_memLp_two hR hu) (1/(2*A))
  change criticalEnergy (u-dualPotential hd A (gibbsDensity hR hu)
    (gibbsDensity_finiteEntropy hR hu)) = _ at hs
  rw [hs,functional,densityFunctional]
  change _ = _-densityEntropy (gibbsValue u)-_
  rw [gibbsDensity_entropy hR hu]
  change Real.log (partition u)-A*criticalEnergy u =
    (1/(4*A))*fourierEnergy (gibbsDensity hR hu)-
      ((∫ x,gibbsValue u x*(u x).re ∂torusMeasure d)-Real.log (partition u))-
      A*(criticalEnergy u+(1/(2*A))^2*fourierEnergy (gibbsDensity hR hu)-
        2*(1/(2*A))*(∫ x,gibbsValue u x*(u x).re ∂torusMeasure d))
  field_simp
  <;> ring

#print axioms square_completion
#print axioms primal_gap_identity
end BecknerOnofri.FiniteEntropyGreen
