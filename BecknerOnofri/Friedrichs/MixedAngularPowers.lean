import BecknerOnofri.Friedrichs.MixedAngularSeries
import BecknerOnofri.AngularRealPowerDomain

/-! Finite differentiated Chebyshev eigenfunctions and their rapidly converging
series lie in the actual mixed spectral-power graph. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators
namespace BecknerOnofri.Friedrichs.MixedAngularSeries
open Legacy.BecknerOnofri Legacy.TorusEndpoint
open TorusSobolev RadialWiener ChebyshevMixedSeries TensorPolynomialDerivatives AngularMixedTerms
open MixedSpatial

lemma angularTerm_eq_chebyshev {d : ℕ} (a : Frequency d → ℂ) (is : List (Fin d))
    (k : Frequency d) (x : Space d) :
    angularTerm a is k x=((a k).re*2^is.length)*
      angularFunction (countIndex is) (chebyshevProfiles (countIndex is) (fun i => (k i).natAbs)) x := by
  simp only [angularTerm,weight,term,unitTensor,angularCube_coordinate,angularFunction,
    productProfile,angularProfiles,JacobiAngular.angular,chebyshevProfiles,countIndex,
    iteratePolynomials,polynomials,Finset.prod_mul_distrib]
  ring

lemma termVector_eq_chebyshev {d : ℕ} (a : Frequency d → ℂ) (is : List (Fin d)) (k : Frequency d) :
    termVector a is k=((a k).re*2^is.length) • chebyshevVector (countIndex is) (fun i => (k i).natAbs) := by
  apply Lp.ext
  filter_upwards [termVector_ae a is k,
    Lp.coeFn_smul ((a k).re*2^is.length) (chebyshevVector (countIndex is) (fun i => (k i).natAbs)),
    (angular_memLp (countIndex is) (chebyshevProfiles (countIndex is) (fun i => (k i).natAbs))
      (chebyshevProfiles_smooth (countIndex is) (fun i => (k i).natAbs))).coeFn_toLp] with x hx hs hv
  change chebyshevVector (countIndex is) (fun i => (k i).natAbs) x=_ at hv
  rw [hx,hs]
  simpa only [Pi.smul_apply,smul_eq_mul,hv] using angularTerm_eq_chebyshev a is k x

lemma termVector_operatorGraph {d : ℕ} (a : Frequency d → ℂ) (is : List (Fin d)) (k : Frequency d) :
    operatorGraph (countIndex is) (termVector a is k) (frequencyRadius k^2 • termVector a is k) := by
  rw [termVector_eq_chebyshev]
  have he : (∑ i,((k i).natAbs:ℝ)^2)=frequencyRadius k^2 := by
    rw [GreenMultiplierSummability.frequencyRadius_sq]
    simp only [Nat.cast_natAbs,Int.cast_abs,sq_abs,GreenMultiplierSummability.radiusSq]
  have h := operatorGraph_smul (chebyshevVector_operatorGraph (countIndex is) (fun i => (k i).natAbs))
    ((a k).re*2^is.length)
  simpa only [he,smul_smul,mul_comm] using h

def powerCoefficients {d : ℕ} (s : ℝ) (a : Frequency d → ℂ) (k : Frequency d) : ℂ :=
  ((frequencyRadius k^(2*s):ℝ):ℂ)*a k

lemma termVector_powerCoefficients {d : ℕ} (s : ℝ) (a : Frequency d → ℂ)
    (is : List (Fin d)) (k : Frequency d) :
    termVector (powerCoefficients s a) is k=(frequencyRadius k^(2*s)) • termVector a is k := by
  rw [termVector_eq_chebyshev,termVector_eq_chebyshev,smul_smul]
  congr 1
  simp only [powerCoefficients,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

lemma termVector_powerGraph {d : ℕ} (s : ℝ) (a : Frequency d → ℂ)
    (is : List (Fin d)) (k : Frequency d) :
    SpectralPowerGraph (countIndex is) s (termVector a is k) (termVector (powerCoefficients s a) is k) := by
  rw [termVector_powerCoefficients]
  have he : (frequencyRadius k^2)^s=frequencyRadius k^(2*s) := by
    rw [← Real.rpow_natCast (frequencyRadius k) 2,← Real.rpow_mul (frequencyRadius_nonneg k)]
    norm_num
  simpa only [he] using spectralPowerGraph_eigenvector (termVector_operatorGraph a is k) s

theorem positive_intertwining {d : ℕ} (s : ℝ) (hs : 0≤s) (a : Frequency d → ℂ)
    (ha : ∀ m : ℕ,RadialSummable a m) (is : List (Fin d)) :
    SpectralPowerGraph (countIndex is) s (vector a is) (vector (powerCoefficients s a) is) := by
  apply spectralPowerGraph_hasSum _ _ (vector_hasSum a ha is)
    (vector_hasSum (powerCoefficients s a)
      (AngularRealPower.real_power_radialSummable (2*s) (by positivity) a ha) is)
  exact termVector_powerGraph s a is

#print axioms positive_intertwining
end BecknerOnofri.Friedrichs.MixedAngularSeries
