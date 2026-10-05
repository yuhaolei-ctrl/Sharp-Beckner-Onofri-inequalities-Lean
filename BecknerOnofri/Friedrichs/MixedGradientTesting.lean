import BecknerOnofri.Friedrichs.MixedTestIntegration
import BecknerOnofri.Friedrichs.MixedClosedFormTests

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff
namespace BecknerOnofri.Friedrichs.MixedSpatial

def testVector {d : ℕ} (α : MultiIndex d) {ψ : Space d → ℝ} (hψ : ContDiff ℝ ∞ ψ) : H α :=
  (continuous_memLp α hψ.continuous).toLp ψ

def testDerivativeVector {d : ℕ} (α : MultiIndex d) {ψ : Space d → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (i : Fin d) : H α :=
  (continuous_memLp α (partialDerivative_continuous hψ i)).toLp (partialDerivative i ψ)

lemma core_gradient_testing {d : ℕ} {α : MultiIndex d} {v : EnergySpace α}
    (hv : v∈core α) {ψ : Space d → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : tsupport ψ ⊆ openBox α) (i : Fin d) :
    inner ℝ (v.2.1 i) (testVector α hψ)= -inner ℝ v.1 (testDerivativeVector α hψ i) := by
  obtain ⟨F,hF,hv0,hv1,hvV⟩ := hv
  unfold testVector testDerivativeVector
  rw [inner_eq_integral_of_ae (hv1 i) (continuous_memLp α hψ.continuous).coeFn_toLp,
    inner_eq_integral_of_ae hv0 (continuous_memLp α (partialDerivative_continuous hψ i)).coeFn_toLp]
  exact mixed_test_integration α hF.1 hψ hs i

lemma closed_gradient_testing {d : ℕ} {α : MultiIndex d} {v : EnergySpace α}
    (hv : v∈formClosure α) {ψ : Space d → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : tsupport ψ ⊆ openBox α) (i : Fin d) :
    inner ℝ (v.2.1 i) (testVector α hψ)= -inner ℝ v.1 (testDerivativeVector α hψ i) := by
  have h1 : Continuous (fun v : EnergySpace α => inner ℝ (v.2.1 i) (testVector α hψ)) := by fun_prop
  have h2 : Continuous (fun v : EnergySpace α => -inner ℝ v.1 (testDerivativeVector α hψ i)) := by fun_prop
  exact closure_minimal (fun u hu => core_gradient_testing hu hψ hs i) (isClosed_eq h1 h2) hv

#print axioms closed_gradient_testing
end BecknerOnofri.Friedrichs.MixedSpatial
