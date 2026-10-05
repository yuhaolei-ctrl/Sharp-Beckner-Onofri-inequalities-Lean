module

public import Legacy.BecknerOnofri.EndpointPotential
public import Legacy.BecknerOnofri.SobolevCentering
public import Legacy.TorusEndpoint.EndpointSymbolNormalization

@[expose] public section

/-! The precise potential form from the manuscript, for every real critical
Sobolev function, with its actual mean removed and its (2π|k|)^d energy. -/
noncomputable section
open MeasureTheory Legacy.TorusEndpoint
open scoped BigOperators
namespace Legacy.BecknerOnofri.EndpointPotential
open TorusSobolev SubcriticalAttainment SobolevCentering

def centeredPartition {d : ℕ} (u : TorusL2 d) : ℝ :=
  ∫ x, Real.exp ((u x).re - ∫ y, (u y).re ∂torusMeasure d) ∂torusMeasure d

def manuscriptEnergy {d : ℕ} (u : TorusL2 d) : ℝ :=
  ∑' k : NonzeroFrequency d, (2*Real.pi*frequencyRadius k.val)^d * ‖fourierIsometry d u k.val‖^2

theorem manuscriptEnergy_eq {d : ℕ} (hd : 0 < d) (u : TorusL2 d)
    (hs : Summable (weightedSquare (fourierIsometry d u))) :
    manuscriptEnergy u = (2*Real.pi)^d * criticalEnergy u := by
  have hsupp : Function.support (weightedSquare (fourierIsometry d u)) ⊆ {k : Frequency d | k ≠ 0} := by
    intro k hk hzero
    subst k
    simp [weightedSquare,frequencyRadius,hd.ne'] at hk
  have hsum : HasSum (fun k : NonzeroFrequency d => weightedSquare (fourierIsometry d u) k.val) (criticalEnergy u) :=
    (hasSum_subtype_iff_of_support_subset hsupp).2 hs.hasSum
  have he (k : NonzeroFrequency d) : (2*Real.pi*frequencyRadius k.val)^d * ‖fourierIsometry d u k.val‖^2 =
      (2*Real.pi)^d * weightedSquare (fourierIsometry d u) k.val := by
    rw [mul_pow]
    unfold weightedSquare
    ring
  unfold manuscriptEnergy
  simp_rw [he]
  rw [tsum_mul_left,hsum.tsum_eq]

theorem coefficient_manuscript {d : ℕ} (hd : 0 < d) (u : TorusL2 d)
    (hs : Summable (weightedSquare (fourierIsometry d u))) :
    coefficient d * criticalEnergy u =
      (1/(4*(d:ℝ)*endpointSymbolConstant d))*manuscriptEnergy u := by
  rw [manuscriptEnergy_eq hd u hs,← endpointSymbolConstant_mul_sigma hd]
  unfold coefficient endpointConstant
  field_simp [(endpointSymbolConstant_pos hd).ne']

theorem centeredPartition_eq {d : ℕ} (u : TorusL2 d) : centeredPartition u = partition (center u) := by
  apply integral_congr_ae
  filter_upwards [center_real_ae u] with x hx
  exact congrArg Real.exp hx.symm

/-- No mean-zero or exponential-integrability assumption is imposed: real L2
membership and summability of the actual critical Fourier energy suffice. -/
theorem onofri_centered {d : ℕ} (hd : 0 < d) (hE : Endpoint d) {u : TorusL2 d}
    (hr : RealPotential u) (hs : Summable (weightedSquare (fourierIsometry d u))) :
    Integrable (fun x => Real.exp ((u x).re - ∫ y, (u y).re ∂torusMeasure d)) (torusMeasure d) ∧
      Real.log (centeredPartition u) ≤ coefficient d * criticalEnergy u := by
  have h := onofri hd hE (center_admissible hd hr hs)
  refine ⟨h.1.congr ?_,?_⟩
  · filter_upwards [center_real_ae u] with x hx
    exact congrArg Real.exp hx
  · rw [centeredPartition_eq,← center_energy hd u]
    exact h.2

/-- Exact manuscript energy and coefficient convention. -/
theorem manuscript_onofri {d : ℕ} (hd : 0 < d) (hE : Endpoint d) {u : TorusL2 d}
    (hr : RealPotential u) (hs : Summable (weightedSquare (fourierIsometry d u))) :
    Integrable (fun x => Real.exp ((u x).re - ∫ y, (u y).re ∂torusMeasure d)) (torusMeasure d) ∧
      Real.log (centeredPartition u) ≤
        (1/(4*(d:ℝ)*endpointSymbolConstant d))*manuscriptEnergy u := by
  simpa only [coefficient_manuscript hd u hs] using onofri_centered hd hE hr hs

#print axioms manuscript_onofri
#print axioms coefficient_manuscript
end Legacy.BecknerOnofri.EndpointPotential
