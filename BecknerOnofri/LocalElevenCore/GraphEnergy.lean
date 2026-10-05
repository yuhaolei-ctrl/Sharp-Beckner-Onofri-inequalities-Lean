module

public import BecknerOnofri.LocalElevenContinuousInverse
public import BecknerOnofri.GraphEnergy
public import BecknerOnofri.LocalElevenCore.GraphCritical
public import BecknerOnofri.QuadraticPairing
public import BecknerOnofri.ContinuousVariations

@[expose] public section

/-! Exact physical Fourier energy on the actual projected Gibbs graph. -/
noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace BecknerOnofri.HighDim.LocalEleven.GraphEnergy

open BecknerOnofri.HighDim.GraphEnergy hiding assembly_square_mean complement_fourier_euler graph_dualFunctional graph_energy_term graph_normalizedEnergy_hasSum graph_normalizedPotentialEnergy graph_potentialEnergy hasSum_pairing hasSum_square
open BecknerOnofri.HighDim.GreenCritical hiding coefficient_square_summable green_inCriticalSobolev nonzero_eigenvalue_ge_one potentialTerm_green
open BecknerOnofri.HighDim.QuadraticModes
open ContinuousGibbs ContinuousFirstShell ContinuousComplement QuadraticModes GreenCritical

open Legacy.BecknerOnofri.TorusSobolev

/-- Parseval for the actual real continuous Haar pairing. -/
theorem hasSum_pairing {d : ℕ} (f g : Space d) :
    HasSum (fun k : Frequency d => (conj (coefficient k f) * coefficient k g).re)
      (mean d (f*g)) := by
  have hh := UnitAddTorus.hasSum_prod_mFourierCoeff (toL2 d f) (toL2 d g)
  have hr := Complex.hasSum_re hh
  change HasSum (fun k : Frequency d =>
      (conj (UnitAddTorus.mFourierCoeff (toL2 d f) k) * UnitAddTorus.mFourierCoeff (toL2 d g) k).re)
      ((∫ x, conj (toL2 d f x)*toL2 d g x ∂torusMeasure d).re) at hr
  have hi : Integrable (fun x => conj (toL2 d f x)*toL2 d g x) (torusMeasure d) :=
    (Lp.memLp (toL2 d f)).star.integrable_mul (Lp.memLp (toL2 d g))
  have he : (∫ x, conj (toL2 d f x)*toL2 d g x ∂torusMeasure d).re = mean d (f*g) := by
    calc
      _ = ∫ x, (conj (toL2 d f x)*toL2 d g x).re ∂torusMeasure d := (integral_re hi).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [toL2_ae f, toL2_ae g] with x hf hg
        simp only [hf, hg, Complex.mul_re, Complex.conj_re, Complex.conj_im,
          Complex.ofReal_re, Complex.ofReal_im, neg_zero, mul_zero, sub_zero, ContinuousMap.mul_apply]
  rw [he] at hr
  simpa only [coefficient_apply, fourierIsometry_apply] using hr

private theorem conj_mul_self_re (z : ℂ) : (conj z*z).re = ‖z‖^2 := by
  rw [← Complex.normSq_eq_conj_mul_self]
  simp only [Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem hasSum_square {d : ℕ} (f : Space d) :
    HasSum (fun k : Frequency d => ‖coefficient k f‖^2) (mean d (f^2)) := by
  simpa only [conj_mul_self_re, ← pow_two] using hasSum_pairing f f

theorem assembly_square_mean {d : ℕ} (z : Coordinates d) :
    mean d ((assembly d z)^2) = 2 * ∑ i : Fin d, ‖z i‖^2 := by
  rw [pow_two, ← pairing_apply]
  rw [show pairing (assembly d z) (assembly d z) =
    pairing (assembly d z) (∑ i, synthesis (axisFrequency i) (z i)) from
      congrArg (pairing (assembly d z)) (assembly_apply z), map_sum]
  have hc (i : Fin d) : coefficient (axisFrequency i) (assembly d z) = z i := by
    exact congrFun (coordinates_assembly z) i
  simp only [pairing_synthesis, hc, conj_mul_self_re, ← Finset.mul_sum]

/-- The actual complement equation forces its Fourier Euler equation. -/
theorem complement_fourier_euler {d : ℕ} (hd : 0 < d) (μ : ℝ) (z : Coordinates d)
    (w : complement d) (he : projectedEquation (greenContinuous d) ((μ,z),w) = 0)
    (k : Frequency d) (hk : ComplementFrequency k) :
    ((frequencyLength k^d : ℝ) : ℂ) * coefficient k (w : Space d) =
      (μ : ℂ) * coefficient k (normalized (reconstruction d (z,w))) := by
  let N := normalized (reconstruction d (z,w))
  have hw : w = μ • complementMap d (greenContinuous d (N-1)) := sub_eq_zero.mp he
  have hc := congrArg (fun v : complement d => coefficient k (v : Space d)) hw
  simp only [Submodule.coe_smul, map_smul] at hc
  rw [complementMap_coefficient, if_pos hk, coefficient_green hd, if_neg hk.1, map_sub] at hc
  have hone : coefficient k (1 : Space d) = 0 := by
    change coefficient k (ContinuousMap.const (Torus d) 1) = 0
    rw [coefficient_const, if_neg hk.1]
  rw [hone, sub_zero] at hc
  have hlam : frequencyLength k^d ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (nonzero_eigenvalue_ge_one ⟨k,hk.1⟩)).ne'
  rw [hc]
  change ((frequencyLength k^d : ℝ) : ℂ) *
    ((μ : ℂ) * (((1 / frequencyLength k^d : ℝ) : ℂ) * coefficient k N)) =
      (μ : ℂ) * coefficient k N
  have hinv : ((frequencyLength k^d : ℝ) : ℂ) *
      ((1 / frequencyLength k^d : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul]
    simp [hlam]
  calc
    _ = (μ : ℂ) * ((((frequencyLength k^d : ℝ) : ℂ) *
      ((1 / frequencyLength k^d : ℝ) : ℂ)) * coefficient k N) := by ring
    _ = _ := by rw [hinv, one_mul]

private theorem weighted_norm_pairing {a b : ℂ} {lam μ : ℝ}
    (he : (lam:ℂ)*a = (μ:ℂ)*b) : lam*‖a‖^2 = μ*(conj a*b).re := by
  have hh := congrArg Complex.re (congrArg (fun q : ℂ => conj a*q) he)
  have hl : conj a*((lam:ℂ)*a) = (lam:ℂ)*(conj a*a) := by ring
  have hr : conj a*((μ:ℂ)*b) = (μ:ℂ)*(conj a*b) := by ring
  rw [hl, hr] at hh
  rw [← Complex.normSq_eq_conj_mul_self] at hh
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.normSq_eq_norm_sq] using hh

theorem graph_energy_term {d : ℕ} (hd : 0 < d) (μ : ℝ) (z : Coordinates d)
    (w : complement d) (he : projectedEquation (greenContinuous d) ((μ,z),w) = 0)
    (k : Frequency d) :
    frequencyLength k^d * ‖coefficient k (reconstruction d (z,w))‖^2 =
      ‖coefficient k (assembly d z)‖^2 +
        μ * (conj (coefficient k (w : Space d)) * coefficient k (normalized (reconstruction d (z,w)))).re := by
  by_cases hk : ComplementFrequency k
  · have hs : coefficient k (assembly d z) = 0 := by
      rw [← projection_assembly z]
      exact coefficient_projection_off_shell _ _ hk.2
    simp only [reconstruction_apply, map_add, hs, zero_add, norm_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0)]
    exact weighted_norm_pairing (complement_fourier_euler hd μ z w he k hk)
  · have hw : coefficient k (w : Space d) = 0 :=
      (mem_complement_fourier_iff (w : Space d)).mp w.property k hk
    simp only [reconstruction_apply, map_add, hw, add_zero, map_zero, zero_mul, Complex.zero_re,
      mul_zero, add_zero]
    by_cases hk0 : k = 0
    · subst k
      rw [coefficient_zero, mean_assembly]
      simp
    · have hs : InFirstShell k := Classical.byContradiction (fun hs => hk ⟨hk0,hs⟩)
      have hlam : frequencyLength k^d = 1 := by
        rw [frequencyLength_pow_eq, (latticeSquare_eq_one_iff k).mpr hs]
        simp
      rw [hlam, one_mul]

/-- The whole actual weighted Fourier series, including its convergence. -/
theorem graph_normalizedEnergy_hasSum {d : ℕ} (hd : 0 < d) (μ : ℝ) (z : Coordinates d)
    (w : complement d) (he : projectedEquation (greenContinuous d) ((μ,z),w) = 0) :
    HasSum (fun k : Frequency d => frequencyLength k^d * ‖coefficient k (reconstruction d (z,w))‖^2)
      (2 * ∑ i : Fin d, ‖z i‖^2 + μ * mean d ((w : Space d)*normalized (reconstruction d (z,w)))) := by
  have hh := (hasSum_square (assembly d z)).add
    ((hasSum_pairing (w : Space d) (normalized (reconstruction d (z,w)))).mul_left μ)
  rw [assembly_square_mean] at hh
  exact hh.congr_fun (fun k => graph_energy_term hd μ z w he k)

/-- Exact physical energy, with the paper's (2π)^d normalization. -/
theorem graph_potentialEnergy {d : ℕ} (hd : 0 < d) (μ : ℝ) (z : Coordinates d)
    (w : complement d) (he : projectedEquation (greenContinuous d) ((μ,z),w) = 0) :
    potentialEnergy (reconstruction d (z,w)) = (2*Real.pi)^d *
      (2 * ∑ i : Fin d, ‖z i‖^2 + μ * mean d ((w : Space d)*normalized (reconstruction d (z,w)))) := by
  have hh := graph_normalizedEnergy_hasSum hd μ z w he
  have hsupp : Function.support (fun k : Frequency d => frequencyLength k^d *
      ‖coefficient k (reconstruction d (z,w))‖^2) ⊆ {k : Frequency d | k ≠ 0} := by
    intro k hk hk0
    subst k
    change frequencyLength 0^d * ‖coefficient 0 (reconstruction d (z,w))‖^2 ≠ 0 at hk
    rw [coefficient_zero, mean_reconstruction] at hk
    simp at hk
  have hn := ((hasSum_subtype_iff_of_support_subset hsupp).mpr hh).mul_left ((2*Real.pi)^d)
  have hp : HasSum (potentialTerm (reconstruction d (z,w)))
      ((2*Real.pi)^d * (2 * ∑ i : Fin d, ‖z i‖^2 +
        μ * mean d ((w : Space d)*normalized (reconstruction d (z,w))))) := by
    apply hn.congr_fun
    intro k
    simp only [potentialTerm, ← coefficient_eq_fourierCoeff, mul_pow, Function.comp_apply]
    ring
  exact hp.tsum_eq

theorem graph_normalizedPotentialEnergy {d : ℕ} (hd : 0 < d) (μ : ℝ) (z : Coordinates d)
    (w : complement d) (he : projectedEquation (greenContinuous d) ((μ,z),w) = 0) :
    normalizedPotentialEnergy (reconstruction d (z,w)) =
      2 * ∑ i : Fin d, ‖z i‖^2 + μ * mean d ((w : Space d)*normalized (reconstruction d (z,w))) := by
  rw [normalizedPotentialEnergy, graph_potentialEnergy hd μ z w he]
  field_simp

/-- Exact value of the trusted dual functional along a genuine projected solution. -/
theorem graph_dualFunctional {d : ℕ} (hd : 0 < d) {μ : ℝ} (hμ : 0 < μ)
    (z : Coordinates d) (w : complement d)
    (he : projectedEquation (greenContinuous d) ((μ,z),w) = 0) :
    dualFunctional (μ * spectralThreshold d) (reconstruction d (z,w)) =
      ((logPartitionReal (reconstruction d (z,w)) - (∑ i : Fin d, ‖z i‖^2)/μ -
        (1/2:ℝ)*mean d ((w : Space d)*normalized (reconstruction d (z,w))) : ℝ) : EReal) := by
  have hσ : spectralThreshold d ≠ 0 := (Legacy.TorusEndpoint.endpointSigma_pos hd).ne'
  rw [dualFunctional, logPartition_eq_centeredLogPartition, centeredLogPartition_eq,
    mean_reconstruction, sub_zero, graph_normalizedPotentialEnergy hd μ z w he]
  rw [← EReal.coe_sub]
  congr 1
  field_simp
  ring

#print axioms graph_normalizedPotentialEnergy
#print axioms graph_dualFunctional
end BecknerOnofri.HighDim.LocalEleven.GraphEnergy
