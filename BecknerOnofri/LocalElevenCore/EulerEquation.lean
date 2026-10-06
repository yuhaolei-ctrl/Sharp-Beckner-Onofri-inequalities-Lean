module

public import BecknerOnofri.LocalElevenContinuousInverse
public import BecknerOnofri.QuarticSignsEleven
public import BecknerOnofri.EulerEquation
public import BecknerOnofri.LocalElevenCore.CriticalReducedIsolation
public import BecknerOnofri.LocalElevenCore.GraphRegularity

@[expose] public section

/-! Exact equivalence between the solved Green equation and the manuscript's
Fourier Euler equation, including the zero-mean normalization. -/
noncomputable section

open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.ReducedEquation

open BecknerOnofri.HighDim.ReducedEquation hiding coefficient_full_zero_iff complementMap_assembly complementMap_reconstruction coordinates_complement coordinates_green coordinates_one coordinates_reconstruction critical_full_locally_isolated critical_stationary_locally_isolated full full_complement full_coordinates full_mean full_zero_iff full_zero_iff_stationary graph_full_iff_reduced graph_stationary_iff local_full_iff_reduced meanZero_zero_iff mean_green potential potential_analytic reduced reduced_analytic
open BecknerOnofri.HighDim.GreenLocalBranch hiding correction correction_analytic correction_axis correction_base correction_derivative_zero correction_quadratic correction_solves correction_unique exists_analytic_complement green_assembly green_first_complement_zero linearPart_eq zero_axis_of_unique
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch
open BecknerOnofri.HighDim.GreenCritical hiding coefficient_square_summable green_inCriticalSobolev nonzero_eigenvalue_ge_one potentialTerm_green
open GreenCritical

theorem coefficient_full_zero_iff {d : ℕ} (hd : 0 < d) (μ : ℝ) (u : Space d)
    (k : NonzeroFrequency d) :
    coefficient k.val (full d μ u) = 0 ↔
      ((frequencyLength k.val^d:ℝ):ℂ)*coefficient k.val u =
        (μ:ℂ)*coefficient k.val (normalized u) := by
  have hone : coefficient k.val (1 : Space d) = 0 := by
    change coefficient k.val (ContinuousMap.const (Torus d) 1) = 0
    rw [coefficient_const, if_neg k.property]
  have hlam : frequencyLength k.val^d ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (nonzero_eigenvalue_ge_one k)).ne'
  have hc : ((frequencyLength k.val^d:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam
  simp only [full, map_sub, map_smul, coefficient_green hd, if_neg k.property,
    hone, sub_zero, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one,
    sub_eq_zero]
  constructor
  · intro he
    rw [he]
    field_simp
    ring
  · intro he
    apply (mul_left_cancel₀ hc)
    rw [he]
    field_simp
    ring

/-- This is exactly the stationary Fourier equation used in FullModeMorseBott. -/
theorem full_zero_iff_stationary {d : ℕ} (hd : 0 < d) (μ : ℝ) (u : Space d) :
    full d μ u = 0 ↔ MeanZero u ∧ ∀ k : NonzeroFrequency d,
      ((frequencyLength k.val^d:ℝ):ℂ)*fourierCoeff u k.val =
        (μ:ℂ)*fourierCoeff (normalizedGibbs u) k.val := by
  have hn : (fun x => normalized u x) = normalizedGibbs u := funext (normalized_apply u)
  constructor
  · intro he
    refine ⟨?_, ?_⟩
    · have hm := congrArg (mean d) he
      change mean d u = 0
      simpa only [full, map_sub, map_smul, mean_green hd, smul_zero, sub_zero, map_zero] using hm
    · intro k
      have hk := (coefficient_full_zero_iff hd μ u k).mp (by rw [he, map_zero])
      simpa only [coefficient_eq_fourierCoeff, hn] using hk
  · rintro ⟨hm, hs⟩
    apply coefficient_ext
    intro k
    rw [map_zero]
    by_cases hk : k = 0
    · subst k
      rw [coefficient_zero, full, map_sub, map_smul, mean_green hd, smul_zero, sub_zero]
      rw [show mean d u = 0 from hm]
      rfl
    · apply (coefficient_full_zero_iff hd μ u ⟨k,hk⟩).mpr
      simpa only [coefficient_eq_fourierCoeff, hn] using hs ⟨k,hk⟩

theorem graph_stationary_iff {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ x in 𝓝 (1, (0 : Coordinates d)),
      (∀ k : NonzeroFrequency d,
        ((frequencyLength k.val^d:ℝ):ℂ)*fourierCoeff (potential hd x) k.val =
          (x.1:ℂ)*fourierCoeff (normalizedGibbs (potential hd x)) k.val) ↔
        reduced hd x = 0 := by
  filter_upwards [graph_full_iff_reduced hd] with x hx
  rw [full_zero_iff_stationary (by omega)] at hx
  have hm : MeanZero (potential hd x) := mean_reconstruction _
  simpa only [hm, true_and] using hx

/-- In the continuous, mean-zero topology the original critical Euler equation
has no nonzero sufficiently small solution. -/
theorem critical_full_locally_isolated {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ (u : Space d) in 𝓝 (0 : Space d), MeanZero u → (full d 1 u = 0 ↔ u = 0) := by
  have ht : Tendsto (fun u : Space d => (((1:ℝ),coordinates d u),complementMap d u))
      (𝓝 0) (𝓝 ((1,0),0)) := by
    simpa only [map_zero] using ((continuous_const.prodMk (coordinates d).continuous).prodMk
      (complementMap d).continuous).tendsto (0 : Space d)
  have hz : Tendsto (coordinates d) (𝓝 (0 : Space d)) (𝓝 0) := by
    simpa only [map_zero] using (coordinates d).continuous.tendsto (0 : Space d)
  filter_upwards [ht.eventually (local_full_iff_reduced hd),
    hz.eventually (ReducedCubicExpansion.reduced_critical_zero_iff hd)] with u hu hred
  intro hm
  have hrecon : reconstruction d (coordinates d u, complementMap d u) = u := by
    have he := decomposition u
    rw [meanProjection_apply, show mean d u = 0 from hm] at he
    simpa only [ContinuousMap.const_zero, zero_add, reconstruction_apply] using he.symm
  rw [hrecon] at hu
  constructor
  · intro he
    obtain ⟨hw,hz⟩ := hu.mp he
    have hcoord := hred.mp hz
    rw [hcoord, correction_base] at hw
    rw [← hrecon, hcoord, ← hw]
    simp
  · rintro rfl
    simp [full]

theorem critical_stationary_locally_isolated {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ (u : Space d) in 𝓝 (0 : Space d), MeanZero u →
      ((∀ k : NonzeroFrequency d,
        ((frequencyLength k.val^d:ℝ):ℂ)*fourierCoeff u k.val =
          fourierCoeff (normalizedGibbs u) k.val) ↔ u = 0) := by
  filter_upwards [critical_full_locally_isolated hd] with u hu
  intro hm
  have he := full_zero_iff_stationary (by omega : 0 < d) 1 u
  simp only [Complex.ofReal_one, one_mul, hm, true_and] at he
  exact he.symm.trans (hu hm)

#print axioms full_zero_iff_stationary
#print axioms graph_stationary_iff
#print axioms critical_stationary_locally_isolated
end BecknerOnofri.HighDim.LocalEleven.ReducedEquation
