module

public import BecknerOnofri.LocalElevenContinuousInverse
public import BecknerOnofri.QuadraticResolvent
public import BecknerOnofri.QuadraticPairing

@[expose] public section

/-! The genuine complement resolvent (D−I)⁻¹ and its exact finite-mode action. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators ComplexConjugate
namespace BecknerOnofri.HighDim.LocalEleven.QuadraticModes

open BecknerOnofri.HighDim.QuadraticModes hiding complementGreen_synthesis complementMap_synthesis complementMap_synthesis_zero complementSynthesis green_synthesis quadraticSource_expansion resolvent resolvent_synthesis synthesis_mem_complement

open ContinuousGibbs ContinuousFirstShell

theorem synthesis_mem_complement {d : ℕ} {k : Frequency d} (hk : ComplementFrequency k) (z : ℂ) :
    synthesis k z ∈ complement d := by
  rw [mem_complement_fourier_iff]
  intro l hl
  rw [coefficient_synthesis]
  have h₁ : l ≠ k := fun h => hl (h ▸ hk)
  have h₂ : l ≠ -k := by
    intro h
    apply hl
    rw [h]
    exact (complementFrequency_neg k).mpr hk
  simp only [if_neg h₁, if_neg h₂, add_zero]

def complementSynthesis {d : ℕ} {k : Frequency d} (hk : ComplementFrequency k) (z : ℂ) : complement d :=
  ⟨synthesis k z, synthesis_mem_complement hk z⟩

theorem complementMap_synthesis {d : ℕ} {k : Frequency d} (hk : ComplementFrequency k) (z : ℂ) :
    complementMap d (synthesis k z) = complementSynthesis hk z := by
  apply Subtype.ext
  exact complementProjection_eq_self (synthesis_mem_complement hk z)

theorem green_synthesis {d : ℕ} (hd : 0 < d) {k : Frequency d} (hk : k ≠ 0) (z : ℂ) :
    greenContinuous d (synthesis k z) = (1/frequencyLength k^d) • synthesis k z := by
  apply coefficient_ext
  intro l
  rw [coefficient_green hd, map_smul, coefficient_synthesis]
  by_cases hlk : l=k
  · subst l
    simp only [if_neg hk, Complex.real_smul]
  · by_cases hln : l = -k
    · subst l
      simp only [frequencyLength_neg, neg_eq_zero, if_neg hk, Complex.real_smul]
    · simp only [if_neg hlk, if_neg hln, add_zero, mul_zero, smul_zero]

theorem complementGreen_synthesis {d : ℕ} (hd : 0 < d) {k : Frequency d}
    (hk : ComplementFrequency k) (z : ℂ) :
    continuousComplementGreen hd (complementSynthesis hk z) =
      (1/frequencyLength k^d) • complementSynthesis hk z := by
  apply Subtype.ext
  exact green_synthesis hd hk.1 z

/-- (D−I)⁻¹ on the actual continuous complement, defined through the proved Green inverse. -/
def resolvent {d : ℕ} (hd : 11 ≤ d) : complement d →L[ℝ] complement d :=
  (continuousComplementContinuousLinearEquiv hd (by norm_num : (0:ℝ)≤1)
    (by norm_num : (1:ℝ)≤2)).symm.toContinuousLinearMap.comp
      (continuousComplementGreen (by omega))

theorem resolvent_synthesis {d : ℕ} (hd : 11 ≤ d) {k : Frequency d}
    (hk : ComplementFrequency k) (z : ℂ) :
    resolvent hd (complementSynthesis hk z) =
      (1/(frequencyLength k^d-1)) • complementSynthesis hk z := by
  let e := continuousComplementContinuousLinearEquiv hd (by norm_num : (0:ℝ)≤1)
    (by norm_num : (1:ℝ)≤2)
  apply e.injective
  change e (e.symm (continuousComplementGreen (by omega) (complementSynthesis hk z))) = _
  rw [e.apply_symm_apply]
  change _ = e.toContinuousLinearMap _
  rw [continuousComplementContinuousLinearEquiv_one, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, map_smul, complementGreen_synthesis]
  rw [smul_smul]
  have hEig : 32 ≤ frequencyLength k^d := complement_eigenvalue_ge_thirtytwo hd hk
  have hEig0 : frequencyLength k^d ≠ 0 := by linarith
  have hEig1 : frequencyLength k^d-1 ≠ 0 := by linarith
  have hs : 1/frequencyLength k^d = 1/(frequencyLength k^d-1) -
      1/(frequencyLength k^d-1)*(1/frequencyLength k^d) := by
    field_simp [hEig0, hEig1]
    <;> ring
  apply Subtype.ext
  ext x
  change (1/frequencyLength k^d) * synthesis k z x =
    (1/(frequencyLength k^d-1)) * synthesis k z x -
      (1/(frequencyLength k^d-1)*(1/frequencyLength k^d)) * synthesis k z x
  linear_combination hs * synthesis k z x

theorem complementMap_synthesis_zero {d : ℕ} (z : ℂ) :
    complementMap d (synthesis (0 : Frequency d) z) = 0 := by
  have h : synthesis (0 : Frequency d) z = ContinuousMap.const (Torus d) (2*z.re) := by
    ext x
    simp [synthesis_apply, UnitAddTorus.mFourier_zero]
  rw [h]
  apply Subtype.ext
  simp [complementMap_coe, complementProjection_apply, meanProjection_apply]

theorem quadraticSource_expansion {d : ℕ} (z : Coordinates d) :
    quadraticSource z = ∑ i : Fin d, ∑ j : Fin d,
      (complementMap d (synthesis (axisFrequency i+axisFrequency j) (z i*z j)) +
       complementMap d (synthesis (axisFrequency i-axisFrequency j) (z i*conj (z j)))) := by
  unfold quadraticSource
  rw [shellSquare_expansion]
  simp only [map_sum, map_add]

#print axioms resolvent_synthesis
end BecknerOnofri.HighDim.LocalEleven.QuadraticModes
