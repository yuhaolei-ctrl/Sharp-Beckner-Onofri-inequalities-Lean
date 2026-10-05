import BecknerOnofri.GraphEnergy

/-! Self-adjointness of the actual continuous Green operator and its
complement projection for the genuine Haar pairing. -/
noncomputable section
open Classical
open scoped ComplexConjugate
namespace BecknerOnofri.HighDim.GreenPairing
open ContinuousGibbs ContinuousFirstShell ContinuousComplement QuadraticModes
open GraphEnergy

theorem mean_mul_selfAdjoint_of_multiplier {d : ℕ}
    (T : Space d →L[ℝ] Space d) (m : Frequency d → ℝ)
    (hm : ∀ (f : Space d) k, coefficient k (T f) = (m k : ℂ) * coefficient k f)
    (f g : Space d) : mean d (f*T g) = mean d (T f*g) := by
  symm
  apply (hasSum_pairing (T f) g).unique
  apply (hasSum_pairing f (T g)).congr_fun
  intro k
  simp only [hm, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem mean_mul_green {d : ℕ} (hd : 0 < d) (f g : Space d) :
    mean d (f * greenContinuous d g) = mean d (greenContinuous d f * g) := by
  apply mean_mul_selfAdjoint_of_multiplier (greenContinuous d)
    (fun k => if k=0 then 0 else 1 / frequencyLength k^d)
  intro u k
  rw [coefficient_green hd]

/-- The actual C-to-C Green operator with the constant and first shell removed. -/
def projectedGreen (d : ℕ) : Space d →L[ℝ] Space d :=
  (complement d).subtypeL.comp ((complementMap d).comp (greenContinuous d))

@[simp] theorem projectedGreen_apply {d : ℕ} (f : Space d) :
    projectedGreen d f = (complementMap d (greenContinuous d f) : Space d) := rfl

theorem coefficient_projectedGreen {d : ℕ} (hd : 0 < d) (f : Space d) (k : Frequency d) :
    coefficient k (projectedGreen d f) =
      ((if ComplementFrequency k then 1 / frequencyLength k^d else 0 : ℝ) : ℂ) * coefficient k f := by
  rw [projectedGreen_apply, complementMap_coefficient]
  by_cases hk : ComplementFrequency k
  · rw [if_pos hk, coefficient_green hd, if_neg hk.1, if_pos hk]
  · simp [hk]

theorem mean_mul_projectedGreen {d : ℕ} (hd : 0 < d) (f g : Space d) :
    mean d (f * projectedGreen d g) = mean d (projectedGreen d f * g) :=
  mean_mul_selfAdjoint_of_multiplier (projectedGreen d)
    (fun k => if ComplementFrequency k then 1 / frequencyLength k^d else 0)
      (coefficient_projectedGreen hd) f g

@[simp] theorem mean_projectedGreen {d : ℕ} (f : Space d) :
    mean d (projectedGreen d f) = 0 := (complementMap d (greenContinuous d f)).property.1

theorem green_one {d : ℕ} (hd : 0 < d) : greenContinuous d (1 : Space d) = 0 := by
  apply coefficient_ext
  intro k
  rw [coefficient_green hd, map_zero]
  by_cases hk : k=0
  · simp [hk]
  · have hc : coefficient k (1 : Space d) = 0 := by
      change coefficient k (ContinuousMap.const (Torus d) 1) = 0
      rw [coefficient_const, if_neg hk]
    simp [hc]

theorem projectedGreen_one {d : ℕ} (hd : 0 < d) : projectedGreen d (1 : Space d) = 0 := by
  rw [projectedGreen_apply, green_one hd, map_zero, Submodule.coe_zero]

theorem projectedGreen_sub_one {d : ℕ} (hd : 0 < d) (f : Space d) :
    projectedGreen d (f-1) = projectedGreen d f := by
  rw [map_sub, projectedGreen_one hd, sub_zero]

#print axioms mean_mul_green
#print axioms mean_mul_projectedGreen
end BecknerOnofri.HighDim.GreenPairing
