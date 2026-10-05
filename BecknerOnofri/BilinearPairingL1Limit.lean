module

public import BecknerOnofri.BilinearPairingL1Continuity

@[expose] public section

noncomputable section
open MeasureTheory Filter Legacy.TorusEndpoint
open scoped Topology
namespace BecknerOnofri.BilinearPolarization

/-- Joint L1 continuity for every bounded measurable kernel. -/
theorem pairing_l1_limit {d : ℕ} {ι : Type*} (l : Filter ι)
    (K : Torus d → Torus d → ℝ) (hmeas : Measurable (Function.uncurry K))
    {C : ℝ} (hC : ∀ x y,‖K x y‖≤C)
    (f g : ι → Torus d → ℝ) (f₀ g₀ : Torus d → ℝ)
    (hf : ∀ j,Integrable (f j) (torusMeasure d))
    (hg : ∀ j,Integrable (g j) (torusMeasure d))
    (hf₀ : Integrable f₀ (torusMeasure d)) (hg₀ : Integrable g₀ (torusMeasure d))
    (hfL : Tendsto (fun j => ∫ x,‖f j x-f₀ x‖ ∂torusMeasure d) l (𝓝 0))
    (hgL : Tendsto (fun j => ∫ x,‖g j x-g₀ x‖ ∂torusMeasure d) l (𝓝 0)) :
    Tendsto (fun j => pairing K (f j) (g j)) l (𝓝 (pairing K f₀ g₀)) := by
  let ef := fun j => ∫ x,‖f j x-f₀ x‖ ∂torusMeasure d
  let eg := fun j => ∫ x,‖g j x-g₀ x‖ ∂torusMeasure d
  let F := ∫ x,‖f₀ x‖ ∂torusMeasure d
  let G := ∫ x,‖g₀ x‖ ∂torusMeasure d
  have hC0 : 0≤C := (norm_nonneg (K 0 0)).trans (hC 0 0)
  have hGN (j : ι) : (∫ x,‖g j x‖ ∂torusMeasure d)≤eg j+G := by
    calc
      _ ≤ ∫ x,(‖g j x-g₀ x‖+‖g₀ x‖) ∂torusMeasure d := by
        apply integral_mono (hg j).norm (((hg j).sub hg₀).norm.add hg₀.norm)
        intro x
        simpa only [Pi.add_apply,Pi.sub_apply,sub_add_cancel] using norm_add_le (g j x-g₀ x) (g₀ x)
      _ = eg j+G := integral_add (f := fun x => ‖g j x-g₀ x‖)
        (((hg j).sub hg₀).norm) hg₀.norm
  have hb (j : ι) : ‖pairing K (f j) (g j)-pairing K f₀ g₀‖≤
      C*ef j*(eg j+G)+C*F*eg j := by
    exact (pairing_l1_error K hmeas hC (f j) f₀ (g j) g₀ (hf j) hf₀ (hg j) hg₀).trans
      (add_le_add (mul_le_mul_of_nonneg_left (hGN j)
        (mul_nonneg hC0 (integral_nonneg (fun x => norm_nonneg (f j x-f₀ x))))) (le_refl _))
  have hlim : Tendsto (fun j => C*ef j*(eg j+G)+C*F*eg j) l (𝓝 0) := by
    simpa only [ef,eg,mul_zero,zero_mul,zero_add,add_zero] using ((tendsto_const_nhds.mul hfL).mul
      (hgL.add (tendsto_const_nhds (x := G)))).add
      ((tendsto_const_nhds (x := C*F)).mul hgL)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) hb hlim

#print axioms pairing_l1_limit
end BecknerOnofri.BilinearPolarization
