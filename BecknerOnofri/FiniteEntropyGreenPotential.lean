module

public import BecknerOnofri.FiniteEntropyPhysical
public import Legacy.BecknerOnofri.GreenDensityPotentialL2
public import Legacy.BecknerOnofri.GreenExponentialIntegrability
public import Legacy.TorusEndpoint.GreenLowerBound

@[expose] public section

/-! Full finite-entropy densities have bounded actual Green potentials.
Young's entropy inequality supplies the product integrability, rather than
assuming the density is in L2. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
namespace BecknerOnofri.FiniteEntropyGreen
open Legacy.TorusEndpoint Legacy.BecknerOnofri GreenRoughEnergy

local instance : (AddCircle.haarAddCircle (T := 1)).IsNegInvariant := by
  have he : AddCircle.haarAddCircle (T := 1) = (volume : Measure UnitAddCircle) := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := 1)).symm
  rw [he]
  infer_instance
local instance (d : ℕ) : (torusMeasure d).IsAddLeftInvariant := by
  rw [torusMeasure_explicit]; infer_instance
local instance (d : ℕ) : (torusMeasure d).IsNegInvariant := by
  rw [torusMeasure_explicit]; infer_instance

lemma weighted_integrable_bound {d : ℕ} (r : ProbabilityDensity d) (hr : r.FiniteEntropy)
    (g : Torus d → ℝ) (hg : AEStronglyMeasurable g (torusMeasure d))
    (he : Integrable (fun x => Real.exp |g x|) (torusMeasure d)) :
    Integrable (fun x => r.value x*g x) (torusMeasure d) ∧
    (∫ x, r.value x*|g x| ∂torusMeasure d) ≤ densityEntropy r.value +
      ∫ x, Real.exp |g x| ∂torusMeasure d := by
  have hb : ∀ᵐ x ∂torusMeasure d, r.value x*|g x| ≤
      r.value x*Real.log (r.value x)+Real.exp |g x| :=
    by
      filter_upwards [r.nonneg] with x hx
      have h := entropy_young (r.value x) |g x| hx
      linarith
  have hi : Integrable (fun x => r.value x*g x) (torusMeasure d) := by
    apply (hr.add he).mono' (r.integrable.aestronglyMeasurable.mul hg)
    filter_upwards [hb,r.nonneg] with x hx hn
    change ‖r.value x*g x‖ ≤ r.value x*Real.log (r.value x)+Real.exp |g x|
    simpa only [norm_mul,Real.norm_eq_abs,abs_of_nonneg hn] using hx
  have hiabs : Integrable (fun x => r.value x*|g x|) (torusMeasure d) := by
    apply hi.norm.congr
    filter_upwards [r.nonneg] with x hx
    simp only [norm_mul,Real.norm_eq_abs,abs_of_nonneg hx]
  have h := integral_mono_ae hiabs (hr.add he) hb
  change (∫ x,r.value x*|g x| ∂torusMeasure d) ≤
    ∫ x,r.value x*Real.log (r.value x)+Real.exp |g x| ∂torusMeasure d at h
  rw [integral_add hr he] at h
  exact ⟨hi,h⟩

lemma kernel_exp_abs_integrable {d : ℕ} (hd : 0 < d) {b : ℝ}
    (hb : 0 < b) (hbd : b < endpointConstant d) :
    Integrable (fun x => Real.exp |b*kernel d x|) (torusMeasure d) := by
  let B := endpointSigma d*GreenLowerBound.greenLowerConstant d
  have hl : ∀ᵐ x ∂torusMeasure d, -B ≤ kernel d x := by
    filter_upwards [GreenLowerBound.realGreen_ae_lower_bound hd] with x hx
    have h := mul_le_mul_of_nonneg_left hx (endpointSigma_pos hd).le
    simpa only [B,kernel,mul_neg] using h
  apply ((GreenExponentialIntegrability.kernel_exp_integrable hd hb.le hbd).add
    (integrable_const (Real.exp (b*B)))).mono'
    (Real.continuous_exp.comp_aestronglyMeasurable
      (continuous_abs.comp_aestronglyMeasurable
        ((kernel_integrable d).aestronglyMeasurable.const_mul b)))
  filter_upwards [hl] with x hx
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  by_cases h : 0 ≤ kernel d x
  · rw [abs_of_nonneg (mul_nonneg hb.le h)]
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  · rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hb.le (le_of_not_ge h))]
    have he : Real.exp (-(b*kernel d x)) ≤ Real.exp (b*B) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    exact he.trans (le_add_of_nonneg_left (Real.exp_pos _).le)

/-- One finite bound works at every point of the actual Green convolution. -/
theorem potential_bounded {d : ℕ} (hd : 0 < d) (r : ProbabilityDensity d)
    (hr : r.FiniteEntropy) : ∃ C : ℝ, ∀ x, ‖potential r x‖ ≤ C := by
  let b := endpointConstant d/2
  have hc : 0 < endpointConstant d := div_pos (Nat.cast_pos.mpr hd) (endpointSigma_pos hd)
  have hb : 0 < b := by dsimp [b]; positivity
  have hbd : b < endpointConstant d := by dsimp [b]; linarith
  have hexp := kernel_exp_abs_integrable hd hb hbd
  refine ⟨(densityEntropy r.value+∫ y,Real.exp |b*kernel d y| ∂torusMeasure d)/b,?_⟩
  intro x
  have hm := Measure.measurePreserving_sub_left (torusMeasure d) x
  have hg : Integrable (fun y => kernel d (x-y)) (torusMeasure d) :=
    ((hm.integrable_comp (kernel_integrable d).aestronglyMeasurable)).mpr (kernel_integrable d)
  have he : Integrable (fun y => Real.exp |b*kernel d (x-y)|) (torusMeasure d) :=
    (hm.integrable_comp hexp.aestronglyMeasurable).mpr hexp
  have h := (weighted_integrable_bound r hr (fun y => b*kernel d (x-y))
    (hg.aestronglyMeasurable.const_mul b) he).2
  have heq : (∫ y,r.value y*|b*kernel d (x-y)| ∂torusMeasure d) =
      b*(∫ y,r.value y*|kernel d (x-y)| ∂torusMeasure d) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun y => by dsimp only; rw [abs_mul,abs_of_pos hb]; ring)
  rw [heq,integral_sub_left_eq_self (fun y => Real.exp |b*kernel d y|) (torusMeasure d) x] at h
  have hnorm : ‖potential r x‖ ≤ ∫ y,r.value y*|kernel d (x-y)| ∂torusMeasure d := by
    calc
      _ ≤ ∫ y,‖kernel d (x-y)*r.value y‖ ∂torusMeasure d := norm_integral_le_integral_norm _
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [r.nonneg] with y hy
        simp only [norm_mul,Real.norm_eq_abs,abs_of_nonneg hy,mul_comm]
  exact hnorm.trans ((le_div_iff₀ hb).mpr (by simpa only [mul_comm] using h))

theorem potential_memLp {d : ℕ} (hd : 0 < d) (r : ProbabilityDensity d)
    (hr : r.FiniteEntropy) : MemLp (potential r) 2 (torusMeasure d) := by
  obtain ⟨C,hC⟩ := potential_bounded hd r hr
  exact MemLp.of_bound (potential_integrable r).aestronglyMeasurable C (Eventually.of_forall hC)

#print axioms potential_bounded
#print axioms potential_memLp
end BecknerOnofri.FiniteEntropyGreen
