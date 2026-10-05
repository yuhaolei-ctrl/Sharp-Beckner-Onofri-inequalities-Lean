import Legacy.BecknerOnofri.GreenRoughEnergy

/-! Exponential Jensen for the actual Green convolution; all integrability is proved. -/
noncomputable section
open MeasureTheory Legacy.TorusEndpoint
namespace Legacy.BecknerOnofri.GreenRoughEnergy

local instance (d : ℕ) : (torusMeasure d).IsAddRightInvariant := by
  rw [torusMeasure_explicit]
  infer_instance

/-- Weighted exponential Jensen follows directly from the tangent line of exp. -/
theorem exp_weighted_integral_le {d : ℕ} (rho : ProbabilityDensity d) (f : Torus d → ℝ)
    (hf : Integrable (fun x => rho.value x * f x) (torusMeasure d))
    (he : Integrable (fun x => rho.value x * Real.exp (f x)) (torusMeasure d)) :
    Real.exp (∫ x, rho.value x * f x ∂torusMeasure d) ≤
      ∫ x, rho.value x * Real.exp (f x) ∂torusMeasure d := by
  let c := ∫ x, rho.value x * f x ∂torusMeasure d
  have hs : Integrable (fun x => rho.value x + rho.value x * f x) (torusMeasure d) :=
    rho.integrable.add hf
  have hi : Integrable (fun x => Real.exp c * (rho.value x + rho.value x * f x - rho.value x * c))
      (torusMeasure d) := (hs.sub (rho.integrable.mul_const c)).const_mul _
  have hp : ∀ᵐ x ∂torusMeasure d,
      Real.exp c * (rho.value x + rho.value x * f x - rho.value x * c) ≤
        rho.value x * Real.exp (f x) := by
    filter_upwards [rho.nonneg] with x hx
    have ht := Real.add_one_le_exp (f x-c)
    rw [Real.exp_sub] at ht
    have h := mul_le_mul_of_nonneg_left
      ((le_div_iff₀ (Real.exp_pos c)).mp ht) hx
    nlinarith only [h]
  have h := integral_mono_ae hi he hp
  rw [integral_const_mul, integral_sub hs (rho.integrable.mul_const c),
    integral_add rho.integrable hf, integral_mul_const, rho.mass] at h
  change Real.exp c * (1+c-1*c) ≤ _ at h
  simpa using h

/-- A genuine Haar change of variables proves integrability of the convolution integrand. -/
theorem convolution_integrand_integrable {d : ℕ} (rho : ProbabilityDensity d)
    (f : Torus d → ℝ) (hf : Integrable f (torusMeasure d)) :
    Integrable (fun xy : Torus d × Torus d => f (xy.1-xy.2) * rho.value xy.2)
      ((torusMeasure d).prod (torusMeasure d)) := by
  have hi := hf.mul_prod rho.integrable
  exact ((measurePreserving_sub_prod (torusMeasure d) (torusMeasure d)).integrable_comp
    hi.aestronglyMeasurable).mpr hi

theorem potential_integrable {d : ℕ} (rho : ProbabilityDensity d) :
    Integrable (potential rho) (torusMeasure d) :=
  (convolution_integrand_integrable rho (kernel d) (kernel_integrable d)).integral_prod_left

/-- The mass of an integrable convolution is the mass of the kernel, since rho has mass one. -/
theorem convolution_integral {d : ℕ} (rho : ProbabilityDensity d)
    (f : Torus d → ℝ) (hf : Integrable f (torusMeasure d)) :
    (∫ x, ∫ y, f (x-y) * rho.value y ∂torusMeasure d ∂torusMeasure d) =
      ∫ x, f x ∂torusMeasure d := by
  rw [integral_integral_swap (convolution_integrand_integrable rho f hf)]
  simp_rw [integral_mul_const, integral_sub_right_eq_self]
  rw [integral_const_mul, rho.mass, mul_one]

/-- Pointwise Jensen holds almost everywhere; the weighted exponential need only be locally
integrable almost everywhere, which follows from the global L1 convolution theorem. -/
theorem exp_potential_le_ae {d : ℕ} (rho : ProbabilityDensity d)
    (hr : MemLp rho.value 2 (torusMeasure d)) (b : ℝ)
    (hexp : Integrable (fun x => Real.exp (b * kernel d x)) (torusMeasure d)) :
    ∀ᵐ x ∂torusMeasure d, Real.exp (b * potential rho x) ≤
      ∫ y, Real.exp (b * kernel d (x-y)) * rho.value y ∂torusMeasure d := by
  have hi := convolution_integrand_integrable rho (fun x => Real.exp (b * kernel d x)) hexp
  filter_upwards [hi.prod_right_ae] with x hx
  have hf : Integrable (fun y => rho.value y * (b * kernel d (x-y))) (torusMeasure d) := by
    convert! (potential_integrand_integrable rho hr x).const_mul b using 1
    funext y
    ring
  have he : Integrable (fun y => rho.value y * Real.exp (b * kernel d (x-y))) (torusMeasure d) := by
    simpa only [mul_comm] using hx
  have h := exp_weighted_integral_le rho (fun y => b * kernel d (x-y)) hf he
  have hm : (∫ y, rho.value y * (b * kernel d (x-y)) ∂torusMeasure d) = b * potential rho x := by
    rw [potential, ← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ (fun y => by ring)
  rw [hm] at h
  simpa only [mul_comm] using h

/-- Exponential integrability and the full Jensen partition bound for the actual Green potential. -/
theorem potential_exp_integrable_and_bound {d : ℕ} (rho : ProbabilityDensity d)
    (hr : MemLp rho.value 2 (torusMeasure d)) (b : ℝ)
    (hexp : Integrable (fun x => Real.exp (b * kernel d x)) (torusMeasure d)) :
    Integrable (fun x => Real.exp (b * potential rho x)) (torusMeasure d) ∧
      (∫ x, Real.exp (b * potential rho x) ∂torusMeasure d) ≤ partition d b := by
  have hmajor := (convolution_integrand_integrable rho (fun x => Real.exp (b * kernel d x)) hexp).integral_prod_left
  have hmeas : AEStronglyMeasurable (fun x => Real.exp (b * potential rho x)) (torusMeasure d) :=
    (Real.continuous_exp.comp_aestronglyMeasurable ((potential_integrable rho).aestronglyMeasurable.const_mul b))
  have hbound := exp_potential_le_ae rho hr b hexp
  have hint : Integrable (fun x => Real.exp (b * potential rho x)) (torusMeasure d) := by
    apply hmajor.mono' hmeas
    filter_upwards [hbound] with x hx
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hx
  refine ⟨hint, ?_⟩
  have h := integral_mono_ae hint hmajor hbound
  rw [convolution_integral rho _ hexp] at h
  exact h

/-- The convolution-Jensen route gives the same actual rough Fourier energy bound. -/
theorem rough_energy_via_jensen {d : ℕ} (hd : 0 < d) (rho : ProbabilityDensity d)
    (hr : MemLp rho.value 2 (torusMeasure d)) (b : ℝ)
    (hexp : Integrable (fun x => Real.exp (b * kernel d x)) (torusMeasure d)) :
    b * fourierEnergy rho ≤ densityEntropy rho.value + Real.log (partition d b) := by
  have he := potential_exp_integrable_and_bound rho hr b hexp
  have hp : Integrable (fun x => rho.value x * (b * potential rho x)) (torusMeasure d) := by
    convert! (pairing_integrable rho hr).const_mul b using 1
    funext x
    ring
  have h := entropy_variational_of_integrable rho.nonneg rho.mass rho.integrable
    (PhysicalGreenL2.finiteEntropy_of_memLp rho hr) hp he.1
  have hi : (∫ x, rho.value x * (b * potential rho x) ∂torusMeasure d) = b * fourierEnergy rho := by
    rw [← pairing_eq_fourier hd rho hr, ← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by ring)
  rw [hi] at h
  have hl := Real.log_le_log (integral_exp_pos he.1) he.2
  change b * fourierEnergy rho - _ ≤ densityEntropy rho.value at h
  linarith

#print axioms exp_weighted_integral_le
#print axioms potential_exp_integrable_and_bound
#print axioms rough_energy_via_jensen
end Legacy.BecknerOnofri.GreenRoughEnergy
