import Legacy.BecknerOnofri.CircleHeatGeometry

/-! Coordinate polarization increases the pairing of the actual torus heat kernel. -/
noncomputable section
open Set MeasureTheory Legacy.TorusEndpoint TorusHeatPositivity
open scoped BigOperators
namespace Legacy.BecknerOnofri.CoordinatePolarization
open HeatDensityApproximation CircleHeat

theorem heatKernel_product {d : ℕ} {t : ℝ} (ht : 0 < t) (x : Torus d) :
    heatKernel t x = ∏ j : Fin d, (theta t (x j)).re := by
  rw [heatKernel, torusTheta_eq_ofReal_product ht, Complex.ofReal_re]

theorem heatKernel_reflection {d : ℕ} {t : ℝ} (ht : 0 < t) (i : Fin d) (a : ℝ) (x y : Torus d) :
    heatKernel t (reflection i a x-reflection i a y) = heatKernel t (x-y) := by
  rw [heatKernel_product ht, heatKernel_product ht]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j=i
  · subst j
    simp only [Pi.sub_apply,reflection,ite_true,circleReflection]
    rw [show ((2*a:ℝ):UnitAddCircle)-x i-(((2*a:ℝ):UnitAddCircle)-y i) = -(x i-y i) by abel]
    exact theta_re_even ht _
  · simp only [Pi.sub_apply,reflection,if_neg hj]

theorem heatKernel_half_comparison {d : ℕ} {t : ℝ} (ht : 0 < t) (i : Fin d) (a : ℝ)
    {x y : Torus d} (hx : x ∈ halfTorus i a) (hy : y ∈ halfTorus i a) :
    heatKernel t (x-reflection i a y) ≤ heatKernel t (x-y) := by
  rw [heatKernel_product ht, heatKernel_product ht]
  apply Finset.prod_le_prod
  · intro j _; exact (theta_re_pos ht _).le
  · intro j _
    by_cases hj : j=i
    · subst j
      simp only [Pi.sub_apply,reflection,ite_true]
      exact theta_re_half_comparison ht a hx hy
    · simp only [Pi.sub_apply,reflection,if_neg hj,le_refl]

theorem heat_pairing_polarize_le {d : ℕ} {t : ℝ} (ht : 0 < t) (i : Fin d) (a : ℝ)
    {f : Torus d → ℝ} (hf : Integrable f (torusMeasure d)) :
    pairing (fun x y => heatKernel t (x-y)) f ≤
      pairing (fun x y => heatKernel t (x-y)) (polarize i a f) := by
  obtain ⟨z, _, hz⟩ := isCompact_univ.exists_isMaxOn (f := fun x : Torus d => ‖heatKernel t x‖)
    univ_nonempty (heatKernel_continuous ht).norm.continuousOn
  exact pairing_polarize_le_bounded i a (fun x y => heatKernel t (x-y))
    ((heatKernel_continuous ht).comp (continuous_fst.sub continuous_snd)).measurable
    (fun x y => hz (mem_univ (x-y)))
    (heatKernel_reflection ht i a)
    (fun x hx y hy => heatKernel_half_comparison ht i a hx hy) hf

theorem heat_pairing_density_le {d : ℕ} {t : ℝ} (ht : 0 < t) (i : Fin d) (a : ℝ)
    (rho : ProbabilityDensity d) :
    pairing (fun x y => heatKernel t (x-y)) rho.value ≤
      pairing (fun x y => heatKernel t (x-y)) (density i a rho).value :=
  heat_pairing_polarize_le ht i a rho.integrable

#print axioms heat_pairing_density_le
end Legacy.BecknerOnofri.CoordinatePolarization
