import Legacy.BecknerOnofri.SteinerFromPolarization
import Legacy.BecknerOnofri.GreenPolarization
import Legacy.BecknerOnofri.SmoothFourier

/-! Genuine smooth Steiner Euler maximizers, selected from the actual compact
variational optimizer set. All polarization energy comparisons are discharged. -/
noncomputable section
namespace Legacy.BecknerOnofri.SteinerSelection
open MeasureTheory Set Legacy.TorusEndpoint TorusSobolev SubcriticalAttainment SubcriticalEuler
open SubcriticalPrimalDual CoordinatePolarization SteinerFromPolarization SmoothFourier WienerFourier

def Steiner {d : ℕ} (f : Torus d → ℝ) : Prop :=
  (∀ (i : Fin d) (x : Torus d), f (Function.update x i (-x i)) = f x) ∧
  ∀ (x : Torus d) (i : Fin d), AntitoneOn (fun t : ℝ => f (slice x i t)) (Icc 0 (1/2))

theorem steiner_of_origin_invariant {d : ℕ} {f : Torus d → ℝ} (hf : Continuous f)
    (hfixed : OriginPolarizationInvariant f) : Steiner f :=
  ⟨separately_even hf hfixed, slice_antitone hf hfixed⟩

theorem steiner_of_normalized_exp {d : ℕ} {f : Torus d → ℝ} {Z : ℝ} (hZ : 0 < Z)
    (h : Steiner (fun x => Real.exp (f x)/Z)) : Steiner f := by
  constructor
  · intro i x
    apply Real.exp_injective
    have he := congrArg (fun t : ℝ => t*Z) (h.1 i x)
    simpa only [div_mul_cancel₀ _ hZ.ne'] using he
  · intro x i s hs t ht hst
    have he := h.2 x i hs ht hst
    exact Real.exp_le_exp.mp ((div_le_div_iff_of_pos_right hZ).mp he)

/-- Every subcritical coefficient has an actual global Euler maximizer whose
smooth density and continuous real potential are both coordinatewise Steiner. -/
theorem exists_steiner_maximizer {d : ℕ} (hd : 0 < d) {A : ℝ}
    (hA : 1/(4*endpointConstant d) < A) :
    ∃ u : TorusL2 d, Admissible u ∧
      (∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u) ∧
      Steiner (smoothGibbsValue u) ∧ Steiner (fun x => (representative u x).re) := by
  obtain ⟨r, hr, hmax, hfixed⟩ := PolarizationSelection.exists_fixed_maximizer hd hA
    (CosineMomentWeight.weight d) (CosineMomentWeight.weight_memLp d)
  have hrinv : OriginPolarizationInvariant r.value := by
    intro i a ha ha0
    exact hfixed i a (CosineMomentWeight.weight_strict i ha ha0)
      (fourierEnergy_polarize_le hd i a r hr)
  have hC : 0 < endpointConstant d := div_pos (Nat.cast_pos.mpr hd) (endpointSigma_pos hd)
  have hA0 : 0 < A := (by positivity : 0 < 1/(4*endpointConstant d)).trans hA
  have hR := roughExponentialBound hd (by positivity : 0 < endpointConstant d/2)
    (by linarith : endpointConstant d/2 < endpointConstant d)
  let u := dualPotential A r hr
  have hu : Admissible u := dualPotential_admissible hd A r hr
  have humax : ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u :=
    (density_maximizer_dual hd hR hA0 r hr hmax).2
  have hs := maximizer_fourier_summable hd hR hA0 hu humax
  have he : smoothGibbsValue u =ᵐ[torusMeasure d] r.value :=
    (smoothGibbsValue_ae_eq u hs).trans (density_maximizer_gibbs hd hR hA0 r hr hmax).symm
  have hinv : OriginPolarizationInvariant (smoothGibbsValue u) := by
    intro i a ha ha0
    exact (polarize_congr_ae i a he).trans ((hrinv i a ha ha0).trans he.symm)
  have hst := steiner_of_origin_invariant (smoothGibbsValue_continuous u hs) hinv
  exact ⟨u, hu, humax, hst, steiner_of_normalized_exp (partition_pos hR hu) hst⟩

/-- A strict continuous density counterexample gives a positive actual
subcritical maximum, and compact selection preserves that maximum value. -/
theorem exists_positive_steiner_maximizer {d : ℕ} (hd : 0 < d)
    (r : ProbabilityDensity d) (hc : Continuous r.value)
    (hfail : densityEntropy r.value < endpointConstant d*fourierEnergy r) :
    ∃ A : ℝ, 1/(4*endpointConstant d) < A ∧ ∃ u : TorusL2 d, Admissible u ∧
      0 < functional A u ∧
      (∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u) ∧
      Steiner (smoothGibbsValue u) ∧ Steiner (fun x => (representative u x).re) := by
  obtain ⟨A, hA, v, hv, hpos, _⟩ :=
    SubcriticalCounterexample.exists_positive_subcritical_maximizer hd r hc hfail
  obtain ⟨u, hu, hmax, hsρ, hsu⟩ := exists_steiner_maximizer hd hA
  exact ⟨A, hA, u, hu, hpos.trans_le (hmax v hv), hmax, hsρ, hsu⟩

#print axioms exists_steiner_maximizer
#print axioms exists_positive_steiner_maximizer
end Legacy.BecknerOnofri.SteinerSelection
