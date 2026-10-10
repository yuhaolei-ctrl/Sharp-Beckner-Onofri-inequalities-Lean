module

public import BecknerOnofri.V2.Reaudit.Attainment.Correspondence
public import BecknerOnofri.V2.Reaudit.Attainment.PotentialFourier
public import BecknerOnofri.V2.Reaudit.Attainment.SobolevSmooth
public import BecknerOnofri.RawGapBridges
public import BecknerOnofri.OnsetSobolev

@[expose] public section

/-! # Euler-Lagrange system and regularity of extremizers
(`cor:section2-extremizer-correspondence` (iii); row S009)

Printed proof: "apply `|∇|^d` to `u = β g * ρ`. The potential identity gives
`|∇|^d u = β c_d (ρ - 1)` in the sense of distributions. Substitution into the Gibbs formula gives
the Kirkwood-Monroe equation.  For the regularity assertion, `eq:section2-all-exponential-moments`
gives `ρ ∈ L²`, and the Fourier multiplier gives `u ∈ H^d`. For each integer `j ≥ 1`, `H^{jd}` is a
Banach algebra embedded in `L^∞`. Hence `u ∈ H^{jd}` implies `e^u ∈ H^{jd}` and therefore
`ρ ∈ H^{jd}`; the Euler-Lagrange equation then gives `u ∈ H^{(j+1)d}`. Iterating proves
`u, ρ ∈ C^∞`. The exponential representation now gives strict positivity."

Here the distributional equation is recorded as the equality of all Fourier coefficients (a
distribution on the torus is determined by them, and `|∇|^d` acts as multiplication by
`(2π|k|)^d`).  The bootstrap is `V2.Onset.sobolev_first_step` / `sobolev_bootstrap`; the step
"`H^{s}` for all `s` implies smooth" is `smooth_of_inSobolev_multiples`. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology ENNReal

namespace BecknerOnofri.V2.Reaudit.Attainment
open BecknerOnofri.HighDim BecknerOnofri.V2.Vocab

variable {d : ℕ}

theorem exp_memLp_two (hd : 0 < d) {u : Torus d → ℝ} (hu : InCriticalSobolev u) (hm : MeanZero u) :
    MemLp (fun x => Real.exp (u x)) 2 (torusMeasure d) := by
  have hint := critical_exp_integrable hd u hu (p := 2) two_pos
  rw [centered_eq_self hm] at hint
  refine (memLp_two_iff_integrable_sq
    (Real.continuous_exp.comp_aestronglyMeasurable hu.1.aestronglyMeasurable)).2 ?_
  refine hint.congr (Filter.Eventually.of_forall fun x => ?_)
  show Real.exp (2 * u x) = Real.exp (u x) ^ 2
  rw [sq, ← Real.exp_add]; ring_nf

theorem normalizedGibbs_memLp_two (hd : 0 < d) {u : Torus d → ℝ} (hu : InCriticalSobolev u)
    (hm : MeanZero u) : MemLp (normalizedGibbs u) 2 (torusMeasure d) := by
  have e : normalizedGibbs u = fun x => (∫ y, Real.exp (u y) ∂torusMeasure d)⁻¹ * Real.exp (u x) := by
    funext x; simp [normalizedGibbs, div_eq_inv_mul]
  rw [e]
  exact (exp_memLp_two hd hu hm).const_mul _


theorem normalizedGibbs_smooth {u : Torus d → ℝ} (hu : SmoothOnTorus u) :
    SmoothOnTorus (normalizedGibbs u) := by
  change ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
    (fun x : Fin d → ℝ => Real.exp (u (fun j => (x j : UnitAddCircle))) /
      (∫ y, Real.exp (u y) ∂torusMeasure d))
  exact hu.exp.div_const _

/-- **Regularity step of `cor:section2-extremizer-correspondence` (iii).** -/
theorem smooth_representative_of_euler (hd : 0 < d) {u : Torus d → ℝ} (hu : InCriticalSobolev u)
    (hm : MeanZero u) (c : ℝ)
    (heuler : ∀ k : Frequency d, k ≠ 0 →
      (frequencyLength k : ℂ) ^ d * fourierCoeff u k = (c : ℂ) * fourierCoeff (normalizedGibbs u) k) :
    ∃ v : ContinuousGibbs.Space d, (⇑v : Torus d → ℝ) =ᵐ[torusMeasure d] u ∧ SmoothOnTorus (⇑v) := by
  have hρ := normalizedGibbs_memLp_two hd hu hm
  -- first step: `ρ ∈ L²` and the Fourier multiplier give `u ∈ H^d`
  obtain ⟨hu1, -⟩ := Onset.sobolev_first_step c (∫ x, normalizedGibbs u x ^ 2 ∂torusMeasure d) u
    (normalizedGibbs u) hu.1 hm hρ le_rfl heuler
  -- `H^d ⊂ C^0`
  obtain ⟨v, hvu, hv1, -⟩ := SobolevEmbedding.exists_continuous_representative hd
    (s := (d : ℝ)) (by have : (0 : ℝ) < d := by exact_mod_cast hd
                       linarith) u hu1
  have hvm : MeanZero (⇑v) := by
    unfold MeanZero; rw [integral_congr_ae hvu]; exact hm
  have hg : normalizedGibbs (⇑v) =ᵐ[torusMeasure d] normalizedGibbs u := Gap.gibbs_congr hvu
  have heuler' : ∀ k : Frequency d, k ≠ 0 →
      ((frequencyLength k : ℂ) ^ d) * fourierCoeff (⇑v) k =
        (c : ℂ) * fourierCoeff (normalizedGibbs (⇑v)) k := by
    intro k hk
    rw [fourierCoeff_congr_ae hvu k, fourierCoeff_congr_ae hg k]
    exact heuler k hk
  have hboot := Onset.sobolev_bootstrap hd |c| (sobolevNorm (d : ℝ) (⇑v)) c le_rfl v
    (by rw [ContinuousGibbs.mean_apply]; exact hvm) heuler' hv1 le_rfl
  exact ⟨v, hvu, smooth_of_inSobolev_multiples hd v fun m => (hboot m).1⟩



/-- `g` has mean zero, so `g * (f - 1) = g * f`. -/
theorem densityPotential_sub_one (β : ℝ) {f : Torus d → ℝ} (hf : MemLp f 2 (torusMeasure d)) :
    Gap.densityPotential β (fun y => f y - 1) = Gap.densityPotential β f := by
  funext x
  unfold Gap.densityPotential
  congr 1
  have hG := Legacy.TorusEndpoint.GreenKernelReal.realGreen_memLp d
  have hcomp := hG.comp_measurePreserving (Legacy.BecknerOnofri.GreenRoughEnergy.sub_left_preserving x)
  have hint : Integrable (fun y => Legacy.TorusEndpoint.GreenKernelReal.realGreen d (x - y) * f y)
      (torusMeasure d) := hcomp.integrable_mul hf
  have hg : Integrable (fun y => Legacy.TorusEndpoint.GreenKernelReal.realGreen d (x - y))
      (torusMeasure d) := hcomp.integrable one_le_two
  have e : (fun y => Legacy.TorusEndpoint.GreenKernelReal.realGreen d (x - y) * (f y - 1)) =
      fun y => Legacy.TorusEndpoint.GreenKernelReal.realGreen d (x - y) * f y -
        Legacy.TorusEndpoint.GreenKernelReal.realGreen d (x - y) := by funext y; ring
  have h0 : (∫ y, Legacy.TorusEndpoint.GreenKernelReal.realGreen d (x - y) ∂torusMeasure d) = 0 :=
    (Legacy.BecknerOnofri.GreenRoughEnergy.integral_sub_left
      (Legacy.TorusEndpoint.GreenKernelReal.realGreen d) x).trans
      (Legacy.TorusEndpoint.GreenKernelReal.realGreen_integral_zero d)
  rw [e, integral_sub hint hg, h0, sub_zero]



/-- The Euler equation of an extremizing potential, in the repository's Fourier form:
`|k|^d û(k) = (β/β_s) ρ̂(k)` for `k ≠ 0`, where `ρ = e^u / ∫ e^u`. -/
theorem euler_of_maximizer (hd : 0 < d) {A : ℝ} (hA : 0 < A) {u : Torus d → ℝ}
    (hmax : IsCoefficientMaximizer d A u) {k : Frequency d} (hk : k ≠ 0) :
    (frequencyLength k : ℂ) ^ d * fourierCoeff u k =
      ((Gap.coefficient d A / spectralThreshold d : ℝ) : ℂ) * fourierCoeff (normalizedGibbs u) k := by
  have hu := hmax.1
  have hm := hmax.2.1
  have hβ : 0 < Gap.coefficient d A := Gap.coefficient_pos hd hA
  have hae := ((coefficientMaximizer_iff hd hA hu hm).1 hmax).2
  have hσf := normalizedGibbsDensity_finiteEntropy hd u hu hm
  have h := fourierCoeff_densityPotential hd hβ (normalizedGibbsDensity hd u hu hm) hσf hk
  have hae' : u =ᵐ[torusMeasure d]
      Gap.densityPotential (Gap.coefficient d A) (normalizedGibbsDensity hd u hu hm).value := hae
  rw [← fourierCoeff_congr_ae hae' k] at h
  exact h


/-- The Euler-Lagrange equation `|∇|^d u = β c_d (ρ - 1)` of `eq:section2-euler-lagrange`, as the
equality of all Fourier coefficients (the symbol of `|∇|^d` is `(2π|k|)^d`), with
`β = (2 A c_d)⁻¹`, for an extremizing potential `u` and `ρ = e^u / ∫ e^u`. -/
theorem euler_lagrange_of_maximizer (hd : 0 < d) {A : ℝ} (hA : 0 < A) {u : Torus d → ℝ}
    (hmax : IsCoefficientMaximizer d A u) (k : Frequency d) :
    (((2 * Real.pi * frequencyLength k : ℝ) : ℂ)) ^ d * fourierCoeff u k =
      (((2 * A * kernelConstant d)⁻¹ * kernelConstant d : ℝ) : ℂ) *
        fourierCoeff (fun x => normalizedGibbs u x - 1) k := by
  have hu := hmax.1
  have hm := hmax.2.1
  have hρ := normalizedGibbs_memLp_two hd hu hm
  have hsub : fourierCoeff (fun x => normalizedGibbs u x - 1) k =
      fourierCoeff (normalizedGibbs u) k - fourierCoeff (fun _ : Torus d => (1 : ℝ)) k :=
    FullHessianDecomposition.fourierCoeff_sub (normalizedGibbs u) (fun _ => 1) hρ (memLp_const _) k
  by_cases hk : k = 0
  · subst hk
    have hd0 : d ≠ 0 := hd.ne'
    have hfl : frequencyLength (0 : Frequency d) = 0 := by simp [frequencyLength]
    rw [hfl]
    simp only [mul_zero, Complex.ofReal_zero, zero_pow hd0, zero_mul]
    symm
    have hmass := (normalizedGibbsDensity hd u hu hm).mass
    have hz : MeanZero (fun x => normalizedGibbs u x - 1) := by
      unfold MeanZero
      have hi := (normalizedGibbsDensity hd u hu hm).integrable
      change Integrable (normalizedGibbs u) (torusMeasure d) at hi
      rw [integral_sub hi (integrable_const 1)]
      change (∫ x, normalizedGibbs u x ∂torusMeasure d) - _ = 0
      have hmass' : (∫ x, normalizedGibbs u x ∂torusMeasure d) = 1 := hmass
      rw [hmass']; simp
    rw [Onset.fourierCoeff_zero_meanZero hz, mul_zero]
  · rw [hsub, fourierCoeff_one_nonzero k hk, sub_zero]
    have h := euler_of_maximizer hd hA hmax hk
    have hβ : Gap.coefficient d A = (2 * A * kernelConstant d)⁻¹ := gapCoefficient_eq hd hA
    rw [hβ] at h
    have hkc := kernelConstant_mul_spectralThreshold hd
    have hσ := spectralThreshold_pos' hd
    have hc := kernelConstant_pos hd
    have e1 : (((2 * Real.pi * frequencyLength k : ℝ)) : ℂ) ^ d =
        ((2 * Real.pi : ℝ) : ℂ) ^ d * (frequencyLength k : ℂ) ^ d := by push_cast; ring
    rw [e1, mul_assoc, h, ← mul_assoc]
    congr 1
    have : ((2 * Real.pi : ℝ) : ℂ) ^ d = (((2 * Real.pi) ^ d : ℝ) : ℂ) := by push_cast; rfl
    rw [this, ← Complex.ofReal_mul]
    congr 1
    rw [← hkc]
    field_simp


/-- **Regularity of an extremizing potential** (`cor:section2-extremizer-correspondence` (iii)):
`u` has a smooth representative `v`, and `e^v / ∫ e^v` is smooth, strictly positive, and equal
almost everywhere to `e^u / ∫ e^u`. -/
theorem maximizer_regularity (hd : 0 < d) {A : ℝ} (hA : 0 < A) {u : Torus d → ℝ}
    (hmax : IsCoefficientMaximizer d A u) :
    ∃ v : Torus d → ℝ, v =ᵐ[torusMeasure d] u ∧ SmoothOnTorus v ∧ MeanZero v ∧
      SmoothOnTorus (normalizedGibbs v) ∧ (∀ x, 0 < normalizedGibbs v x) ∧
      normalizedGibbs v =ᵐ[torusMeasure d] normalizedGibbs u := by
  have hu := hmax.1
  have hm := hmax.2.1
  obtain ⟨v, hvu, hvs⟩ := smooth_representative_of_euler hd hu hm (Gap.coefficient d A / spectralThreshold d)
    (fun k hk => euler_of_maximizer hd hA hmax hk)
  have hvc : InCriticalSobolev (⇑v) := (Gap.inCriticalSobolev_congr hvu).2 hu
  have hvm : MeanZero (⇑v) := by
    unfold MeanZero; rw [integral_congr_ae hvu]; exact hm
  exact ⟨⇑v, hvu, hvs, hvm, normalizedGibbs_smooth hvs, normalizedGibbs_pos hd _ hvc hvm,
    Gap.gibbs_congr hvu⟩

/-- **Regularity of an extremizing density** (`cor:section2-extremizer-correspondence` (iii)):
every global minimizer `ρ` of the free energy at `β = (2 A c_d)⁻¹` agrees almost everywhere with a
smooth, strictly positive function `q`, and `q = e^v / ∫ e^v` for a smooth mean-zero `v` that
agrees almost everywhere with `u_ρ = β g * ρ`. -/
theorem densityMinimizer_regularity (hd : 0 < d) {A : ℝ} (hA : 0 < A) (ρ : ProbabilityDensity d)
    (hmin : IsGlobalMinimizer (Gap.coefficient d A) ρ) :
    ∃ v : Torus d → ℝ, v =ᵐ[torusMeasure d] Gap.densityPotential (Gap.coefficient d A) ρ.value ∧
      SmoothOnTorus v ∧ MeanZero v ∧ SmoothOnTorus (normalizedGibbs v) ∧
      (∀ x, 0 < normalizedGibbs v x) ∧ ρ.value =ᵐ[torusMeasure d] normalizedGibbs v := by
  obtain ⟨hmax, hρae⟩ := (densityMinimizer_iff hd hA ρ hmin.1).1 hmin
  obtain ⟨v, hvu, hvs, hvm, hs, hp, hg⟩ := maximizer_regularity hd hA hmax
  exact ⟨v, hvu, hvs, hvm, hs, hp, hρae.trans hg.symm⟩

/-- **Kirkwood-Monroe equation** (`eq:section2-kirkwood-monroe`) for the smooth representative
`q = e^v / ∫ e^v` of an extremizer: `q = exp(β g * (q - 1)) / ∫ exp(β g * (q - 1))` almost everywhere
(`g * (q - 1) = g * q` because `g` has mean zero). -/
theorem kirkwoodMonroe_of_maximizer (hd : 0 < d) {A : ℝ} (hA : 0 < A) {u : Torus d → ℝ}
    (hmax : IsCoefficientMaximizer d A u) {v : Torus d → ℝ} (hvu : v =ᵐ[torusMeasure d] u) :
    normalizedGibbs v =ᵐ[torusMeasure d]
      normalizedGibbs (Gap.densityPotential (Gap.coefficient d A)
        (fun y => normalizedGibbs v y - 1)) := by
  have hu := hmax.1
  have hm := hmax.2.1
  have hρ := normalizedGibbs_memLp_two hd hu hm
  have hae := ((coefficientMaximizer_iff hd hA hu hm).1 hmax).2
  have hg : normalizedGibbs v =ᵐ[torusMeasure d] normalizedGibbs u := Gap.gibbs_congr hvu
  have hρv : MemLp (normalizedGibbs v) 2 (torusMeasure d) := hρ.ae_eq hg.symm
  rw [densityPotential_sub_one _ hρv, Gap.densityPotential_congr _ hg]
  exact hg.trans (Gap.gibbs_congr hae)


end BecknerOnofri.V2.Reaudit.Attainment
