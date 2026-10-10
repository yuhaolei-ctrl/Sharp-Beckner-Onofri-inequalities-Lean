module

public import BecknerOnofri.V2.Reaudit.MorseBott.OrbitMap
public import BecknerOnofri.V2.Reaudit.MorseBott.TranslateInvariance
public import BecknerOnofri.LegacyBridge

@[expose] public section

/-! # The tangent space of the orbit is the Hessian kernel

For a smooth `p`, `\widehat{∂_j p}(k) = 2π i k_j \hat p(k)`, hence
`encode (Σ_j c_j ∂_j p) = DΓ(t)(-c)` for the orbit map `Γ` of `p = u(· - t)`.  Together with
Fourier uniqueness in `L²`, the tangent space `range DΓ(t)` (inside `H^s`) is identified with the
set of `h` with `h =ᵐ tangentCombination p c`. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

namespace BecknerOnofri.V2.Reaudit.MorseBott
open BecknerOnofri.HighDim

theorem axis_eq {d : ℕ} (j : Fin d) (t : ℝ) :
    (fun i : Fin d => if i = j then ((t : ℝ) : UnitAddCircle) else 0) = SmoothTorus.axis j t := by
  funext i
  by_cases h : i = j
  · subst h; simp [SmoothTorus.axis, SmoothTorus.quotient]
  · simp [SmoothTorus.axis, SmoothTorus.quotient, h]

/-- The real coordinate derivative of a smooth real function is the real part of the complex one,
and in fact the complex one is real. -/
theorem coordinateDeriv_ofReal {d : ℕ} {p : Torus d → ℝ} (hp : SmoothOnTorus p) (j : Fin d)
    (x : Torus d) :
    SmoothTorus.coordinateDeriv j (fun y => (p y : ℂ)) x = ((coordinateDerivative p j x : ℝ) : ℂ) := by
  have hf := SmoothTorus.of_real hp
  have h0 := SmoothTorus.partial_hasDerivAt hf j x 0
  have hz : SmoothTorus.axis j 0 = 0 := by
    ext i; simp [SmoothTorus.axis, SmoothTorus.quotient]
  rw [hz, add_zero] at h0
  set D := SmoothTorus.coordinateDeriv j (fun y => (p y : ℂ)) x with hD
  -- real part
  have hre : HasDerivAt (fun t : ℝ => p (x + SmoothTorus.axis j t)) D.re 0 := by
    have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h0
    simpa [Function.comp_def] using this
  have hder : coordinateDerivative p j x = D.re := by
    unfold coordinateDerivative
    simp only [axis_eq]
    exact hre.deriv
  have h1 : HasDerivAt (fun t : ℝ => ((p (x + SmoothTorus.axis j t) : ℝ) : ℂ)) ((D.re : ℝ) : ℂ) 0 :=
    hre.ofReal_comp
  have h2 := h0.unique h1
  rw [hder]
  exact h2

theorem coordinateDerivative_smooth {d : ℕ} {p : Torus d → ℝ} (hp : SmoothOnTorus p) (j : Fin d) :
    SmoothOnTorus (coordinateDerivative p j) := by
  have h := SmoothTorus.partial_smooth (SmoothTorus.of_real hp) j
  unfold SmoothTorus.Smooth at h
  unfold SmoothOnTorus
  have : (fun x : Fin d → ℝ => coordinateDerivative p j (fun i => (x i : UnitAddCircle))) =
      fun x => Complex.re (SmoothTorus.coordinateDeriv j (fun y => (p y : ℂ))
        (SmoothTorus.quotient x)) := by
    funext x
    rw [coordinateDeriv_ofReal hp]
    simp [SmoothTorus.quotient]
    rfl
  rw [this]
  exact Complex.reCLM.contDiff.comp h

theorem fourierCoeff_coordinateDerivative {d : ℕ} {p : Torus d → ℝ} (hp : SmoothOnTorus p)
    (j : Fin d) (k : Frequency d) :
    HighDim.fourierCoeff (coordinateDerivative p j) k =
      (2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ)) * HighDim.fourierCoeff p k := by
  have h := SmoothTorus.coefficient_partial (SmoothTorus.of_real hp) j k
  have e1 : HighDim.fourierCoeff (coordinateDerivative p j) k =
      SmoothTorus.coefficient (SmoothTorus.coordinateDeriv j (fun y => (p y : ℂ))) k := by
    unfold HighDim.fourierCoeff SmoothTorus.coefficient
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [coordinateDeriv_ofReal hp]
  have e2 : HighDim.fourierCoeff p k = SmoothTorus.coefficient (fun y => (p y : ℂ)) k := rfl
  rw [e1, e2]
  exact h

theorem tangentCombination_smooth {d : ℕ} {p : Torus d → ℝ} (hp : SmoothOnTorus p) (c : Fin d → ℝ) :
    SmoothOnTorus (tangentCombination p c) := by
  unfold SmoothOnTorus
  have : (fun x : Fin d → ℝ => tangentCombination p c (fun i => (x i : UnitAddCircle))) =
      fun x => ∑ j : Fin d, c j * coordinateDerivative p j (fun i => (x i : UnitAddCircle)) := by
    funext x; rfl
  rw [this]
  exact ContDiff.sum (fun j _ => contDiff_const.mul (coordinateDerivative_smooth hp j))

theorem fourierCoeff_tangentCombination {d : ℕ} {p : Torus d → ℝ} (hp : SmoothOnTorus p)
    (c : Fin d → ℝ) (k : Frequency d) :
    HighDim.fourierCoeff (tangentCombination p c) k =
      (2 * (Real.pi : ℂ) * Complex.I * ((∑ j, c j * (k j : ℝ) : ℝ) : ℂ)) * HighDim.fourierCoeff p k := by
  have hcont : ∀ j : Fin d, Continuous (coordinateDerivative p j) := fun j =>
    SmoothTorus.real_continuous (coordinateDerivative_smooth hp j)
  unfold HighDim.fourierCoeff
  have hint : ∀ j : Fin d, Integrable (fun x => UnitAddTorus.mFourier (-k) x *
      ((c j * coordinateDerivative p j x : ℝ) : ℂ)) (torusMeasure d) := by
    intro j
    exact (((UnitAddTorus.mFourier (-k)).continuous.mul
      (Complex.continuous_ofReal.comp (continuous_const.mul (hcont j)))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
  have : (fun x => UnitAddTorus.mFourier (-k) x * ((tangentCombination p c x : ℝ) : ℂ)) =
      fun x => ∑ j : Fin d, UnitAddTorus.mFourier (-k) x *
        ((c j * coordinateDerivative p j x : ℝ) : ℂ) := by
    funext x
    simp only [tangentCombination, Complex.ofReal_sum, Finset.mul_sum]
  rw [this, integral_finsetSum _ (fun j _ => hint j)]
  have hj : ∀ j : Fin d, (∫ x, UnitAddTorus.mFourier (-k) x *
      ((c j * coordinateDerivative p j x : ℝ) : ℂ) ∂torusMeasure d) =
      (c j : ℂ) * ((2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ)) * fourierCoeff p k) := by
    intro j
    rw [← fourierCoeff_coordinateDerivative hp j k]
    unfold HighDim.fourierCoeff
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Complex.ofReal_mul]
    ring
  simp only [hj]
  have hsum : (∑ j : Fin d, (c j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ))) =
      2 * (Real.pi : ℂ) * Complex.I * ((∑ j, c j * (k j : ℝ) : ℝ) : ℂ) := by
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [← hsum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  unfold HighDim.fourierCoeff
  ring


theorem fourierCoeff_congr_ae {d : ℕ} {f g : Torus d → ℝ} (h : f =ᵐ[torusMeasure d] g)
    (k : Frequency d) : HighDim.fourierCoeff f k = HighDim.fourierCoeff g k := by
  unfold HighDim.fourierCoeff
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx]

theorem inSobolev_congr_ae {d : ℕ} {s : ℝ} {f g : Torus d → ℝ} (h : f =ᵐ[torusMeasure d] g)
    (hg : InSobolev s g) : InSobolev s f := by
  refine ⟨hg.1.ae_eq h.symm, ?_⟩
  have : sobolevTerm s f = sobolevTerm s g := by
    funext k; unfold sobolevTerm; rw [fourierCoeff_congr_ae h k]
  rw [this]; exact hg.2

/-- **Fourier uniqueness in `L²`** for real functions on the torus. -/
theorem ae_eq_of_fourierCoeff_eq {d : ℕ} {f g : Torus d → ℝ}
    (hf : MemLp f 2 (torusMeasure d)) (hg : MemLp g 2 (torusMeasure d))
    (h : ∀ k : Frequency d, HighDim.fourierCoeff f k = HighDim.fourierCoeff g k) :
    f =ᵐ[torusMeasure d] g := by
  have hp : Bridge.potentialLp f hf = Bridge.potentialLp g hg := by
    apply (Legacy.BecknerOnofri.TorusSobolev.fourierIsometry d).injective
    ext k
    rw [Bridge.potentialLp_fourier, Bridge.potentialLp_fourier]
    exact h k
  filter_upwards [Bridge.potentialLp_ae f hf, Bridge.potentialLp_ae g hg] with x h1 h2
  have : (f x : ℂ) = (g x : ℂ) := by rw [← h1, ← h2, hp]
  exact_mod_cast this

section Tangent
variable {d : ℕ} {s : ℝ} {u : Torus d → ℝ}

/-- The Fourier coefficients of `Σ c_j ∂_j p` in the weighted `ℓ²` model are `DΓ(t)(-c)`. -/
theorem encode_tangentCombination (hd : 0 < d) (hall : ∀ σ : ℝ, 0 ≤ σ → InSobolev σ u)
    (hs : 0 ≤ s) (hu : InSobolev s u) (hsm : SmoothOnTorus u) (t : Fin d → ℝ) (c : Fin d → ℝ)
    (hS : InSobolev s (tangentCombination (translate u (lift t)) c)) :
    encodeSobolev (tangentCombination (translate u (lift t)) c) hS =
      fderiv ℝ (orbitMap hu) t (-c) := by
  have hps : SmoothOnTorus (translate u (lift t)) := smoothOnTorus_translate' hsm (lift t)
  ext k
  rw [encodeSobolev_apply, fderiv_orbitMap_apply hd hall hs hu, orbitMap_apply,
    ell_apply]
  unfold scaledFourier
  rw [fourierCoeff_tangentCombination hps, fourierCoeff_translate]
  rw [mFourier_neg_lift]
  simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  push_cast
  have : ∑ x, (c x : ℂ) * (k x : ℂ) = ∑ x, (k x : ℂ) * (c x : ℂ) :=
    Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [this]
  ring

/-- **The tangent space of the orbit is the Hessian-kernel space.**  For `p = u(· - t)`, a function
`h` is of the form `Σ_j c_j ∂_j p` (the kernel description in `FullModeMorseBott.hessianKernel`) iff
it lies in `H^s` and its `H^s` coordinates lie in the range of the differential of the orbit map. -/
theorem tangent_iff_range_fderiv (hd : 0 < d) (hall : ∀ σ : ℝ, 0 ≤ σ → InSobolev σ u)
    (hs : 0 ≤ s) (hu : InSobolev s u) (hsm : SmoothOnTorus u) (t : Fin d → ℝ)
    (h : Torus d → ℝ) :
    (∃ c : Fin d → ℝ, h =ᵐ[torusMeasure d] tangentCombination (translate u (lift t)) c) ↔
      ∃ hS : InSobolev s h, encodeSobolev h hS ∈ Set.range (fderiv ℝ (orbitMap hu) t) := by
  have hps : SmoothOnTorus (translate u (lift t)) := smoothOnTorus_translate' hsm (lift t)
  constructor
  · rintro ⟨c, hc⟩
    have hT : InSobolev s (tangentCombination (translate u (lift t)) c) :=
      SmoothTorus.smooth_mem_sobolev (tangentCombination_smooth hps c) s
    have hS : InSobolev s h := inSobolev_congr_ae hc hT
    refine ⟨hS, -c, ?_⟩
    rw [← encode_tangentCombination hd hall hs hu hsm t c hT]
    ext k
    simp only [encodeSobolev_apply, scaledFourier, fourierCoeff_congr_ae hc k]
  · rintro ⟨hS, v, hv⟩
    refine ⟨-v, ?_⟩
    have hps' := hps
    have hT : InSobolev s (tangentCombination (translate u (lift t)) (-v)) :=
      SmoothTorus.smooth_mem_sobolev (tangentCombination_smooth hps _) s
    have h1 := encode_tangentCombination hd hall hs hu hsm t (-v) hT
    rw [neg_neg] at h1
    refine ae_eq_of_fourierCoeff_eq hS.1 hT.1 (fun k => ?_)
    have h2 : encodeSobolev h hS k = encodeSobolev _ hT k := by rw [h1, hv]
    simp only [encodeSobolev_apply, scaledFourier] at h2
    have hne : ((sobolevScale s k : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (sobolevScale_pos s k).ne'
    exact mul_left_cancel₀ hne h2

end Tangent

end BecknerOnofri.V2.Reaudit.MorseBott

#print axioms BecknerOnofri.V2.Reaudit.MorseBott.fourierCoeff_tangentCombination
#print axioms BecknerOnofri.V2.Reaudit.MorseBott.ae_eq_of_fourierCoeff_eq
#print axioms BecknerOnofri.V2.Reaudit.MorseBott.encode_tangentCombination
#print axioms BecknerOnofri.V2.Reaudit.MorseBott.tangent_iff_range_fderiv
