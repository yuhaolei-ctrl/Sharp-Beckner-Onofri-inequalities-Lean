module

public import BecknerOnofri.Translation
public import BecknerOnofri.Statement

@[expose] public section

/-! # Translation invariance of the Morse--Bott structure

If `FullModeMorseBott β u` holds then it holds for every translate `x ↦ u(x - a)`: this is the
statement that the Morse--Bott property holds at *each* point of the translation orbit, not only at
the base point. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal

namespace BecknerOnofri.V2.Reaudit.MorseBott
open BecknerOnofri.HighDim

local instance (d : ℕ) : Measure.IsAddRightInvariant (torusMeasure d) := by
  unfold torusMeasure
  infer_instance

theorem translate_neg_translate {d : ℕ} (h : Torus d → ℝ) (a : Torus d) :
    translate (translate h (-a)) a = h := by
  rw [translate_translate, neg_add_cancel, translate_zero]

theorem translate_translate_neg {d : ℕ} (h : Torus d → ℝ) (a : Torus d) :
    translate (translate h a) (-a) = h := by
  rw [translate_translate, add_neg_cancel, translate_zero]

theorem translate_sub {d : ℕ} (f g : Torus d → ℝ) (a : Torus d) :
    translate (fun x => f x - g x) a = fun x => translate f a x - translate g a x := rfl

theorem ae_eq_translate_iff {d : ℕ} (f g : Torus d → ℝ) (a : Torus d) :
    translate f a =ᵐ[torusMeasure d] translate g a ↔ f =ᵐ[torusMeasure d] g := by
  constructor
  · intro h
    have := (translation_measurePreserving (-a)).quasiMeasurePreserving.ae_eq_comp h
    change translate (translate f a) (-a) =ᵐ[torusMeasure d] translate (translate g a) (-a) at this
    rwa [translate_translate_neg, translate_translate_neg] at this
  · intro h
    exact (translation_measurePreserving a).quasiMeasurePreserving.ae_eq_comp h

/-- Translation preserves smoothness. -/
theorem smoothOnTorus_translate' {d : ℕ} {u : Torus d → ℝ} (hs : SmoothOnTorus u) (a : Torus d) :
    SmoothOnTorus (translate u a) := by
  obtain ⟨t, ht⟩ : ∃ t : Fin d → ℝ, a = fun j => (t j : UnitAddCircle) := by
    refine ⟨fun j => (a j).out, ?_⟩
    funext j
    exact (QuotientAddGroup.out_eq' (a j)).symm
  unfold SmoothOnTorus at hs ⊢
  have : (fun x : Fin d → ℝ => translate u a (fun j => (x j : UnitAddCircle))) =
      (fun x : Fin d → ℝ => u (fun j => (x j : UnitAddCircle))) ∘ (fun x => x - t) := by
    funext x
    simp only [translate, Function.comp, ht]
    congr 1
  rw [this]
  exact hs.comp (contDiff_id.sub contDiff_const)

/-- The Euler--Lagrange (stationarity) equation in Fourier form at coupling `μ = β/β_s`:
`|k|^d û(k) = μ \widehat{e^u/Z}(k)` for `k ≠ 0` (equation `(5.normalized-critical-equation)`). -/
def IsCritical {d : ℕ} (μ : ℝ) (v : Torus d → ℝ) : Prop :=
  ∀ k : NonzeroFrequency d, (frequencyLength k.val ^ d : ℂ) * fourierCoeff v k.val =
    (μ : ℂ) * fourierCoeff (normalizedGibbs v) k.val

theorem isCritical_translate {d : ℕ} {μ : ℝ} {v : Torus d → ℝ} (h : IsCritical μ v) (a : Torus d) :
    IsCritical μ (translate v a) := by
  intro k
  rw [normalizedGibbs_translate, fourierCoeff_translate, fourierCoeff_translate]
  have := h k
  linear_combination (UnitAddTorus.mFourier (-k.val) a) * this

theorem isCritical_translate_iff {d : ℕ} {μ : ℝ} {v : Torus d → ℝ} (a : Torus d) :
    IsCritical μ (translate v a) ↔ IsCritical μ v := by
  refine ⟨fun h => ?_, fun h => isCritical_translate h a⟩
  simpa only [translate_translate_neg] using isCritical_translate h (-a)

theorem isCritical_of_stationary {d : ℕ} {β : ℝ} {u : Torus d → ℝ}
    (h : ∀ k : NonzeroFrequency d, (frequencyLength k.val ^ d : ℂ) * fourierCoeff u k.val =
      (β / spectralThreshold d : ℝ) * fourierCoeff (normalizedGibbs u) k.val) :
    IsCritical (β / spectralThreshold d) u := h

/-- **Translation invariance of `FullModeMorseBott`**: every point of the orbit is a Morse--Bott
point with the same constants. -/
theorem fullModeMorseBott_translate {d : ℕ} {β : ℝ} {u : Torus d → ℝ}
    (hu : FullModeMorseBott β u) (a : Torus d) : FullModeMorseBott β (translate u a) where
  smooth := smoothOnTorus_translate' hu.smooth a
  sobolev := fun s hs => (inSobolev_translate_iff s u a).mpr (hu.sobolev s hs)
  criticalSobolev := (inCriticalSobolev_translate_iff u a).mpr hu.criticalSobolev
  meanZero := (meanZero_translate_iff u a).mpr hu.meanZero
  stationary := isCritical_translate (μ := β / spectralThreshold d) hu.stationary a
  fullModes := fun j => by
    rw [Ne, fourierCoeff_translate_eq_zero_iff]; exact hu.fullModes j
  tangentIndependent := fun c hc => by
    apply hu.tangentIndependent c
    rw [tangentCombination_translate] at hc
    have : translate (tangentCombination u c) a =ᵐ[torusMeasure d] translate (fun _ => (0 : ℝ)) a := hc
    exact (ae_eq_translate_iff _ _ a).mp this
  hessianNonpos := fun h hc hm => by
    have h' : translate (translate h (-a)) a = h := translate_neg_translate h a
    rw [← h', secondVariation_translate]
    exact hu.hessianNonpos _ ((inCriticalSobolev_translate_iff h (-a)).mpr hc)
      ((meanZero_translate_iff h (-a)).mpr hm)
  hessianKernel := fun h hc hm => by
    have h' : translate (translate h (-a)) a = h := translate_neg_translate h a
    have hc' := (inCriticalSobolev_translate_iff h (-a)).mpr hc
    have hm' := (meanZero_translate_iff h (-a)).mpr hm
    have key := hu.hessianKernel _ hc' hm'
    conv_lhs => rw [← h', secondVariation_translate]
    rw [key]
    constructor
    · rintro ⟨c, hcc⟩
      refine ⟨c, ?_⟩
      rw [tangentCombination_translate]
      have := (ae_eq_translate_iff _ _ a).mpr hcc
      rwa [h'] at this
    · rintro ⟨c, hcc⟩
      refine ⟨c, ?_⟩
      rw [tangentCombination_translate] at hcc
      have := (ae_eq_translate_iff _ _ (-a)).mpr hcc
      simpa only [translate_translate_neg] using this
  normalCoercivity := by
    obtain ⟨c, hc, hcoer⟩ := hu.normalCoercivity
    refine ⟨c, hc, fun h hcr hS hm hperp => ?_⟩
    have h' : translate (translate h (-a)) a = h := translate_neg_translate h a
    have key := hcoer (translate h (-a)) ((inCriticalSobolev_translate_iff h (-a)).mpr hcr)
      ((inSobolev_translate_iff _ h (-a)).mpr hS) ((meanZero_translate_iff h (-a)).mpr hm)
      (fun j => by
        have hj := hperp j
        rw [coordinateDerivative_translate] at hj
        have e : (∫ x, translate h (-a) x * coordinateDerivative u j x ∂torusMeasure d) =
            ∫ x, h x * translate (coordinateDerivative u j) a x ∂torusMeasure d := by
          rw [← integral_add_right_eq_self
            (fun x => h x * translate (coordinateDerivative u j) a x) a]
          refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
          simp only [translate, sub_neg_eq_add, add_sub_cancel_right]
        rw [e]; exact hj)
    rw [← h', secondVariation_translate, sobolevNorm_translate]
    exact key
  localMaximum := by
    intro s hs
    obtain ⟨r, hr, hlm⟩ := hu.localMaximum s hs
    refine ⟨r, hr, fun v hSv hcv hmv hSd hn => ?_⟩
    have hd' : (fun x => translate v (-a) x - u x) =
        translate (fun x => v x - translate u a x) (-a) := by
      funext x
      simp only [translate, sub_neg_eq_add, add_sub_cancel_right]
    have key := hlm (translate v (-a)) ((inSobolev_translate_iff s v (-a)).mpr hSv)
      ((inCriticalSobolev_translate_iff v (-a)).mpr hcv) ((meanZero_translate_iff v (-a)).mpr hmv)
      (by rw [hd']; exact (inSobolev_translate_iff s _ (-a)).mpr hSd)
      (by rw [hd', sobolevNorm_translate]; exact hn)
    simpa only [dualFunctional_translate] using key

end BecknerOnofri.V2.Reaudit.MorseBott

#print axioms BecknerOnofri.V2.Reaudit.MorseBott.isCritical_translate
#print axioms BecknerOnofri.V2.Reaudit.MorseBott.isCritical_translate_iff
#print axioms BecknerOnofri.V2.Reaudit.MorseBott.fullModeMorseBott_translate
