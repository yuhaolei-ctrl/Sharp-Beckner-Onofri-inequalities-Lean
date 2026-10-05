import BecknerOnofri.SmoothTorusDifferentiation
import BecknerOnofri.CompactComplexDifferentiation
import BecknerOnofri.Translation
import Mathlib.Analysis.Fourier.AddCircle

/-! Fourier differentiation from the raw smooth periodic lift. The identity is
proved by differentiating the exact Haar translation identity. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace BecknerOnofri.SmoothTorus
open HighDim

local instance (d : ℕ) : Measure.IsAddRightInvariant (torusMeasure d) := by
  unfold torusMeasure
  infer_instance

def coefficient {d : ℕ} (f : Torus d → ℂ) (k : Frequency d) : ℂ :=
  ∫ x,UnitAddTorus.mFourier (-k) x * f x ∂torusMeasure d

theorem coefficient_translate {d : ℕ} (f : Torus d → ℂ) (k : Frequency d)
    (a : Torus d) :
    coefficient (fun x => f (x+a)) k = UnitAddTorus.mFourier k a * coefficient f k := by
  unfold coefficient
  rw [← integral_sub_right_eq_self
    (fun x => UnitAddTorus.mFourier (-k) x * f (x+a)) a]
  simp only [sub_add_cancel,sub_eq_add_neg,mFourier_add_argument]
  have hn : UnitAddTorus.mFourier (-k) (-a) = UnitAddTorus.mFourier k a := by
    simp only [UnitAddTorus.mFourier,ContinuousMap.coe_mk,Pi.neg_apply,fourier_apply,
      neg_zsmul, zsmul_neg,neg_neg]
  rw [hn,← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    have he : x + -a + a = x := by abel
    dsimp only
    rw [he]
    ring)

theorem character_axis {d : ℕ} (k : Frequency d) (j : Fin d) (t : ℝ) :
    UnitAddTorus.mFourier k (axis j t) = fourier (k j) (t : UnitAddCircle) := by
  classical
  simp only [UnitAddTorus.mFourier,ContinuousMap.coe_mk,axis,quotient]
  rw [Finset.prod_eq_single j]
  · simp
  · intro i _ hij
    simp [Pi.single_eq_of_ne hij,fourier_eval_zero]
  · simp

theorem coefficient_partial {d : ℕ} {f : Torus d → ℂ} (hf : Smooth f)
    (j : Fin d) (k : Frequency d) :
    coefficient (coordinateDeriv j f) k =
      (2*(Real.pi:ℂ)*Complex.I*(k j)) * coefficient f k := by
  let F : ℝ → Torus d → ℂ := fun t x => UnitAddTorus.mFourier (-k) x * f (x+axis j t)
  let D : ℝ → Torus d → ℂ := fun t x =>
    UnitAddTorus.mFourier (-k) x * coordinateDeriv j f (x+axis j t)
  have hshift : Continuous (fun p : ℝ × Torus d => p.2+axis j p.1) :=
    continuous_snd.add ((axis_continuous j).comp continuous_fst)
  have hF : Continuous F.uncurry :=
    ((UnitAddTorus.mFourier (-k)).continuous.comp continuous_snd).mul
      ((smooth_continuous hf).comp hshift)
  have hD : Continuous D.uncurry :=
    ((UnitAddTorus.mFourier (-k)).continuous.comp continuous_snd).mul
      ((smooth_continuous (partial_smooth hf j)).comp hshift)
  have h := CompactParameter.complex_integral_hasDerivAt (torusMeasure d) F D hF hD
    (fun t x => (partial_hasDerivAt hf j x t).const_mul _) 0
  have heq : (fun t => ∫ x,F t x ∂torusMeasure d) =
      (fun t : ℝ => fourier (k j) (t : UnitAddCircle) * coefficient f k) := by
    funext t
    change coefficient (fun x => f (x+axis j t)) k = _
    rw [coefficient_translate,character_axis]
  rw [heq] at h
  have h' := (hasDerivAt_fourier (1:ℝ) (k j) 0).mul_const (coefficient f k)
  have hd := h.unique h'
  have hz : axis j 0 = 0 := by ext i; simp [axis,quotient]
  simpa [D,hz,coefficient,fourier_eval_zero] using hd

theorem coefficient_iterPartial {d : ℕ} {f : Torus d → ℂ} (hf : Smooth f)
    (j : Fin d) (m : ℕ) (k : Frequency d) :
    coefficient (iterPartial j f m) k =
      (2*(Real.pi:ℂ)*Complex.I*(k j))^m * coefficient f k := by
  induction m with
  | zero => simp [iterPartial]
  | succ m ih =>
    rw [iterPartial,coefficient_partial (iterPartial_smooth hf j m),ih,pow_succ]
    ring

#print axioms coefficient_partial
#print axioms coefficient_iterPartial
end BecknerOnofri.SmoothTorus
