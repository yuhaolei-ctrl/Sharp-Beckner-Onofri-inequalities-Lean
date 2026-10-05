import BecknerOnofri.EntropyShearer.PositiveBounds

/-! Relative-entropy contraction under genuine product-Haar averaging. -/

noncomputable section
open MeasureTheory Function
open scoped BigOperators

namespace BecknerOnofri.HighDim.EntropyShearer

def entropyIntegral {d : ℕ} (f : Torus d → ℝ) : ℝ :=
  ∫ x, f x * Real.log (f x) ∂torusMeasure d

def relativeEntropy {d : ℕ} (f g : Torus d → ℝ) : ℝ :=
  ∫ x, f x * (Real.log (f x) - Real.log (g x)) ∂torusMeasure d

theorem entropy_difference {d : ℕ} {f : Torus d → ℝ}
    (hf : PositiveBounded f) (s : Finset (Fin d)) :
    relativeEntropy f (avg s f) = entropyIntegral f - entropyIntegral (avg s f) := by
  have hpair := integral_pairing s hf.bounded (hf.avg s).logBounded
    (fun x y => by rw [avg_update])
  unfold relativeEntropy entropyIntegral
  simp_rw [mul_sub]
  rw [integral_sub (hf.bounded.mul hf.logBounded).integrable
    (hf.bounded.mul (hf.avg s).logBounded).integrable, hpair]

theorem relativeEntropy_avg_le {d : ℕ} {f g : Torus d → ℝ}
    (hf : PositiveBounded f) (hg : PositiveBounded g) (s : Finset (Fin d)) :
    relativeEntropy (avg s f) (avg s g) ≤ relativeEntropy f g := by
  let F := avg s f
  let G := avg s g
  let t : Torus d → ℝ := fun x => Real.log (F x) - Real.log (G x)
  let q : Torus d → ℝ := fun x => F x / G x
  have hF : PositiveBounded F := hf.avg s
  have hG : PositiveBounded G := hg.avg s
  have ht : BoundedMeasurable t := hF.logBounded.sub hG.logBounded
  have hq : BoundedMeasurable q := by
    simpa only [q, div_eq_mul_inv] using hF.bounded.mul hG.invBounded
  have htInv : ∀ x y, t (updateFinset x s y) = t x := by
    intro x y
    simp only [t, F, G, avg_update]
  have hqInv : ∀ x y, q (updateFinset x s y) = q x := by
    intro x y
    simp only [q, F, G, avg_update]
  have hpair : (∫ x, f x * t x ∂torusMeasure d) = relativeEntropy F G :=
    integral_pairing s hf.bounded ht htInv
  have hmass : (∫ x, g x * q x ∂torusMeasure d) = ∫ x, f x ∂torusMeasure d := by
    rw [integral_pairing s hg.bounded hq hqInv]
    calc
      _ = ∫ x, F x ∂torusMeasure d := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by
          change G x * (F x / G x) = F x
          field_simp [(hG.pos x).ne'])
      _ = _ := integral_avg s hf.bounded
  have hpoint (x : Torus d) : f x * t x ≤
      (f x * (Real.log (f x) - Real.log (g x)) - f x) + g x * q x :=
    relative_young (hf.pos x) (hg.pos x) (hF.pos x) (hG.pos x)
  have hi := (hf.bounded.mul (hf.logBounded.sub hg.logBounded)).integrable
  have hineq := integral_mono (hf.bounded.mul ht).integrable
    ((hf.bounded.mul (hf.logBounded.sub hg.logBounded)).sub hf.bounded |>.add
      (hg.bounded.mul hq)).integrable hpoint
  rw [integral_add (f := fun x => f x * (Real.log (f x) - Real.log (g x)) - f x)
    (g := fun x => g x * q x) (hi.sub hf.bounded.integrable) (hg.bounded.mul hq).integrable,
    integral_sub hi hf.bounded.integrable, hmass, sub_add_cancel, hpair] at hineq
  exact hineq

#print axioms relativeEntropy_avg_le

end BecknerOnofri.HighDim.EntropyShearer
