import BecknerOnofri.Definitions
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.GroupTheory.Divisible

/-! The genuine two-copy torus transformation used by the Ginibre inequality.
Its finite covering degree is handled by normalized Haar measure; injectivity
is neither asserted nor needed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace BecknerOnofri.HighDim.GinibreHaar

def doubleMap (d : ℕ) : Torus d × Torus d →+ Torus d × Torus d where
  toFun p := (p.1+p.2,p.1-p.2)
  map_zero' := by simp
  map_add' p q := by
    apply Prod.ext <;> dsimp <;> abel

@[simp] theorem doubleMap_apply {d : ℕ} (p : Torus d × Torus d) :
    doubleMap d p=(p.1+p.2,p.1-p.2) := rfl

theorem doubleMap_surjective (d : ℕ) : Function.Surjective (doubleMap d) := by
  intro p
  obtain ⟨a,ha⟩ := DivisibleBy.surjective_smul (Torus d) ℤ (by norm_num : (2:ℤ)≠0) (p.1+p.2)
  refine ⟨(a,p.1-a),?_⟩
  apply Prod.ext
  · change a+(p.1-a)=p.1
    abel
  · change a-(p.1-a)=p.2
    have he : a+a=p.1+p.2 := by simpa only [two_zsmul] using ha
    calc
      _ = a+a-p.1 := by abel
      _ = p.2 := by rw [he]; abel

theorem doubleMap_continuous (d : ℕ) : Continuous (doubleMap d) :=
  (continuous_fst.add continuous_snd).prodMk (continuous_fst.sub continuous_snd)

theorem doubleMap_measurePreserving (d : ℕ) :
    MeasurePreserving (doubleMap d) ((torusMeasure d).prod (torusMeasure d))
      ((torusMeasure d).prod (torusMeasure d)) := by
  letI : (torusMeasure d).IsAddHaarMeasure := by
    unfold torusMeasure
    infer_instance
  letI : ((torusMeasure d).prod (torusMeasure d)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure (torusMeasure d) (torusMeasure d)
  exact (doubleMap d).measurePreserving (doubleMap_continuous d) (doubleMap_surjective d) rfl

#print axioms doubleMap_measurePreserving
end BecknerOnofri.HighDim.GinibreHaar
