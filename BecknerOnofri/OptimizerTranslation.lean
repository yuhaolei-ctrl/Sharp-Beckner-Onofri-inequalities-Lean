module

public import BecknerOnofri.ContinuousSymmetry
public import BecknerOnofri.RawAttainment

@[expose] public section

/-! Translation transports actual raw and continuous global optimizers.
All comparison domains are the full raw critical Sobolev domain. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace BecknerOnofri.HighDim.OptimizerTranslation
open ContinuousGibbs ContinuousFirstShell ContinuousSymmetry

@[simp] theorem rawFunctional_translate {d : ℕ} (A : ℝ) (u : Torus d → ℝ)
    (a : Torus d) :
    RawAttainment.rawFunctional A (translate u a) = RawAttainment.rawFunctional A u := by
  simp only [RawAttainment.rawFunctional,logPartition_translate,potentialEnergy_translate]

/-- Translation preserves the full raw variational comparison. -/
theorem dual_maximizer_translate_iff {d : ℕ} (β : ℝ) (u : Torus d → ℝ)
    (a : Torus d) :
    (∀ v : Torus d → ℝ, InCriticalSobolev v →
      dualFunctional β v ≤ dualFunctional β (translate u a)) ↔
    (∀ v : Torus d → ℝ, InCriticalSobolev v →
      dualFunctional β v ≤ dualFunctional β u) := by
  simp only [dualFunctional_translate]

/-- Both admissibility and the global optimum are transported together. -/
theorem dual_optimizer_translate_iff {d : ℕ} (β : ℝ) (u : Torus d → ℝ)
    (a : Torus d) :
    (InCriticalSobolev (translate u a) ∧ MeanZero (translate u a) ∧
      ∀ v : Torus d → ℝ, InCriticalSobolev v →
        dualFunctional β v ≤ dualFunctional β (translate u a)) ↔
    (InCriticalSobolev u ∧ MeanZero u ∧
      ∀ v : Torus d → ℝ, InCriticalSobolev v → dualFunctional β v ≤ dualFunctional β u) := by
  simp only [inCriticalSobolev_translate_iff,meanZero_translate_iff,dualFunctional_translate]

theorem raw_optimizer_translate_iff {d : ℕ} (A : ℝ) (u : Torus d → ℝ)
    (a : Torus d) :
    (InCriticalSobolev (translate u a) ∧ MeanZero (translate u a) ∧
      ∀ v : Torus d → ℝ, InCriticalSobolev v →
        RawAttainment.rawFunctional A v ≤ RawAttainment.rawFunctional A (translate u a)) ↔
    (InCriticalSobolev u ∧ MeanZero u ∧
      ∀ v : Torus d → ℝ, InCriticalSobolev v →
        RawAttainment.rawFunctional A v ≤ RawAttainment.rawFunctional A u) := by
  simp only [inCriticalSobolev_translate_iff,meanZero_translate_iff,rawFunctional_translate]

@[simp] theorem coe_translation {d : ℕ} (a : Torus d) (u : Space d) :
    (translation a u : Torus d → ℝ) = translate u a := rfl

@[simp] theorem continuous_critical_translation_iff {d : ℕ} (a : Torus d) (u : Space d) :
    InCriticalSobolev (translation a u) ↔ InCriticalSobolev u :=
  inCriticalSobolev_translate_iff u a

@[simp] theorem continuous_meanZero_translation_iff {d : ℕ} (a : Torus d) (u : Space d) :
    MeanZero (translation a u) ↔ MeanZero u := meanZero_translate_iff u a

@[simp] theorem continuous_dual_translation {d : ℕ} (β : ℝ) (a : Torus d) (u : Space d) :
    dualFunctional β (translation a u) = dualFunctional β u := dualFunctional_translate β u a

theorem continuous_optimizer_translation_iff {d : ℕ} (β : ℝ) (u : Space d)
    (a : Torus d) :
    (InCriticalSobolev (translation a u) ∧ MeanZero (translation a u) ∧
      ∀ v : Torus d → ℝ, InCriticalSobolev v →
        dualFunctional β v ≤ dualFunctional β (translation a u)) ↔
    (InCriticalSobolev u ∧ MeanZero u ∧
      ∀ v : Torus d → ℝ, InCriticalSobolev v → dualFunctional β v ≤ dualFunctional β u) :=
  dual_optimizer_translate_iff β u a

/-- A continuous global optimizer remains one after any actual torus translation. -/
theorem continuous_optimizer_translation {d : ℕ} (β : ℝ) (u : Space d)
    (hu : InCriticalSobolev u) (hm : MeanZero u)
    (hmax : ∀ v : Torus d → ℝ, InCriticalSobolev v → dualFunctional β v ≤ dualFunctional β u)
    (a : Torus d) :
    InCriticalSobolev (translation a u) ∧ MeanZero (translation a u) ∧
      ∀ v : Torus d → ℝ, InCriticalSobolev v →
        dualFunctional β v ≤ dualFunctional β (translation a u) :=
  (continuous_optimizer_translation_iff β u a).mpr ⟨hu,hm,hmax⟩

/-- The associated normalized density is transported by the same translation. -/
theorem continuous_gibbs_translation {d : ℕ} (u : Space d) (a : Torus d) :
    normalizedGibbs (translation a u) = translate (normalizedGibbs u) a :=
  normalizedGibbs_translate u a

#print axioms dual_optimizer_translate_iff
#print axioms continuous_optimizer_translation
#print axioms continuous_gibbs_translation
end BecknerOnofri.HighDim.OptimizerTranslation
