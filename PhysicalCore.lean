module

public import PhysicalLp
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff BigOperators
namespace BecknerOnofri.Paper2.Physical
open Friedrichs.MixedSpatial

abbrev EnergySpace {d : ℕ} (α : MultiIndex d) := H α × ((Fin d → H α) × (Fin d → H α))

def inactivePeriodic {d : ℕ} (α : MultiIndex d) (F : Space d → ℝ) : Prop :=
  ∀ i, α i=0 → ∀ x, F (Function.update x i (x i+1))=F x

def interiorSupport {d : ℕ} (α : MultiIndex d) (F : Space d → ℝ) : Prop :=
  ∃ δ : ℝ, 0<δ ∧ ∀ x, (∃ i, 0<α i ∧ (x i≤δ ∨ 1/2-δ≤x i)) → F x=0

def smoothCoreProfile {d : ℕ} (α : MultiIndex d) (F : Space d → ℝ) : Prop :=
  ContDiff ℝ ∞ F ∧ inactivePeriodic α F ∧ interiorSupport α F

def potentialFactor (m : ℕ) (x : ℝ) : ℝ :=
  scale * Friedrichs.SpatialForm.potentialFactor m (scale*x)

def core {d : ℕ} (α : MultiIndex d) : Set (EnergySpace α) :=
  {v | ∃ F : Space d → ℝ, smoothCoreProfile α F ∧
    (v.1 : Space d → ℝ)=ᵐ[spatialMeasure α] F ∧
    (∀ i,(v.2.1 i : Space d → ℝ)=ᵐ[spatialMeasure α] partialDerivative i F) ∧
    (∀ i,(v.2.2 i : Space d → ℝ)=ᵐ[spatialMeasure α]
      (fun x => potentialFactor (α i) (x i)*F x))}

def formClosure {d : ℕ} (α : MultiIndex d) : Set (EnergySpace α) := closure (core α)
def formPairing {d : ℕ} {α : MultiIndex d} (v w : EnergySpace α) : ℝ :=
  ∑ i, (inner ℝ (v.2.1 i) (w.2.1 i) + inner ℝ (v.2.2 i) (w.2.2 i))
def operatorGraph {d : ℕ} (α : MultiIndex d) (f g : H α) : Prop :=
  ∃ v : EnergySpace α, v.1=f ∧ v∈formClosure α ∧
    ∀ w∈formClosure α, formPairing v w=inner ℝ g w.1

lemma smoothCore_up {d : ℕ} {α : MultiIndex d} {F : Space d → ℝ}
    (hF : Friedrichs.MixedSpatial.smoothCoreProfile α F) :
    smoothCoreProfile α (fun x => F (up x)) := by
  obtain ⟨hs,hper,δ,hδ,hsupp⟩ := hF
  refine ⟨hs.comp (by unfold up; fun_prop), ?_, δ/scale, div_pos hδ scale_pos, ?_⟩
  · intro i hi x
    have he : up (Function.update x i (x i+1)) =
        Function.update (up x) i ((up x) i+2*Real.pi) := by
      ext j
      by_cases hj : j=i <;> simp [up,Function.update_apply,hj,scale] <;> ring
    dsimp only
    rw [he]
    exact hper i hi (up x)
  · intro x hx
    apply hsupp
    obtain ⟨i,hi,hx⟩ := hx
    refine ⟨i,hi,?_⟩
    rcases hx with hx|hx
    · left
      simpa [up,mul_comm] using (le_div_iff₀ scale_pos).mp hx
    · right
      have hm := (mul_le_mul_of_nonneg_left hx scale_pos.le)
      have hc : scale*(δ/scale)=δ := mul_div_cancel₀ δ scale_ne
      dsimp [up]
      rw [mul_sub, hc] at hm
      dsimp [scale] at hm ⊢
      linarith

lemma smoothCore_down {d : ℕ} {α : MultiIndex d} {F : Space d → ℝ}
    (hF : smoothCoreProfile α F) :
    Friedrichs.MixedSpatial.smoothCoreProfile α (fun x => F (down x)) := by
  obtain ⟨hs,hper,δ,hδ,hsupp⟩ := hF
  refine ⟨hs.comp (by unfold down; fun_prop), ?_, scale*δ, mul_pos scale_pos hδ, ?_⟩
  · intro i hi x
    have he : down (Function.update x i (x i+2*Real.pi)) =
        Function.update (down x) i ((down x) i+1) := by
      ext j
      by_cases hj : j=i <;> simp [down,Function.update_apply,hj,scale, mul_add,Real.pi_ne_zero] <;> field_simp
    dsimp only
    rw [he]
    exact hper i hi (down x)
  · intro x hx
    apply hsupp
    obtain ⟨i,hi,hx⟩ := hx
    refine ⟨i,hi,?_⟩
    dsimp [down]
    rw [inv_mul_eq_div]
    rcases hx with hx|hx
    · exact Or.inl ((div_le_iff₀ scale_pos).mpr (by nlinarith [hx]))
    · right
      apply (le_div_iff₀ scale_pos).mpr
      dsimp [scale] at hx ⊢
      nlinarith [hx]

lemma partial_comp_scale {d : ℕ} {F : Space d → ℝ} (hF : ContDiff ℝ ∞ F)
    (a : ℝ) (i : Fin d) (x : Space d) :
    partialDerivative i (fun y => F (a • y)) x = a * partialDerivative i F (a • x) := by
  have hd := (hF.differentiable (by simp)).differentiableAt.hasFDerivAt.comp x
    ((a • ContinuousLinearMap.id ℝ (Space d)).hasFDerivAt)
  change fderiv ℝ (fun y => F (a • y)) x (Pi.single i 1) = _
  convert! congrArg (fun L : Space d →L[ℝ] ℝ => L (Pi.single i 1)) hd.fderiv using 1
  simp [partialDerivative, ContinuousLinearMap.comp_apply]

lemma partial_up {d : ℕ} {F : Space d → ℝ} (hF : ContDiff ℝ ∞ F)
    (i : Fin d) (x : Space d) :
    partialDerivative i (fun y => F (up y)) x = scale * partialDerivative i F (up x) :=
  partial_comp_scale hF scale i x
lemma partial_down {d : ℕ} {F : Space d → ℝ} (hF : ContDiff ℝ ∞ F)
    (i : Fin d) (x : Space d) :
    partialDerivative i (fun y => F (down y)) x = scale⁻¹ * partialDerivative i F (down x) :=
  partial_comp_scale hF scale⁻¹ i x

lemma potentialFactor_sq (m : ℕ) (x : ℝ) :
    potentialFactor m x ^ 2 =
      (2*Real.pi)^2 * ((m:ℝ)*((m:ℝ)-1)) / Real.sin (2*Real.pi*x)^2 := by
  have hm : 0 ≤ (m:ℝ)*((m:ℝ)-1) := by
    cases m with
    | zero => norm_num
    | succ m => rw [Nat.cast_succ,add_sub_cancel_right]; positivity
  simp only [potentialFactor,Friedrichs.SpatialForm.potentialFactor,mul_pow,div_pow,
    Real.sq_sqrt hm,scale]
  ring

end BecknerOnofri.Paper2.Physical
