import BecknerOnofri.Friedrichs.MixedCoordinateWeak
import Mathlib.Topology.Algebra.Module.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ContDiff
namespace BecknerOnofri.Friedrichs.MixedSpatial

lemma interiorSupport_add {d : ℕ} {α : MultiIndex d} {F G : Space d → ℝ}
    (hF : interiorSupport α F) (hG : interiorSupport α G) : interiorSupport α (F+G) := by
  obtain ⟨δ,hδ,hF⟩ := hF
  obtain ⟨ε,hε,hG⟩ := hG
  refine ⟨min δ ε,lt_min hδ hε,?_⟩
  rintro x ⟨i,hi,hx⟩
  have hf : F x=0 := hF x ⟨i,hi,hx.imp (fun h => h.trans (min_le_left _ _))
    (fun h => by linarith [min_le_left δ ε])⟩
  have hg : G x=0 := hG x ⟨i,hi,hx.imp (fun h => h.trans (min_le_right _ _))
    (fun h => by linarith [min_le_right δ ε])⟩
  simp [hf,hg]

lemma interiorSupport_smul {d : ℕ} {α : MultiIndex d} {F : Space d → ℝ}
    (hF : interiorSupport α F) (c : ℝ) : interiorSupport α (c • F) := by
  obtain ⟨δ,hδ,hF⟩ := hF
  exact ⟨δ,hδ,fun x hx => by simp [hF x hx]⟩

lemma partialDerivative_add {d : ℕ} {F G : Space d → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (i : Fin d) :
    partialDerivative i (F+G)=partialDerivative i F+partialDerivative i G := by
  funext x
  simp only [partialDerivative,fderiv_add (hF.differentiable (by simp) x)
    (hG.differentiable (by simp) x),ContinuousLinearMap.add_apply,Pi.add_apply]

lemma partialDerivative_smul {d : ℕ} {F : Space d → ℝ}
    (hF : ContDiff ℝ ∞ F) (c : ℝ) (i : Fin d) :
    partialDerivative i (c • F)=c • partialDerivative i F := by
  funext x
  simp only [partialDerivative,fderiv_const_smul (hF.differentiable (by simp) x) c,
    ContinuousLinearMap.smul_apply,Pi.smul_apply]

lemma zero_mem_core {d : ℕ} (α : MultiIndex d) : (0 : EnergySpace α)∈core α := by
  refine ⟨0,⟨contDiff_const,?_,?_⟩,?_,?_,?_⟩
  · intro i hi x
    rfl
  · exact ⟨1,by norm_num,fun x hx => rfl⟩
  · exact Lp.coeFn_zero ℝ 2 (spatialMeasure α)
  · intro i
    filter_upwards [Lp.coeFn_zero ℝ 2 (spatialMeasure α)] with x hx
    change (0 : H α) x=partialDerivative i 0 x
    simpa [partialDerivative] using hx
  · intro i
    filter_upwards [Lp.coeFn_zero ℝ 2 (spatialMeasure α)] with x hx
    change (0 : H α) x=SpatialForm.potentialFactor (α i) (x i)*0
    simpa only [Pi.zero_apply,mul_zero] using hx

lemma add_mem_core {d : ℕ} {α : MultiIndex d} {u v : EnergySpace α}
    (hu : u∈core α) (hv : v∈core α) : u+v∈core α := by
  obtain ⟨F,hF,hu0,hu1,huV⟩ := hu
  obtain ⟨G,hG,hv0,hv1,hvV⟩ := hv
  refine ⟨F+G,⟨hF.1.add hG.1,?_,interiorSupport_add hF.2.2 hG.2.2⟩,?_,?_,?_⟩
  · intro i hi x
    simp only [Pi.add_apply,hF.2.1 i hi x,hG.2.1 i hi x]
  · exact (Lp.coeFn_add u.1 v.1).trans (hu0.add hv0)
  · intro i
    rw [partialDerivative_add hF.1 hG.1]
    exact (Lp.coeFn_add (u.2.1 i) (v.2.1 i)).trans ((hu1 i).add (hv1 i))
  · intro i
    filter_upwards [Lp.coeFn_add (u.2.2 i) (v.2.2 i),huV i,hvV i] with x hx hf hg
    change (u.2.2 i+v.2.2 i) x=SpatialForm.potentialFactor (α i) (x i)*(F x+G x)
    rw [hx]
    simp only [Pi.add_apply,hf,hg,mul_add]

lemma smul_mem_core {d : ℕ} {α : MultiIndex d} {u : EnergySpace α}
    (hu : u∈core α) (c : ℝ) : c • u∈core α := by
  obtain ⟨F,hF,hu0,hu1,huV⟩ := hu
  refine ⟨c • F,⟨contDiff_const.smul hF.1,?_,interiorSupport_smul hF.2.2 c⟩,?_,?_,?_⟩
  · intro i hi x
    simp only [Pi.smul_apply,hF.2.1 i hi x]
  · exact (Lp.coeFn_smul c u.1).trans (hu0.const_smul c)
  · intro i
    rw [partialDerivative_smul hF.1]
    exact (Lp.coeFn_smul c (u.2.1 i)).trans ((hu1 i).const_smul c)
  · intro i
    filter_upwards [Lp.coeFn_smul c (u.2.2 i),huV i] with x hx hf
    change (c • u.2.2 i) x=SpatialForm.potentialFactor (α i) (x i)*(c • F x)
    rw [hx]
    simp only [Pi.smul_apply,smul_eq_mul,hf]
    ring

def coreSubmodule {d : ℕ} (α : MultiIndex d) : Submodule ℝ (EnergySpace α) where
  carrier := core α
  zero_mem' := zero_mem_core α
  add_mem' := add_mem_core
  smul_mem' := fun c _ hu => smul_mem_core hu c

def closedFormSubmodule {d : ℕ} (α : MultiIndex d) : Submodule ℝ (EnergySpace α) :=
  (coreSubmodule α).topologicalClosure

@[simp] lemma mem_closedFormSubmodule {d : ℕ} (α : MultiIndex d) (u : EnergySpace α) :
    u∈closedFormSubmodule α ↔ u∈formClosure α := Iff.rfl

#print axioms closedFormSubmodule
end BecknerOnofri.Friedrichs.MixedSpatial
