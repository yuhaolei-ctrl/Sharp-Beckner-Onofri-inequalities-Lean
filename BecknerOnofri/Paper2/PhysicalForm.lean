module

public import BecknerOnofri.Paper2.PhysicalCore

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ContDiff BigOperators
namespace BecknerOnofri.Paper2.Physical
open Friedrichs.MixedSpatial

def scaledCoordinateEquiv {d : ℕ} (α : MultiIndex d) :
    Friedrichs.MixedSpatial.H α ≃L[ℝ] H α where
  toFun f := scale • coordinateLpEquiv α f
  invFun f := scale⁻¹ • (coordinateLpEquiv α).symm f
  map_add' f g := by simp [map_add,smul_add]
  map_smul' c f := by simp [map_smul,smul_smul,mul_comm]
  left_inv f := by simp [map_smul,smul_smul,scale_ne]
  right_inv f := by simp [map_smul,smul_smul,scale_ne]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def energyEquiv {d : ℕ} (α : MultiIndex d) :
    Friedrichs.MixedSpatial.EnergySpace α ≃L[ℝ] EnergySpace α :=
  (coordinateLpEquiv α).prodCongr
    ((ContinuousLinearEquiv.piCongrRight (fun _ : Fin d => scaledCoordinateEquiv α)).prodCongr
      (ContinuousLinearEquiv.piCongrRight (fun _ : Fin d => scaledCoordinateEquiv α)))

lemma energyEquiv_core {d : ℕ} {α : MultiIndex d}
    {v : Friedrichs.MixedSpatial.EnergySpace α} (hv : v ∈ Friedrichs.MixedSpatial.core α) :
    energyEquiv α v ∈ core α := by
  obtain ⟨F,hF,hv,hgrad,hpot⟩ := hv
  refine ⟨fun x => F (up x), smoothCore_up hF, ?_, ?_, ?_⟩
  · exact (coordinateLpEquiv_ae α v.1).trans (up_ae hv)
  · intro i
    change (scale • coordinateLpEquiv α (v.2.1 i) : H α) =ᵐ[spatialMeasure α] _
    filter_upwards [Lp.coeFn_smul scale (coordinateLpEquiv α (v.2.1 i)),
      coordinateLpEquiv_ae α (v.2.1 i), up_ae (hgrad i)] with x hs hx hg
    rw [hs]
    simp only [Pi.smul_apply,smul_eq_mul,hx,hg,partial_up hF.1]
  · intro i
    change (scale • coordinateLpEquiv α (v.2.2 i) : H α) =ᵐ[spatialMeasure α] _
    filter_upwards [Lp.coeFn_smul scale (coordinateLpEquiv α (v.2.2 i)),
      coordinateLpEquiv_ae α (v.2.2 i), up_ae (hpot i)] with x hs hx hg
    rw [hs]
    simp only [Pi.smul_apply,smul_eq_mul,hx,hg,potentialFactor,up]
    ring

lemma energyEquiv_symm_core {d : ℕ} {α : MultiIndex d}
    {v : EnergySpace α} (hv : v ∈ core α) :
    (energyEquiv α).symm v ∈ Friedrichs.MixedSpatial.core α := by
  obtain ⟨F,hF,hv,hgrad,hpot⟩ := hv
  refine ⟨fun x => F (down x), smoothCore_down hF, ?_, ?_, ?_⟩
  · exact (coordinateLpEquiv_symm_ae α v.1).trans (down_ae hv)
  · intro i
    change (scale⁻¹ • (coordinateLpEquiv α).symm (v.2.1 i) : Friedrichs.MixedSpatial.H α)
      =ᵐ[Friedrichs.MixedSpatial.spatialMeasure α] _
    filter_upwards [Lp.coeFn_smul scale⁻¹ ((coordinateLpEquiv α).symm (v.2.1 i)),
      coordinateLpEquiv_symm_ae α (v.2.1 i), down_ae (hgrad i)] with x hs hx hg
    rw [hs]
    simp only [Pi.smul_apply,smul_eq_mul,hx,hg,partial_down hF.1]
  · intro i
    change (scale⁻¹ • (coordinateLpEquiv α).symm (v.2.2 i) : Friedrichs.MixedSpatial.H α)
      =ᵐ[Friedrichs.MixedSpatial.spatialMeasure α] _
    filter_upwards [Lp.coeFn_smul scale⁻¹ ((coordinateLpEquiv α).symm (v.2.2 i)),
      coordinateLpEquiv_symm_ae α (v.2.2 i), down_ae (hpot i)] with x hs hx hg
    rw [hs]
    simp only [Pi.smul_apply,smul_eq_mul,hx,hg,potentialFactor,down]
    simp [← mul_assoc,scale_ne]

lemma energyEquiv_core_image {d : ℕ} (α : MultiIndex d) :
    energyEquiv α '' Friedrichs.MixedSpatial.core α = core α := by
  apply Subset.antisymm
  · rintro _ ⟨v,hv,rfl⟩
    exact energyEquiv_core hv
  · intro v hv
    exact ⟨(energyEquiv α).symm v, energyEquiv_symm_core hv, (energyEquiv α).apply_symm_apply v⟩

theorem energyEquiv_closure_image {d : ℕ} (α : MultiIndex d) :
    energyEquiv α '' Friedrichs.MixedSpatial.formClosure α = formClosure α := by
  change (energyEquiv α).toHomeomorph '' closure (Friedrichs.MixedSpatial.core α) = closure (core α)
  rw [(energyEquiv α).toHomeomorph.image_closure]
  exact congrArg closure (energyEquiv_core_image α)

lemma energyEquiv_mem_closure {d : ℕ} (α : MultiIndex d)
    (v : Friedrichs.MixedSpatial.EnergySpace α) :
    energyEquiv α v ∈ formClosure α ↔ v ∈ Friedrichs.MixedSpatial.formClosure α := by
  rw [← energyEquiv_closure_image]
  exact (energyEquiv α).injective.mem_set_image

lemma energyEquiv_pairing {d : ℕ} (α : MultiIndex d)
    (v w : Friedrichs.MixedSpatial.EnergySpace α) :
    scale^d * formPairing (energyEquiv α v) (energyEquiv α w) =
      scale^2 * Friedrichs.MixedSpatial.formPairing v w := by
  unfold formPairing Friedrichs.MixedSpatial.formPairing
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change scale^d * (inner ℝ (scale • coordinateLpEquiv α (v.2.1 i))
    (scale • coordinateLpEquiv α (w.2.1 i)) +
    inner ℝ (scale • coordinateLpEquiv α (v.2.2 i))
    (scale • coordinateLpEquiv α (w.2.2 i))) = _
  simp only [inner_smul_left,inner_smul_right,conj_trivial]
  have h₁ := coordinateLpEquiv_inner α (v.2.1 i) (w.2.1 i)
  have h₂ := coordinateLpEquiv_inner α (v.2.2 i) (w.2.2 i)
  linear_combination scale^2 * h₁ + scale^2 * h₂

#print axioms energyEquiv_closure_image
#print axioms energyEquiv_pairing
end BecknerOnofri.Paper2.Physical
