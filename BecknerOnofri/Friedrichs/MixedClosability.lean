import BecknerOnofri.Friedrichs.MixedGradientTesting
import BecknerOnofri.Friedrichs.MixedPotentialClosed
import BecknerOnofri.Friedrichs.MixedFormSubmodule
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff
namespace BecknerOnofri.Friedrichs.MixedSpatial

lemma gradient_zero_of_first_zero {d : ℕ} {α : MultiIndex d} {v : EnergySpace α}
    (hv : v∈formClosure α) (h0 : v.1=0) (i : Fin d) : v.2.1 i=0 := by
  have hint : Integrable (v.2.1 i : Space d → ℝ) (spatialMeasure α) :=
    (Lp.memLp (v.2.1 i)).integrable (by norm_num)
  have ha := (isOpen_openBox α).ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hint.integrableOn.locallyIntegrableOn) (fun ψ hψ hc hs => by
      have hh := closed_gradient_testing hv hψ hs i
      rw [h0,inner_zero_left,neg_zero] at hh
      unfold testVector at hh
      rw [inner_eq_integral_of_ae (Filter.EventuallyEq.rfl)
        (continuous_memLp α hψ.continuous).coeFn_toLp] at hh
      simpa only [smul_eq_mul,mul_comm] using hh)
  apply Lp.ext
  filter_upwards [ha,ae_mem_openBox α,Lp.coeFn_zero ℝ 2 (spatialMeasure α)] with x hx hmem hz
  exact (hx hmem).trans hz.symm

lemma potential_zero_of_first_zero {d : ℕ} {α : MultiIndex d} {v : EnergySpace α}
    (hv : v∈formClosure α) (h0 : v.1=0) (i : Fin d) : v.2.2 i=0 := by
  have hp := closed_potential_relation hv i
  rw [h0] at hp
  apply Lp.ext
  filter_upwards [hp,Lp.coeFn_zero ℝ 2 (spatialMeasure α)] with x hx hz
  rw [hx,hz]
  simp

theorem formClosure_first_injective {d : ℕ} (α : MultiIndex d) :
    Set.InjOn (fun v : EnergySpace α => v.1) (formClosure α) := by
  intro u hu v hv he
  have hc : u-v∈formClosure α := (closedFormSubmodule α).sub_mem hu hv
  have h0 : (u-v).1=0 := by simp only [Prod.fst_sub,he,sub_self]
  have h1 : u.2.1=v.2.1 := by
    funext i
    exact sub_eq_zero.mp (gradient_zero_of_first_zero hc h0 i)
  have hV : u.2.2=v.2.2 := by
    funext i
    exact sub_eq_zero.mp (potential_zero_of_first_zero hc h0 i)
  exact Prod.ext he (Prod.ext h1 hV)

#print axioms formClosure_first_injective
end BecknerOnofri.Friedrichs.MixedSpatial
