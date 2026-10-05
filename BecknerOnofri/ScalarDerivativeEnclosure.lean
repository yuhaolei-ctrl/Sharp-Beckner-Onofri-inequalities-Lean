import BecknerOnofri.ScalarCompositionEnclosure
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace BecknerOnofri.HighDim.ScalarCertificate
open Set Filter
open scoped Topology

theorem FunctionEnclosure.derivative_mem {a b x f' : ℝ} {f : ℝ → ℝ}
    (ef : FunctionEnclosure a b f) (hx : x∈Ioo a b) (hd : HasDerivAt f f' x) :
    ef.slope.Contains f' := by
  have hnear : ∀ᶠ y in 𝓝[≠] x,y∈Ioo a b :=
    nhdsWithin_le_nhds (Ioo_mem_nhds hx.1 hx.2)
  have hneq : ∀ᶠ y in 𝓝[≠] x,y≠x := self_mem_nhdsWithin
  have hb : ∀ᶠ y in 𝓝[≠] x,ef.slope.Contains (_root_.slope f x y) := by
    filter_upwards [hnear,hneq] with y hy hyx
    have h := ef.secant_mem_ne (Ioo_subset_Icc_self hx) (Ioo_subset_Icc_self hy) hyx.symm
    simpa only [_root_.slope,vsub_eq_sub,smul_eq_mul,div_eq_mul_inv,mul_comm] using h
  exact ⟨le_of_tendsto_of_tendsto tendsto_const_nhds hd.tendsto_slope (hb.mono fun _ h => h.1),
    le_of_tendsto_of_tendsto hd.tendsto_slope tendsto_const_nhds (hb.mono fun _ h => h.2)⟩

#print axioms FunctionEnclosure.derivative_mem
end BecknerOnofri.HighDim.ScalarCertificate
