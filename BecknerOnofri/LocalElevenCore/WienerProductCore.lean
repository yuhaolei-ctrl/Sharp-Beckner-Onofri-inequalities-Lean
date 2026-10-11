module

public import BecknerOnofri.ContinuousFirstShell
public import Legacy.BecknerOnofri.WienerRepresentative

@[expose] public section

/-! Fourier coefficients of a product of two continuous functions with absolutely summable
Fourier coefficients.  These two lemmas (`WeightedCubicExponentialTail.series_eq` and
`WienerAlgebraBounds.coefficient_product`) sit below `LocalEleven.GreenLocalBranch` in the import
graph, so that the Sobolev Banach algebra can be used by the construction of the complement
correction; they were moved here verbatim from `WeightedCubicExponentialTail.lean` and
`WienerAlgebraBounds.lean`, which import this module. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators

namespace BecknerOnofri.HighDim.LocalEleven.WeightedCubicExponentialTail
open ContinuousGibbs ContinuousFirstShell
open Legacy.TorusEndpoint Legacy.BecknerOnofri.WienerFourier

lemma series_eq {d : ℕ} (u : Space d) (hu : Summable (fun k => ‖coefficient k u‖)) :
    absoluteFourierSeries (fun k => coefficient k u) = fun x => (u x : ℂ) := by
  haveI : (Legacy.TorusEndpoint.torusMeasure d).IsOpenPosMeasure := by
    rw [Legacy.TorusEndpoint.torusMeasure_explicit]
    infer_instance
  exact Measure.eq_of_ae_eq
    ((representative_ae_eq (toL2 d u) hu).trans (toL2_ae u))
    (representative_continuous (toL2 d u) hu) (Complex.continuous_ofReal.comp u.continuous)

end BecknerOnofri.HighDim.LocalEleven.WeightedCubicExponentialTail

namespace BecknerOnofri.HighDim.LocalEleven.WienerAlgebraBounds
open ContinuousGibbs ContinuousFirstShell WeightedCubicExponentialTail
open Legacy.TorusEndpoint Legacy.BecknerOnofri.WienerFourier

lemma coefficient_product {d : ℕ} (u v : Space d)
    (hu : Summable (fun k => ‖coefficient k u‖))
    (hv : Summable (fun k => ‖coefficient k v‖)) (k : Frequency d) :
    coefficient k (u*v)=convolution (fun k => coefficient k u) (fun k => coefficient k v) k := by
  have he : absoluteFourierSeries (convolution (fun k => coefficient k u) (fun k => coefficient k v))=
      fun x => (u x:ℂ)*(v x:ℂ) := by
    funext x
    rw [convolution_series _ _ hu hv,series_eq u hu,series_eq v hv]
  rw [← absoluteFourierSeries_coefficient _ (convolution_norm_summable _ _ hu hv),he,
    coefficient_integral]
  simp only [UnitAddTorus.mFourierCoeff,smul_eq_mul,ContinuousMap.mul_apply,Complex.ofReal_mul]
  rfl

end BecknerOnofri.HighDim.LocalEleven.WienerAlgebraBounds
