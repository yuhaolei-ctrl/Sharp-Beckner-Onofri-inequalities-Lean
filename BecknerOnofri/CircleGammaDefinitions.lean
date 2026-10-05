import BecknerOnofri.CircleRateDefinitions
import BecknerOnofri.CircleScalarDefinitions
import BecknerOnofri.CircleWeightDefinitions
import BecknerOnofri.SpinProductDefinitions

/-! The source's h(t), I(t), and γ(t). The inverse is only used after
existence is established on the domain in question. The four-point minimum
is proved equal to the constrained quadratic minimum in CircleScalarCandidates. -/
namespace BecknerOnofri.HighDim.CircleScalar
noncomputable def parameter (t : ℝ) : ℝ := Function.invFun (besselMoment 1) t
noncomputable def rate (t : ℝ) : ℝ :=
  2*parameter t*t-Real.log (bessel 0 (parameter t))
noncomputable def gamma (t : ℝ) : ℝ :=
  (13/40)*rate t+(27/40)*t^2-2*Spin.binaryCost t+
    candidateMinimum (633/2000) ((27/40)*weight 1 t) ((27/40)*weight 2 t)
      (6-t) (6*besselMoment 2 (parameter t)-besselMoment 3 (parameter t))
      (t^2) (besselMoment 2 (parameter t))
end BecknerOnofri.HighDim.CircleScalar
