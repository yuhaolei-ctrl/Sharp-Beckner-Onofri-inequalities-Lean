module

public import BecknerOnofri.CircleRateDefinitions
public import BecknerOnofri.CircleScalarDefinitions
public import BecknerOnofri.CircleWeightDefinitions
public import BecknerOnofri.SpinProductDefinitions

@[expose] public section

/-! The source's h(t), I(t), and γ(t). The inverse is only used after
existence is established on the domain in question. The four-point minimum
is proved equal to the constrained quadratic minimum in CircleScalarCandidates. -/
namespace BecknerOnofri.HighDim.CircleScalar
noncomputable def parameter (t : ℝ) : ℝ := Function.invFun (besselMoment 1) t
noncomputable def rate (t : ℝ) : ℝ :=
  2*parameter t*t-Real.log (bessel 0 (parameter t))
noncomputable def gamma (t : ℝ) : ℝ :=
  (33/100)*rate t+(67/100)*t^2-2*Spin.binaryCost t+
    candidateMinimum (157/500) ((67/100)*weight 1 t) ((67/100)*weight 2 t)
      (6-t) (6*besselMoment 2 (parameter t)-besselMoment 3 (parameter t))
      (t^2) (besselMoment 2 (parameter t))
end BecknerOnofri.HighDim.CircleScalar
