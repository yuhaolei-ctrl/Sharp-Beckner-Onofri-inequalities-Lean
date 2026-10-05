import BecknerOnofri.Friedrichs.MixedFractionalStatementDefinitions
import BecknerOnofri.Friedrichs.FullPeriodicStatementDefinitions
import Legacy.BecknerOnofri.JacobiTensorBasis
import BecknerOnofri.Friedrichs.MixedSpatialDefinitions
import BecknerOnofri.Friedrichs.MixedEigenStatementDefinitions
import BecknerOnofri.Friedrichs.MixedOperatorStatementDefinitions
import BecknerOnofri.Friedrichs.MixedStatementDefinitions
import Legacy.BecknerOnofri.JacobiEigenfunctions
import BecknerOnofri.Friedrichs.SpatialStatementDefinitions
import BecknerOnofri.SmoothEulerStatementDefinitions
import BecknerOnofri.CanonicalSelectionDefinitions
import BecknerOnofri.PrescribedSelectionDefinitions
import BecknerOnofri.ActiveSquaredHessianDefinitions
import BecknerOnofri.SobolevAnalyticGraphDefinitions
import BecknerOnofri.SobolevQuadraticReductionDefinitions
import BecknerOnofri.StableSupportedClassificationDefinitions
import BecknerOnofri.LocalFullModeBranchDefinitions
import BecknerOnofri.SupportedClassificationStatementDefinitions
import BecknerOnofri.SupportedEnergyStatementDefinitions
import BecknerOnofri.SupportedBranchStatementDefinitions
import BecknerOnofri.LocalQuarticStatementDefinitions
import BecknerOnofri.LocalStationaryBranchDefinitions
import BecknerOnofri.CircleRearrangementDefinitions
import BecknerOnofri.CosineShapeDefinitions
import BecknerOnofri.CosineMixtureStatementDefinitions
import BecknerOnofri.ExtendedEntropyDefinitions
import BecknerOnofri.CoordinateMarginalDefinitions
import BecknerOnofri.CurveThresholdDefinitions
import BecknerOnofri.GapDefinitions
import BecknerOnofri.OrderParameterDefinitions
import BecknerOnofri.LowScalarDefinitions
import BecknerOnofri.ClosedCubeTaylorDefinitions
import BecknerOnofri.HeatDefinitions
import BecknerOnofri.ElevenCoordinateDefinitions
import BecknerOnofri.ElevenLabelDefinitions
import Legacy.BecknerOnofri.ThetaDomination
import BecknerOnofri.LowDimensionDefinitions
import BecknerOnofri.ElevenScalarDefinitions
import BecknerOnofri.ElevenDefinitions
import BecknerOnofri.EntropyMixtureDefinitions
import BecknerOnofri.EntropyTailIntegralDefinitions
import BecknerOnofri.ConditionalProfileDefinitions
import BecknerOnofri.SpinPrefixDefinitions
import BecknerOnofri.ConditionalEntropyDefinitions
import BecknerOnofri.CircleDeficitDefinitions
import BecknerOnofri.CircleTorusFlowDefinitions
import BecknerOnofri.CircleFisherDefinitions
import Mathlib.Analysis.Calculus.ContDiff.Basic
import BecknerOnofri.CircleOuterDefinitions
import BecknerOnofri.CirclePoissonDefinitions
import BecknerOnofri.CircleHardyDefinitions
import Mathlib.Analysis.Convex.Function
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import BecknerOnofri.CircleTailDefinitions
import BecknerOnofri.CircleBesselEnclosureDefinitions
import BecknerOnofri.CircleGammaDefinitions
import Mathlib.Analysis.SpecialFunctions.Sqrt
import BecknerOnofri.CircleWeightDefinitions
import BecknerOnofri.CircleBesselDefinitions
import Mathlib.Analysis.Calculus.Deriv.Basic
import BecknerOnofri.CircleScalarDefinitions
import BecknerOnofri.SpinProductGradientDefinitions
import BecknerOnofri.SpinDifferentialDefinitions
import BecknerOnofri.SpinProductDefinitions
import BecknerOnofri.SpinChannelDefinitions
import BecknerOnofri.SpinCountDefinitions
import BecknerOnofri.Definitions
import BecknerOnofri.Constants
import BecknerOnofri.BranchDefinitions
import BecknerOnofri.LatticeDefinitions
import Mathlib.Probability.Moments.Variance

/-!
# Trusted targets from the September 21 full manuscript

Only this trusted challenge may contain proof holes. It imports mathematical
definitions and Mathlib, not Solution or the auxiliary proof files.

The targets include the endpoint, equality cases, thresholds, the full
translation-orbit Morse--Bott classification, the uniform H^s branch profile,
and scalar onset asymptotics, together with low-dimensional, dimension-eleven,
and common analytic assertions. All target proofs live in Solution and its auxiliaries.
The source-coverage audit remains distinct from target build/Comparator validation.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators ContDiff
namespace BecknerOnofri.Target
open HighDim

/-- Equation (1.29), over every finite-entropy Haar probability density.
Using an extended nonnegative sum also asserts the required energy finiteness. -/
theorem density_endpoint (d : ℕ) (hd : 12 ≤ d)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    spectralEnergy ρ ≤ ENNReal.ofReal (2 * entropy ρ) := by
  sorry

/-- Full density equality case in Theorem 1.3, interpreted almost everywhere. -/
theorem density_rigidity (d : ℕ) (hd : 12 ≤ d)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    spectralEnergy ρ = ENNReal.ofReal (2 * entropy ρ) ↔
      ρ.value =ᵐ[torusMeasure d] (fun _ => 1) := by
  sorry

/-- Equation (1.30); exponential integrability is a conclusion, not a hypothesis. -/
theorem potential_endpoint (d : ℕ) (hd : 12 ≤ d)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    Integrable (fun x => Real.exp (centered u x)) (torusMeasure d) ∧
      logPartition u ≤ ((spectralCoefficient d * potentialEnergy u : ℝ) : EReal) := by
  sorry

/-- Full potential equality case in Theorem 1.3. -/
theorem potential_rigidity (d : ℕ) (hd : 12 ≤ d)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    logPartition u = ((spectralCoefficient d * potentialEnergy u : ℝ) : EReal) ↔
      ∃ c : ℝ, u =ᵐ[torusMeasure d] (fun _ => c) := by
  sorry

/-- Equation (1.31), with the endpoint exhibited as the greatest zero-pressure coupling. -/
theorem pressure_threshold (d : ℕ) (hd : 12 ≤ d) :
    IsGreatest {β : ℝ | 0 ≤ β ∧ pressure d β = 0} (spectralThreshold d) := by
  sorry

/-- Equation (1.31), with the endpoint exhibited as the least zero-defect coefficient. -/
theorem coefficient_threshold (d : ℕ) (hd : 12 ≤ d) :
    IsLeast {A : ℝ | 0 < A ∧ coefficientDefect d A = 0} (spectralCoefficient d) := by
  sorry

/-- Positivity explicitly asserted after (1.28); includes odd dimensions. -/
theorem kappa_positive (d : ℕ) (hd : 12 ≤ d) : 0 < kappa d := by
  sorry

/-- Equations (1.32)--(1.34), including existence, classification of every
global minimizer, the full-mode Morse--Bott orbit, and the uniform H^s error. -/
theorem full_branch_onset (d : ℕ) (hd : 12 ≤ d) : FullBranchOnset d := by
  sorry

/-- Equation (1.35): quantified one-sided O bound, with pressure finiteness explicit. -/
theorem pressure_onset (d : ℕ) (hd : 12 ≤ d) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧
      ∀ β : ℝ, spectralThreshold d < β → β < spectralThreshold d + ε →
        ∃ p : ℝ, pressure d β = (p : EReal) ∧
          |p - (d : ℝ) / (2 * kappa d) * (1 - spectralThreshold d / β) ^ 2| ≤
            C * (β - spectralThreshold d) ^ 3 := by
  sorry

/-- Equation (1.36): quantified left-sided O bound on the positive coefficient domain. -/
theorem coefficient_onset (d : ℕ) (hd : 12 ≤ d) :
    ∃ ε C : ℝ, 0 < ε ∧ ε < spectralCoefficient d ∧ 0 ≤ C ∧
      ∀ A : ℝ, spectralCoefficient d - ε < A → A < spectralCoefficient d →
        ∃ c : ℝ, coefficientDefect d A = (c : EReal) ∧
          |c - (d : ℝ) / (2 * kappa d) * (1 - A / spectralCoefficient d) ^ 2| ≤
            C * (1 - A / spectralCoefficient d) ^ 3 := by
  sorry

/-- The entropy rigidity used by the proof, at its actual analytic domain. -/
theorem entropy_zero (d : ℕ) (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    entropy ρ = 0 ↔ ρ.value =ᵐ[torusMeasure d] (fun _ => 1) := by
  sorry

/-- The strict subcritical gap used for minimizer selection in Section 5. -/
theorem spectral_subcriticality (d : ℕ) (hd : 12 ≤ d) :
    spectralThreshold d < 2 * (d : ℝ) := by
  sorry

/-- The uniform competitor attains the proposed endpoint in every dimension. -/
theorem uniform_equality (d : ℕ) :
    (uniformDensity d).FiniteEntropy ∧
      spectralEnergy (uniformDensity d) = ENNReal.ofReal (2 * entropy (uniformDensity d)) := by
  sorry

/-- The actual exponential estimates and parametric exit check in Section 5. -/
theorem local_exit_conditions :
    Real.exp (6 / 49 : ℝ) < 8 / 7 ∧
      Real.exp (187 / 105 : ℝ) < 6 ∧
      0 < 1 - Real.exp (187 / 105 : ℝ) / 64 ∧
      (12 / 64 : ℝ) * Real.exp (6 / 49 : ℝ) /
        (1 - Real.exp (187 / 105 : ℝ) / 64) < 6 / 25 := by
  sorry

/-- The exact norm-conversion arithmetic in `eq:section5-d12-partition-bound`. -/
theorem initial_norm_arithmetic : (24000 : ℕ) ^ 5 < 300000 ^ 4 := by
  sorry

/-- The analytic integrability step, without an assumed rough inequality. -/
theorem critical_exponential_integrability (d : ℕ) (hd : 0 < d)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) (p : ℝ) (hp : 0 < p) :
    Integrable (fun x => Real.exp (p * centered u x)) (torusMeasure d) := by
  sorry

/-- In particular the extended log partition is genuinely finite and nonnegative. -/
theorem log_partition_regular (d : ℕ) (hd : 0 < d)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    0 ≤ logPartition u ∧ logPartition u ≠ ⊤ := by
  sorry

/-- The combinatorial large-support tail estimate in the rectangle proof. -/
theorem three_symbol_count (d : ℕ) :
    (∑ j ∈ (Finset.range (d + 1)).filter (fun j => 2 * d < 3 * j),
      (2 : ℝ) ^ j * (d.choose j : ℝ)) ≤ (2 / 3 : ℝ) * 3 ^ d := by
  sorry

/-- The logarithmic Bessel-series estimate used in the local exclusion step. -/
theorem bessel_series_quartic (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1 / 5) :
    Real.log (∑' n : ℕ, t ^ (2 * n) / (n.factorial : ℝ) ^ 2) ≤
      t ^ 2 - (6 / 25 : ℝ) * t ^ 4 := by
  sorry

/-- The actual centered exponential estimate, including its variance term. -/
theorem centered_exponential_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (w : Ω → ℝ) (B : ℝ)
    (hw : AEStronglyMeasurable w μ) (hB : 0 ≤ B)
    (hbound : ∀ᵐ x ∂μ, |w x| ≤ B) :
    Real.log (∫ x, Real.exp (w x) ∂μ) ≤
      (∫ x, w x ∂μ) + (Real.exp (2 * B) / 2) * ProbabilityTheory.variance w μ := by
  sorry

/-- Actual subcritical attainment used in the high-dimensional selection argument. -/
theorem subcritical_dual_attainment (d : ℕ) (hd : 0 < d)
    (β : ℝ) (hβ : 0 < β) (hβd : β < 2 * (d : ℝ)) :
    ∃ u : Torus d → ℝ, InCriticalSobolev u ∧ MeanZero u ∧
      0 ≤ dualFunctional β u ∧
      ∀ v : Torus d → ℝ, InCriticalSobolev v → dualFunctional β v ≤ dualFunctional β u := by
  sorry

/-- The local quartic estimate for the actual normalized circle Haar integral. -/
theorem circle_partition_quartic (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1 / 5) :
    Real.log (∫ x : UnitAddCircle, Real.exp (2 * t * (fourier 1 x).re)
      ∂AddCircle.haarAddCircle) ≤ t ^ 2 - (6 / 25 : ℝ) * t ^ 4 := by
  sorry

/-- The exact real-exponent spectral slice lemma, including its rational margin. -/
theorem spectral_slice (p a : ℝ) (hp : 12 ≤ p) (ha : Real.sqrt 2 ≤ a) :
    a ^ (p - 1) * (∑' n : ℤ, (a ^ 2 + (n : ℝ) ^ 2) ^ (-p / 2)) ≤
      (311141 / 342144 : ℝ) := by
  sorry

/-- The full rectangular lattice comparison, with arbitrary nonnegative radii. -/
theorem rectangular_lattice (d : ℕ) (hd : 12 ≤ d) (R : Fin d → ℕ) :
    RectangleLattice.latticeSum (d : ℝ) R ≤
      (1 / ((d : ℝ) - 1)) * ∑ i : Fin d,
        RectangleLattice.latticeSum ((d : ℝ) - 1) (Function.update R i 0) := by
  sorry

/-- First-shell obstruction proves sharpness on the full potential domain. -/
theorem coefficient_sharpness (d : ℕ) (hd : 0 < d) (A : ℝ)
    (hA : A < spectralCoefficient d) : 0 < coefficientDefect d A := by
  sorry

/-- Full finite-entropy domain has finite spectral energy, without assuming L2. -/
theorem finite_entropy_energy (d : ℕ) (hd : 0 < d)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) : spectralEnergy ρ ≠ ⊤ := by
  sorry

/-- Exact Gibbs duality on the full domains. -/
theorem pressure_duality (d : ℕ) (hd : 0 < d) (β : ℝ) (hβ : 0 < β) :
    pressure d β = coefficientDefect d
      (spectralThreshold d / (2 * β * (2 * Real.pi) ^ d)) := by
  sorry

/-- Pressure is finite throughout the nonnegative subcritical interval. -/
theorem subcritical_pressure_finite (d : ℕ) (hd : 0 < d) (β : ℝ)
    (hβ : 0 ≤ β) (hβd : β < 2 * (d : ℝ)) :
    pressure d β ≠ ⊥ ∧ pressure d β ≠ ⊤ := by
  sorry

/-- Actual first-shell Gibbs competitors make pressure positive above the threshold. -/
theorem pressure_sharpness (d : ℕ) (hd : 0 < d) (β : ℝ)
    (hβ : spectralThreshold d < β) : 0 < pressure d β := by
  sorry

/-- Shearer for the actual coordinate-deletion Haar marginals. -/
theorem entropy_shearer (d : ℕ) (ρ : ProbabilityDensity d)
    (hρ : Continuous ρ.value) (hpos : ∀ x, 0 < ρ.value x) :
    (∑ i : Fin d, ∫ x,
      (∫ y : UnitAddCircle, ρ.value (Function.update x i y) ∂AddCircle.haarAddCircle) *
      Real.log (∫ y : UnitAddCircle, ρ.value (Function.update x i y) ∂AddCircle.haarAddCircle)
        ∂torusMeasure d) ≤ ((d : ℝ) - 1) * entropy ρ := by
  sorry

/-- Exact first-shell cubic moment and quartic cumulant. -/
theorem first_shell_moments (d : ℕ) (t : Fin d → ℝ) :
    let v : Torus d → ℝ := fun x => ∑ i, 2 * t i * (fourier 1 (x i)).re
    (∫ x, v x ^ 3 ∂torusMeasure d) = 0 ∧
      (1/24:ℝ) * (∫ x, v x ^ 4 ∂torusMeasure d) -
        (1/8:ℝ) * (∫ x, v x ^ 2 ∂torusMeasure d) ^ 2 =
          -(1/4:ℝ) * ∑ i, t i ^ 4 := by
  sorry


/-! Additional exact targets from the authoritative 2026-09-21 §5.2 proof. -/

theorem spin_vertex_bound :
    ∀ i j k : Spin.Count, 1 ≤ i.val → i < j → j < k →
    Spin.quadraticQ (Spin.vertexQ i j k) ≤
      (3187261891510618067287:ℚ)/3722907769367296702500 := by
  sorry

theorem spin_vertex_maximizer :
    Spin.quadraticQ (Spin.vertexQ 1 9 12) =
    (3187261891510618067287:ℚ)/3722907769367296702500 := by
  sorry

theorem spin_correcting_bounds :
    Spin.quadraticQ Spin.correctionVQ < 4 ∧ Spin.quadraticQ Spin.correctionZQ < 16 := by
  sorry

theorem spin_matrix_positive :
    ∀ q : Spin.Count → ℝ, 0 ≤ Spin.quadratic q := by
  sorry

theorem spin_small_mean_arithmetic :
    5*Spin.smallMeanQ^2*Spin.oscillationConstantQ < 191/1000 ∧
    (1/50:ℚ) ≤ Spin.smallMarginQ := by
  sorry

theorem spin_exchangeable_entropy :
    ∀ ν : Spin.Configuration → ℝ, Spin.Exchangeable ν →
    (∑ σ : Spin.Configuration,ν σ*Real.log (ν σ/(1/4096))) =
      Spin.relativeEntropy (Spin.countLaw ν) Spin.reference := by
  sorry


theorem spin_channel_probability :
    ∀ ρ : ProbabilityDensity 12,
    (∀ σ : Spin.Configuration,0 ≤ Spin.channelLaw ρ σ) ∧
      (∑ σ : Spin.Configuration,Spin.channelLaw ρ σ)=1 := by
  sorry

theorem spin_channel_joint_moment :
    ∀ (ρ : ProbabilityDensity 12) (S : Finset (Fin 12)),
    (∑ σ : Spin.Configuration,Spin.channelLaw ρ σ*Spin.jointSpin S σ)=
      ∫ x,ρ.value x*(∏ i ∈ S,(fourier 1 (x i)).re) ∂torusMeasure 12 := by
  sorry

theorem spin_exchangeable_energy :
    ∀ ν : Spin.Configuration → ℝ, Spin.Exchangeable ν →
    (∑ s : Spin.Order,Spin.weight s*
      (∑ σ : Spin.Configuration,ν σ*Spin.jointSpin (Spin.firstCoordinates s) σ)^2)=
      Spin.quadratic (Spin.countLaw ν) := by
  sorry


/-- Lemma 5.18, fixed-mean curvature on the entire feasible domain. -/
theorem spin_fixed_mean_curvature (p q : Spin.Count → ℝ)
    (hp : Spin.Feasible p) (hpos : ∀ j, 0 < p j)
    (hmass : (∑ j : Spin.Count,q j)=0) (hmean : Spin.mean q=0) :
    Spin.quadratic q ≤ (9/10)*(∑ j : Spin.Count,q j^2/p j) := by
  sorry

/-- Lemma 5.18, arbitrary-mean curvature on the entire feasible domain. -/
theorem spin_all_mean_curvature (p q : Spin.Count → ℝ)
    (hp : Spin.Feasible p) (hpos : ∀ j, 0 < p j)
    (hmass : (∑ j : Spin.Count,q j)=0) :
    Spin.quadratic q ≤ (19/20)*(∑ j : Spin.Count,q j^2/p j)+350*(Spin.mean q)^2 := by
  sorry


/-! Further completed steps from the new entropy route. -/

theorem spin_supporting_parabola (p q : Spin.Count → ℝ) (s t δ ell η : ℝ)
    (hp : Spin.FeasibleAt s p) (hpos : ∀ j,0<p j) (hq : Spin.FeasibleAt t q)
    (hδ : ∀ j,|Spin.gradient p j-ell-η*Spin.meanCoordinate j|≤δ) :
    Spin.functional p+η*(t-s)-350*(t-s)^2-5*δ^2≤Spin.functional q := by
  sorry

theorem spin_fixed_mean_entropy_convexity (p q : Spin.Count → ℝ)
    (hp : Spin.Feasible p) (hpos : ∀ j,0<p j) (hq : Spin.Feasible q)
    (hmean : Spin.mean p=Spin.mean q) :
    Spin.functional p+(∑ j : Spin.Count,Spin.gradient p j*(q j-p j))+
      Spin.relativeEntropy q p/5≤Spin.functional q := by
  sorry

theorem spin_finite_gibbs (p q H : Spin.Count → ℝ)
    (hp : ∀ j,0<p j) (hq : ∀ j,0≤q j) (hmass : (∑ j : Spin.Count,q j)=1) :
    (∑ j : Spin.Count,q j*H j)-Spin.relativeEntropy q p≤
      Real.log (∑ j : Spin.Count,p j*Real.exp (H j)) := by
  sorry

theorem spin_centered_log_mgf (p H : Spin.Count → ℝ) (B : ℝ)
    (hp : ∀ j,0<p j) (hmass : (∑ j : Spin.Count,p j)=1)
    (hcenter : (∑ j : Spin.Count,p j*H j)=0)
    (hB : 0≤B) (hsmall : 5*B<1) (hbound : ∀ j,|H j|≤B) :
    (1/5)*Real.log (∑ j : Spin.Count,p j*Real.exp (5*H j))≤
      ((5/2)/(1-5*B))*(∑ j : Spin.Count,p j*(H j)^2) := by
  sorry

theorem spin_binary_cost_quartic (t : ℝ) (ht : 0≤t) (ht1 : t≤1) :
    t^2/2+t^4/12≤Spin.binaryCost t := by
  sorry

theorem spin_product_feasible (t : ℝ) (ht : 0≤t) (ht1 : t≤1) :
    Spin.FeasibleAt t (Spin.productProbability t) := by
  sorry

theorem spin_product_entropy_energy (t : ℝ) (ht : 0≤t) (ht1 : t<1) :
    Spin.relativeEntropy (Spin.productProbability t) Spin.reference=12*Spin.binaryCost t ∧
      Spin.quadratic (Spin.productProbability t)=∑ s : Spin.Order,Spin.weight s*t^(2*(s.val+1)) := by
  sorry

theorem spin_product_quartic_baseline (t : ℝ) (ht : 0≤t) (ht1 : t≤1/16) :
    (2-(∑ s : Spin.Order,if 2≤s.val+1 then Spin.weight s*(1/16)^(2*(s.val+1)-4) else 0))*t^4≤
      Spin.functional (Spin.productProbability t) := by
  sorry

theorem spin_small_mean (t : ℝ) (q : Spin.Count → ℝ)
    (ht : 0≤t) (ht1 : t≤1/16) (hq : Spin.FeasibleAt t q) :
    t^4/50≤Spin.functional q+12*((3/40)*t^4) := by
  sorry

theorem spin_product_gradient_bounds (t : ℝ) (ht : 0≤t) (ht1 : t≤1/16) :
    (∀ i j : Spin.Count, |Spin.productGradientCorrection t i-Spin.productGradientCorrection t j|≤
      (Spin.oscillationConstantQ:ℝ)*t^2) ∧
    (∑ j : Spin.Count, Spin.productProbability t j*(Spin.productGradientCorrection t j)^2)≤
      (Spin.varianceConstantQ:ℝ)*t^4 := by
  sorry

theorem spin_large_mean_ingredients (a t : ℝ) (q : Spin.Count → ℝ)
    (ha : 0≤a) (ha1 : a<1) (hat : a≤t) (hq : Spin.FeasibleAt t q) :
    12*Spin.binaryCost a≤Spin.relativeEntropy q Spin.reference ∧
      Spin.quadratic q≤∑ s : Spin.Order,Spin.weight s := by
  sorry

theorem spin_interval_certificate (p q : Spin.Count → ℝ) (a b s t δ ell η α β κ : ℝ)
    (hp : Spin.FeasibleAt s p) (hpos : ∀ j,0<p j) (hq : Spin.FeasibleAt t q)
    (hδ : ∀ j,|Spin.gradient p j-ell-η*Spin.meanCoordinate j|≤δ)
    (ha0 : 0≤a) (ha : a≤t) (hb : t≤b) (hκ : 0≤κ)
    (hleft : κ*b^4≤Spin.functional p+η*(a-s)-350*(a-s)^2-5*δ^2+12*(α*a+β))
    (hright : κ*b^4≤Spin.functional p+η*(b-s)-350*(b-s)^2-5*δ^2+12*(α*b+β)) :
    κ*t^4≤Spin.functional q+12*(α*t+β) := by
  sorry

theorem spin_binary_cost_upper (a : ℝ) (ha : 0≤a) (ha1 : a<1) :
    2*Spin.binaryCost a≤a^2+a^4/(6*(1-a^2)) := by
  sorry

theorem circle_scalar_minimum (A B C D L r m : ℝ)
    (hA : 0<A) (hB : 0≤B) (hC : 0≤C) (hD : 0<D) :
    (∀ x : ℝ, m≤x → CircleScalar.candidateMinimum A B C D L r m≤CircleScalar.cost A B C D L r x) ∧
    (∃ x : ℝ, m≤x ∧ CircleScalar.cost A B C D L r x=CircleScalar.candidateMinimum A B C D L r m) := by
  sorry

theorem circle_small_mean_algebra (t I B C D L m : ℝ)
    (ht : 0≤t) (ht1 : t≤1/16) (hI : t^2+t^4/4≤I)
    (hB : (27/80:ℝ)≤B) (hC : 0≤C) :
    (3/40:ℝ)*t^4≤(13/40)*I+(27/40)*t^2-2*Spin.binaryCost t+
      CircleScalar.candidateMinimum (633/2000) B C D L (t^2) m := by
  sorry

theorem circle_weight_enclosure (n N : ℕ) (t : ℝ) (ht : 0≤t) (ht1 : t<1) :
    (∑ j ∈ Finset.range N,t^(2*j)/(n+j+1:ℝ))≤CircleScalar.weight n t ∧
    CircleScalar.weight n t≤(∑ j ∈ Finset.range N,t^(2*j)/(n+j+1:ℝ))+
      t^(2*N)/((n+N+1:ℝ)*(1-t^2)) := by
  sorry

theorem circle_small_mean_weighted (t I m₂ m₃ : ℝ)
    (ht : 0≤t) (ht1 : t≤1/16) (hI : t^2+t^4/4≤I) :
    (3/40:ℝ)*t^4≤(13/40)*I+(27/40)*t^2-2*Spin.binaryCost t+
      CircleScalar.candidateMinimum (633/2000) ((27/40)*CircleScalar.weight 1 t)
        ((27/40)*CircleScalar.weight 2 t) (6-t) (6*m₂-m₃) (t^2) m₂ := by
  sorry

theorem circle_bessel_derivative (n : ℕ) (hn : 1≤n) (h : ℝ) :
    HasDerivAt (CircleScalar.besselMoment n)
      (CircleScalar.besselMoment (n-1) h+CircleScalar.besselMoment (n+1) h-
        2*CircleScalar.besselMoment n h*CircleScalar.besselMoment 1 h) h := by
  sorry

theorem circle_bessel_monotonicity :
    (∀ n : ℕ, MonotoneOn (CircleScalar.besselMoment n) (Set.Ici 0)) ∧
      StrictMono (CircleScalar.besselMoment 1) := by
  sorry

theorem circle_bessel_riccati (h : ℝ) (hh : h≠0) :
    deriv (CircleScalar.besselMoment 1) h+CircleScalar.besselMoment 1 h/h+
      2*(CircleScalar.besselMoment 1 h)^2=2 := by
  sorry

theorem circle_bessel_supersolution (h : ℝ) (hh : 0≤h) :
    CircleScalar.besselMoment 1 h≤h/Real.sqrt (1+h^2) := by
  sorry

theorem circle_parameter_bounds (t : ℝ) (ht : 0≤t) (ht1 : t<1) :
    CircleScalar.besselMoment 1 (CircleScalar.parameter t)=t ∧
      0≤CircleScalar.parameter t ∧ t/(2*(1-t^2))≤CircleScalar.parameter t := by
  sorry

theorem circle_rate_quartic (t : ℝ) (ht : 0≤t) (ht1 : t<1) :
    t^2+t^4/4≤CircleScalar.rate t := by
  sorry

theorem circle_gamma_minimum (t : ℝ) (ht : 0≤t) (ht1 : t<1) :
    IsLeast ((fun a : ℝ => (13/40)*CircleScalar.rate t+(27/40)*t^2-2*Spin.binaryCost t+
      CircleScalar.cost (633/2000) ((27/40)*CircleScalar.weight 1 t) ((27/40)*CircleScalar.weight 2 t)
        (6-t) (6*CircleScalar.besselMoment 2 (CircleScalar.parameter t)-
          CircleScalar.besselMoment 3 (CircleScalar.parameter t)) (t^2) a) ''
      Set.Ici (CircleScalar.besselMoment 2 (CircleScalar.parameter t))) (CircleScalar.gamma t) := by
  sorry

theorem circle_gamma_small (t : ℝ) (ht : 0≤t) (ht1 : t≤1/16) :
    (3/40:ℝ)*t^4≤CircleScalar.gamma t := by
  sorry

theorem spin_mixture_feasible (ρ : ProbabilityDensity 12)
    (w : ℕ → ℝ) (N : ℕ → Fin 12 → ℕ) (hw : ∀ n,0≤w n) (hm : HasSum w 1)
    (hSup : Summable (fun n => w n*∏ i : Fin 12,
      (4:ℝ)^(N n i)/((2*N n i).choose (N n i):ℝ)))
    (hρ : ∀ x,ρ.value x=∑' n,w n*∏ i : Fin 12,
      Complex.normSq (1+fourier 1 (x i))^(N n i)/((2*N n i).choose (N n i):ℝ)) :
    Spin.Feasible (Spin.countLaw (Spin.channelLaw ρ)) := by
  sorry

theorem spin_channel_symmetry (ρ : ProbabilityDensity 12)
    (hρ : ∀ (π : Equiv.Perm (Fin 12)) (x : Torus 12),
      ρ.value (fun i => x (π.symm i))=ρ.value x) : Spin.Exchangeable (Spin.channelLaw ρ) := by
  sorry

theorem spin_channel_mean (ρ : ProbabilityDensity 12)
    (hρ : Spin.Exchangeable (Spin.channelLaw ρ)) :
    Spin.mean (Spin.countLaw (Spin.channelLaw ρ))=
      ∫ x,ρ.value x*(fourier 1 (x (0:Fin 12))).re ∂torusMeasure 12 := by
  sorry

theorem spin_small_mean_gamma (t : ℝ) (q : Spin.Count → ℝ)
    (ht : 0≤t) (ht1 : t≤1/16) (hq : Spin.FeasibleAt t q) :
    t^4/50≤Spin.functional q+12*CircleScalar.gamma t := by
  sorry

theorem circle_gamma_final_range :
    MonotoneOn CircleScalar.tailBase (Set.Ico (999/1000) 1) ∧
    ∀ t : ℝ,(999/1000:ℝ)≤t → t<1 → CircleScalar.tailBase (999/1000)≤CircleScalar.gamma t := by
  sorry

theorem circle_bessel_enclosure (n N : ℕ) (h q : ℝ) (hh : 0≤h) (hq : 0≤q)
    (hq1 : q<1) (hbound : h^2≤q*(N+1:ℝ)*(N+n+1:ℝ)) :
    CircleScalar.besselPartial n N h≤CircleScalar.bessel n h ∧
      CircleScalar.bessel n h≤CircleScalar.besselPartial n N h+CircleScalar.besselTerm n h N/(1-q) := by
  sorry

theorem circle_bessel_ratio_enclosure (n N : ℕ) (h q : ℝ) (hh : 0≤h)
    (hN : 1≤N) (hq : 0≤q) (hq1 : q<1) (hbound : h^2≤q*(N+1:ℝ)^2) :
    CircleScalar.besselPartial n N h/
      (CircleScalar.besselPartial 0 N h+CircleScalar.besselTerm 0 h N/(1-q))≤CircleScalar.besselMoment n h ∧
    CircleScalar.besselMoment n h≤
      (CircleScalar.besselPartial n N h+CircleScalar.besselTerm n h N/(1-q))/CircleScalar.besselPartial 0 N h := by
  sorry

theorem circle_parameter_bracket (t l u : ℝ) (ht : 0≤t) (ht1 : t<1)
    (hl : CircleScalar.besselMoment 1 l≤t) (hu : t≤CircleScalar.besselMoment 1 u) :
    l≤CircleScalar.parameter t ∧ CircleScalar.parameter t≤u := by
  sorry

theorem circle_weight_closed_form (n : ℕ) (t : ℝ) (ht : 0<t) (ht1 : t<1) :
    CircleScalar.weight n t=
      (-Real.log (1-t^2)-∑ j ∈ Finset.range n,t^(2*(j+1))/(j+1:ℝ))/t^(2*n+2) := by
  sorry

theorem circle_logconvex_comparison (F : ℝ → ℝ) (t : ℝ)
    (hcF : ContinuousOn F (Set.Icc (-1:ℝ) 1)) (hF : ConvexOn ℝ (Set.Icc (-1:ℝ) 1) F)
    (hinc : MonotoneOn F (Set.Icc (-1:ℝ) 1))
    (hmass : (∫ x : UnitAddCircle,Real.exp (F ((fourier 1 x).re)) ∂AddCircle.haarAddCircle)=1)
    (hm : (∫ x : UnitAddCircle,Real.exp (F ((fourier 1 x).re))*(fourier 1 x).re
      ∂AddCircle.haarAddCircle)=t) :
    0≤t ∧ t<1 ∧
    CircleScalar.besselMoment 2 (CircleScalar.parameter t)≤
      (∫ x : UnitAddCircle,Real.exp (F ((fourier 1 x).re))*(fourier 2 x).re ∂AddCircle.haarAddCircle) ∧
    |(∫ x : UnitAddCircle,Real.exp (F ((fourier 1 x).re))*(fourier 3 x).re ∂AddCircle.haarAddCircle)-
      CircleScalar.besselMoment 3 (CircleScalar.parameter t)|≤
      6*((∫ x : UnitAddCircle,Real.exp (F ((fourier 1 x).re))*(fourier 2 x).re ∂AddCircle.haarAddCircle)-
        CircleScalar.besselMoment 2 (CircleScalar.parameter t)) ∧
    CircleScalar.rate t≤∫ x : UnitAddCircle,Real.exp (F ((fourier 1 x).re))*
      Real.log (Real.exp (F ((fourier 1 x).re))) ∂AddCircle.haarAddCircle := by
  sorry

theorem circle_entropy_rate_lower (p : UnitAddCircle → ℝ) (t : ℝ)
    (hp : ∀ᵐ x ∂AddCircle.haarAddCircle,0≤p x)
    (hmass : (∫ x,p x ∂AddCircle.haarAddCircle)=1)
    (hi : Integrable p AddCircle.haarAddCircle)
    (hent : Integrable (fun x => p x*Real.log (p x)) AddCircle.haarAddCircle)
    (hm : (∫ x,p x*(fourier 1 x).re ∂AddCircle.haarAddCircle)=t) :
    CircleScalar.rate t≤∫ x,p x*Real.log (p x) ∂AddCircle.haarAddCircle := by
  sorry

theorem circle_weight_integral (n : ℕ) (t : ℝ) (ht : 0≤t) (ht1 : t<1) :
    CircleScalar.weight n t=∫ s in (0:ℝ)..1,s^n/(1-t^2*s) := by
  sorry

theorem circle_gamma_entropy_reduction (t a b E T : ℝ) (ht : 0≤t) (ht1 : t<1)
    (hI : CircleScalar.rate t≤E)
    (hrem : t^2+a^2/2+T+CircleScalar.weight 1 t*(a-t^2)^2+CircleScalar.weight 2 t*(b-t*a)^2≤E)
    (ha : CircleScalar.besselMoment 2 (CircleScalar.parameter t)≤a)
    (hb : |b-CircleScalar.besselMoment 3 (CircleScalar.parameter t)|≤6*(a-CircleScalar.besselMoment 2 (CircleScalar.parameter t))) :
    2*Spin.binaryCost t+CircleScalar.gamma t+(21/1000)*a^2+(27/40)*T≤E := by
  sorry

theorem circle_hardy_fisher_bound (f : CircleHardy.Space) (hf : ‖f‖=1)
    (hE : Summable (fun m : ℕ => (m:ℝ)*(f m)^2)) :
    2/(1-(CircleHardy.moment f 1)^2)*
      (∑' n,(CircleHardy.moment f (n+2)-CircleHardy.moment f 1*CircleHardy.moment f (n+1))^2) ≤
    2*((∑' m : ℕ,(m:ℝ)*(f m)^2)-(∑' n,(CircleHardy.moment f (n+1))^2)) := by
  sorry

theorem circle_poisson_kernel (q : ℝ) (hq : 0≤q) (hq1 : q<1) :
    (∀ x : UnitAddCircle,0<CirclePoisson.kernel q x) ∧
    (∫ x : UnitAddCircle,CirclePoisson.kernel q x ∂AddCircle.haarAddCircle)=1 ∧
    ∀ x : UnitAddCircle,CirclePoisson.kernel q x=
      2*(∑' n : ℕ,q^n*(fourier (n:ℤ) x).re)-1 := by
  sorry

theorem circle_poisson_bounds (q : ℝ) (hq : 0≤q) (hq1 : q<1)
    (p : UnitAddCircle → ℝ) (hp : Continuous p) (a b : ℝ)
    (hlo : ∀ x,a≤p x) (hhi : ∀ x,p x≤b) (x : UnitAddCircle) :
    a≤CirclePoisson.smoothing q p x ∧ CirclePoisson.smoothing q p x≤b := by
  sorry

theorem circle_poisson_deviation (q : ℝ) (hq : 0≤q) (hq1 : q≤1/2)
    (p : UnitAddCircle → ℝ) (hp : Continuous p) (hn : ∀ x,0≤p x)
    (hm : (∫ x,p x ∂AddCircle.haarAddCircle)=1) (x : UnitAddCircle) :
    |CirclePoisson.smoothing q p x-1|≤12*q := by
  sorry

theorem circle_poisson_weight_integral (n : ℕ) (t : ℝ) (ht : 0≤t) (ht1 : t<1) :
    CircleScalar.weight n t=∫ s in Set.Ioi (0:ℝ),
      2*Real.exp (-2*(n+1:ℝ)*s)/(1-t^2*Real.exp (-2*s)) := by
  sorry

theorem circle_outer_factorization (p : Torus 1 → ℝ)
    (hp : Continuous p) (hpos : ∀ x,0<p x) (he : ∀ x,p (-x)=p x)
    (hm : (∫ x,p x ∂torusMeasure 1)=1)
    (hlog : Summable (fun k => CircleOuter.linearWeight k*
      ‖UnitAddTorus.mFourierCoeff (fun x => (Real.log (p x):ℂ)) k‖)) :
    ∃ f : C(Torus 1,ℂ), ∃ u : CircleHardy.Space,
      (∀ x,Complex.normSq (f x)=p x) ∧ ‖u‖=1 ∧
      Summable (fun n : ℕ => (n:ℝ)*(u n)^2) ∧
      Summable (fun k => ‖UnitAddTorus.mFourierCoeff f k‖) ∧
      (∀ n : ℕ,(u n:ℂ)=UnitAddTorus.mFourierCoeff f (fun _ => (n:ℤ))) ∧
      (∀ k,k (0:Fin 1)<0 → UnitAddTorus.mFourierCoeff f k=0) ∧
      ∀ n : ℕ,CircleHardy.moment u n=
        (UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) (fun _ => (n:ℤ))).re := by
  sorry

theorem circle_outer_autocorrelation (f : C(Torus 1,ℂ)) (u : CircleHardy.Space)
    (hc : ∀ m : ℕ,(u m:ℂ)=UnitAddTorus.mFourierCoeff f (fun _ => (m:ℤ)))
    (hn : ∀ k,k (0:Fin 1)<0 → UnitAddTorus.mFourierCoeff f k=0) (n : ℕ) :
    CircleHardy.moment u n=
      (UnitAddTorus.mFourierCoeff (fun x => (Complex.normSq (f x):ℂ)) (fun _ => (n:ℤ))).re := by
  sorry

theorem circle_smooth_outer_factorization (p : Torus 1 → ℝ)
    (hp : Continuous p) (hpos : ∀ x,0<p x) (he : ∀ x,p (-x)=p x)
    (hm : (∫ x,p x ∂torusMeasure 1)=1)
    (hsmooth : ContDiff ℝ 3 (fun x : ℝ => p (fun _ => (x:UnitAddCircle)))) :
    ∃ f : C(Torus 1,ℂ), ∃ u : CircleHardy.Space,
      (∀ x,Complex.normSq (f x)=p x) ∧ ‖u‖=1 ∧
      Summable (fun n : ℕ => (n:ℝ)*(u n)^2) ∧
      Summable (fun k => ‖UnitAddTorus.mFourierCoeff f k‖) ∧
      (∀ n : ℕ,(u n:ℂ)=UnitAddTorus.mFourierCoeff f (fun _ => (n:ℤ))) ∧
      (∀ k,k (0:Fin 1)<0 → UnitAddTorus.mFourierCoeff f k=0) ∧
      ∀ n : ℕ,CircleHardy.moment u n=
        (UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) (fun _ => (n:ℤ))).re := by
  sorry

theorem circle_smooth_fourier_summability (f : Torus 1 → ℂ)
    (hf : ContDiff ℝ 3 (fun x : ℝ => f (fun _ => (x:UnitAddCircle)))) :
    Summable (fun k => CircleOuter.linearWeight k*‖UnitAddTorus.mFourierCoeff f k‖) := by
  sorry

theorem circle_density_hardy_bound (p : Torus 1 → ℝ)
    (hp : Continuous p) (hpos : ∀ x,0<p x) (he : ∀ x,p (-x)=p x)
    (hm : (∫ x,p x ∂torusMeasure 1)=1)
    (hsmooth : ContDiff ℝ 3 (fun x : ℝ => p (fun _ => (x:UnitAddCircle)))) :
    let r : ℕ → ℝ := fun n =>
      (UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) (fun _ => (n:ℤ))).re
    ∃ u : CircleHardy.Space, ‖u‖=1 ∧
      Summable (fun n : ℕ => (n:ℝ)*(u n)^2) ∧
      (∀ n : ℕ,CircleHardy.moment u n=r n) ∧
      (r 1)^2<1 ∧
      2/(1-(r 1)^2)*(∑' n : ℕ,(r (n+2)-r 1*r (n+1))^2) ≤
        2*(∑' m : ℕ,(m:ℝ)*(u m)^2)-((∫ x,(p x)^2 ∂torusMeasure 1)-1) := by
  sorry

theorem circle_poisson_multiplier (q : ℝ) (hq : 0≤q) (hq1 : q<1)
    (p : UnitAddCircle → ℝ) (hp : Continuous p) (n : ℤ) :
    _root_.fourierCoeff (fun x => (CirclePoisson.smoothing q p x:ℂ)) n=
      ((q^n.natAbs:ℝ):ℂ)*_root_.fourierCoeff (fun x => (p x:ℂ)) n := by
  sorry

theorem circle_poisson_flow (s : ℝ) (hs : 0<s) (p : UnitAddCircle → ℝ) (hp : Continuous p) :
    Continuous (CirclePoisson.smoothing (Real.exp (-s)) p) ∧
    (∫ x,CirclePoisson.smoothing (Real.exp (-s)) p x ∂AddCircle.haarAddCircle)=
      (∫ x,p x ∂AddCircle.haarAddCircle) ∧
    ∀ n : ℤ,_root_.fourierCoeff (fun x => (CirclePoisson.smoothing (Real.exp (-s)) p x:ℂ)) n=
      (Real.exp (-((n.natAbs:ℝ)*s)):ℂ)*_root_.fourierCoeff (fun x => (p x:ℂ)) n := by
  sorry

theorem circle_fisher_representation (p : Torus 1 → ℝ)
    (hp : Continuous p) (hpos : ∀ x,0<p x) (he : ∀ x,p (-x)=p x)
    (hm : (∫ x,p x ∂torusMeasure 1)=1)
    (hsmooth : ContDiff ℝ 3 (fun x : ℝ => p (fun _ => (x:UnitAddCircle)))) :
    ∃ u : CircleHardy.Space, ‖u‖=1 ∧
      Summable (fun n : ℕ => (n:ℝ)*(u n)^2) ∧
      (∀ n : ℕ,CircleHardy.moment u n=
        (UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) (fun _ => (n:ℤ))).re) ∧
      (∫ x,p x*CircleFisher.lambda (fun y => Real.log (p y)) x ∂torusMeasure 1)=
        2*∑' n : ℕ,(n:ℝ)*(u n)^2 := by
  sorry

theorem circle_fisher_dissipation (p : Torus 1 → ℝ)
    (hp : Continuous p) (hpos : ∀ x,0<p x) (he : ∀ x,p (-x)=p x)
    (hm : (∫ x,p x ∂torusMeasure 1)=1)
    (hsmooth : ContDiff ℝ 3 (fun x : ℝ => p (fun _ => (x:UnitAddCircle)))) :
    let r : ℕ → ℝ := fun n =>
      (UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) (fun _ => (n:ℤ))).re
    (r 1)^2<1 ∧
      2/(1-(r 1)^2)*(∑' n : ℕ,(r (n+2)-r 1*r (n+1))^2) ≤
        (∫ x,p x*CircleFisher.lambda (fun y => Real.log (p y)) x ∂torusMeasure 1)-
          ((∫ x,(p x)^2 ∂torusMeasure 1)-1) := by
  sorry

theorem circle_lambda_self_adjoint (p g : Torus 1 → ℝ) (hp : Continuous p) (hg : Continuous g)
    (hpw : Summable (fun k => CircleOuter.linearWeight k*‖UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) k‖))
    (hgw : Summable (fun k => CircleOuter.linearWeight k*‖UnitAddTorus.mFourierCoeff (fun x => (g x:ℂ)) k‖)) :
    (∫ x,p x*CircleFisher.lambda g x ∂torusMeasure 1)=∫ x,CircleFisher.lambda p x*g x ∂torusMeasure 1 := by
  sorry

theorem circle_poisson_generator (p : Torus 1 → ℝ) (hp : Continuous p)
    (hsmooth : ContDiff ℝ 3 (fun x : ℝ => p (fun _ => (x:UnitAddCircle))))
    (s : ℝ) (hs : 0<s) (x : Torus 1) :
    HasDerivAt (fun t => CirclePoisson.torusFlow t p x) (-CircleFisher.lambda (CirclePoisson.torusFlow s p) x) s := by
  sorry

theorem circle_poisson_entropy_derivative (p : Torus 1 → ℝ) (hp : Continuous p)
    (hpos : ∀ x,0<p x)
    (hsmooth : ContDiff ℝ 3 (fun x : ℝ => p (fun _ => (x:UnitAddCircle))))
    (s : ℝ) (hs : 0<s) :
    HasDerivAt (fun t => ∫ x,CirclePoisson.torusFlow t p x * Real.log (CirclePoisson.torusFlow t p x) ∂torusMeasure 1)
      (-(∫ x,Real.log (CirclePoisson.torusFlow s p x)*CircleFisher.lambda (CirclePoisson.torusFlow s p) x ∂torusMeasure 1)) s := by
  sorry

theorem circle_poisson_deficit_dissipation (p : Torus 1 → ℝ) (hp : Continuous p)
    (hpos : ∀ x,0<p x) (he : ∀ x,p (-x)=p x) (hm : (∫ x,p x ∂torusMeasure 1)=1)
    (hsmooth : ContDiff ℝ 3 (fun x : ℝ => p (fun _ => (x:UnitAddCircle))))
    (s : ℝ) (hs : 0<s) :
    let r : ℕ → ℝ := fun n =>
      (UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) (fun _ => (n:ℤ))).re
    let R : ℕ → ℝ := fun n => Real.exp (-(n:ℝ)*s)*r n
    let D : ℝ → ℝ := fun t =>
      (∫ x,CirclePoisson.torusFlow t p x*Real.log (CirclePoisson.torusFlow t p x) ∂torusMeasure 1)-
        ∑' n : ℕ,Real.exp (-2*(n+1:ℝ)*t)*(r (n+1))^2/(n+1:ℝ)
    HasDerivAt D
      (-(∫ x,CirclePoisson.torusFlow s p x*CircleFisher.lambda (fun y => Real.log (CirclePoisson.torusFlow s p y)) x ∂torusMeasure 1)+
        ((∫ x,(CirclePoisson.torusFlow s p x)^2 ∂torusMeasure 1)-1)) s ∧
    (R 1)^2<1 ∧
      2/(1-(R 1)^2)*(∑' n : ℕ,(R (n+2)-R 1*R (n+1))^2) ≤ -deriv D s := by
  sorry

theorem circle_poisson_deficit_control (p : Torus 1 → ℝ) (hp : Continuous p)
    (hpos : ∀ x,0<p x) (he : ∀ x,p (-x)=p x) (hm : (∫ x,p x ∂torusMeasure 1)=1)
    (hsmooth : ContDiff ℝ 3 (fun x : ℝ => p (fun _ => (x:UnitAddCircle)))) :
    let r : ℕ → ℝ := fun n =>
      (UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) (fun _ => (n:ℤ))).re
    let D : ℝ → ℝ := fun t =>
      (∫ x,CirclePoisson.torusFlow t p x*Real.log (CirclePoisson.torusFlow t p x) ∂torusMeasure 1)-
        ∑' n : ℕ,Real.exp (-2*(n+1:ℝ)*t)*(r (n+1))^2/(n+1:ℝ)
    AntitoneOn D (Set.Ioi (0:ℝ)) ∧ (∀ s : ℝ,0<s → 0≤D s) ∧ Filter.Tendsto D Filter.atTop (nhds 0) := by
  sorry

theorem circle_poisson_initial_continuity (p : Torus 1 → ℝ) (hp : Continuous p)
    (hpos : ∀ x,0<p x) (he : ∀ x,p (-x)=p x) (hm : (∫ x,p x ∂torusMeasure 1)=1)
    (hsmooth : ContDiff ℝ 3 (fun x : ℝ => p (fun _ => (x:UnitAddCircle)))) :
    ContinuousWithinAt (CirclePoisson.deficit p) (Set.Ici 0) 0 := by
  sorry

theorem circle_poisson_integrated_dissipation (p : Torus 1 → ℝ) (hp : Continuous p)
    (hpos : ∀ x,0<p x) (he : ∀ x,p (-x)=p x) (hm : (∫ x,p x ∂torusMeasure 1)=1)
    (hsmooth : ContDiff ℝ 3 (fun x : ℝ => p (fun _ => (x:UnitAddCircle)))) :
    IntegrableOn (fun s => -deriv (CirclePoisson.deficit p) s) (Set.Ioi (0:ℝ)) ∧
      (∫ s in Set.Ioi (0:ℝ),-deriv (CirclePoisson.deficit p) s)=CirclePoisson.deficit p 0 := by
  sorry

theorem circle_entropy_remainder (p : Torus 1 → ℝ) (hp : Continuous p)
    (hpos : ∀ x,0<p x) (he : ∀ x,p (-x)=p x) (hm : (∫ x,p x ∂torusMeasure 1)=1)
    (hsmooth : ContDiff ℝ 3 (fun x : ℝ => p (fun _ => (x:UnitAddCircle)))) :
    Summable (fun n : ℕ => CircleScalar.weight (n+1) (CirclePoisson.moment p 1)*
      (CirclePoisson.moment p (n+2)-CirclePoisson.moment p 1*CirclePoisson.moment p (n+1))^2) ∧
    (∑' n : ℕ,CircleScalar.weight (n+1) (CirclePoisson.moment p 1)*
      (CirclePoisson.moment p (n+2)-CirclePoisson.moment p 1*CirclePoisson.moment p (n+1))^2) ≤
      (∫ x,p x*Real.log (p x) ∂torusMeasure 1)-∑' n : ℕ,(CirclePoisson.moment p (n+1))^2/(n+1:ℝ) := by
  sorry

theorem circle_gamma_actual_density (p : Torus 1 → ℝ) (hp : Continuous p)
    (hm : (∫ x,p x ∂torusMeasure 1)=1)
    (hsmooth : ContDiff ℝ 3 (fun x : ℝ => p (fun _ => (x:UnitAddCircle))))
    (F : ℝ → ℝ) (hcF : ContinuousOn F (Set.Icc (-1:ℝ) 1))
    (hF : ConvexOn ℝ (Set.Icc (-1:ℝ) 1) F) (hinc : MonotoneOn F (Set.Icc (-1:ℝ) 1))
    (hprofile : ∀ x,p x=Real.exp (F ((fourier 1 (x 0)).re))) :
    2*Spin.binaryCost (CirclePoisson.moment p 1)+CircleScalar.gamma (CirclePoisson.moment p 1)+(21/1000)*(CirclePoisson.moment p 2)^2+
      (27/40)*(∑' n : ℕ,(CirclePoisson.moment p (n+3))^2/(n+3:ℝ)) ≤
        ∫ x,p x*Real.log (p x) ∂torusMeasure 1 := by
  sorry

theorem conditional_circle_probability (d : ℕ) (f : Torus d → ℝ)
    (hf : Continuous f) (hpos : ∀ x, 0 < f x) (i : Fin d) (x : Torus d) :
    (∀ z, 0 < ConditionalEntropy.conditionalDensity f i x z) ∧
      (∫ z, ConditionalEntropy.conditionalDensity f i x z ∂AddCircle.haarAddCircle) = 1 ∧
      ∀ n : ℕ, |ConditionalEntropy.conditionalCosineMoment f i n x| ≤ 1 := by
  sorry

theorem conditional_entropy_chain (d : ℕ) (f : Torus d → ℝ)
    (hf : Continuous f) (hpos : ∀ x, 0 < f x)
    (hm : (∫ x, f x ∂torusMeasure d) = 1) :
    (∫ x, f x * Real.log (f x) ∂torusMeasure d) =
      ∑ i : Fin d, ∫ x, f x * ConditionalEntropy.conditionalEntropy f i x ∂torusMeasure d := by
  sorry

theorem conditional_cosine_moments (d : ℕ) (f : Torus d → ℝ)
    (hf : Continuous f) (hpos : ∀ x, 0 < f x)
    (hm : (∫ x, f x ∂torusMeasure d) = 1) (i : Fin d) (n : ℕ) :
    (∫ x, f x * ConditionalEntropy.conditionalCosineMoment f i n x ∂torusMeasure d) =
      (∫ x, f x * (fourier (n : ℤ) (x i)).re ∂torusMeasure d) ∧
    (∫ x, f x * (fourier (n : ℤ) (x i)).re ∂torusMeasure d) ^ 2 ≤
      ∫ x, f x * (ConditionalEntropy.conditionalCosineMoment f i n x) ^ 2 ∂torusMeasure d := by
  sorry

theorem conditional_convex_jensen (d : ℕ) (f : Torus d → ℝ)
    (hf : Continuous f) (hpos : ∀ x, 0 < f x)
    (hm : (∫ x, f x ∂torusMeasure d) = 1) (i : Fin d) (n : ℕ) (a b : ℝ)
    (hr : ∀ x, ConditionalEntropy.conditionalCosineMoment f i n x ∈ Set.Icc a b)
    (ψ : ℝ → ℝ) (hc : ContinuousOn ψ (Set.Icc a b)) (hψ : ConvexOn ℝ (Set.Icc a b) ψ) :
    ψ (∫ x, f x * (fourier (n : ℤ) (x i)).re ∂torusMeasure d) ≤
      ∫ x, f x * ψ (ConditionalEntropy.conditionalCosineMoment f i n x) ∂torusMeasure d := by
  sorry

theorem logarithmic_marginal_shape {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [NeZero μ] (V : ℝ → X → ℝ)
    (hconv : ∀ y, ConvexOn ℝ (Set.Icc (-1 : ℝ) 1) (fun t => V t y))
    (hmono : ∀ y, MonotoneOn (fun t => V t y) (Set.Icc (-1 : ℝ) 1))
    (hI : ∀ t ∈ Set.Icc (-1 : ℝ) 1, Integrable (fun y => Real.exp (V t y)) μ) :
    ConvexOn ℝ (Set.Icc (-1 : ℝ) 1) (fun t => Real.log (∫ y, Real.exp (V t y) ∂μ)) ∧
      MonotoneOn (fun t => Real.log (∫ y, Real.exp (V t y) ∂μ)) (Set.Icc (-1 : ℝ) 1) := by
  sorry

theorem spin_posterior_entropy (f : Torus 12 → ℝ)
    (hf : Continuous f) (hpos : ∀ x, 0 < f x) (i : Fin 12) (σ : Spin.Configuration) :
    let m := ∫ x, f x * Spin.prefixLikelihood i.val σ x ∂torusMeasure 12
    0 < m ∧ m * Spin.binaryCost
      ((∫ x, f x * (Spin.prefixLikelihood i.val σ x * Spin.torusCosines x i) ∂torusMeasure 12) / m) ≤
      ∫ x, f x * (Spin.prefixLikelihood i.val σ x *
        Spin.binaryCost (ConditionalEntropy.conditionalCosineMoment f i 1 x)) ∂torusMeasure 12 := by
  sorry

theorem spin_channel_conditional_entropy (ρ : ProbabilityDensity 12)
    (hc : Continuous ρ.value) (hp : ∀ x, 0 < ρ.value x) :
    (∑ σ : Spin.Configuration, Spin.channelLaw ρ σ *
      Real.log (Spin.channelLaw ρ σ / (1/4096))) ≤
    ∑ i : Fin 12, ∫ x, ρ.value x * Spin.binaryCost
      (ConditionalEntropy.conditionalCosineMoment ρ.value i 1 x) ∂torusMeasure 12 := by
  sorry

theorem spin_count_conditional_entropy (ρ : ProbabilityDensity 12)
    (hc : Continuous ρ.value) (hp : ∀ x, 0 < ρ.value x)
    (hsym : Spin.Exchangeable (Spin.channelLaw ρ)) :
    Spin.relativeEntropy (Spin.countLaw (Spin.channelLaw ρ)) Spin.reference ≤
    ∑ i : Fin 12, ∫ x, ρ.value x * Spin.binaryCost
      (ConditionalEntropy.conditionalCosineMoment ρ.value i 1 x) ∂torusMeasure 12 := by
  sorry

theorem conditional_logarithmic_profile {d : ℕ} (V : (Fin d → ℝ) → ℝ)
    (hc : ContinuousOn V (ConditionalEntropy.cosineCube d))
    (hconv : ∀ v ∈ ConditionalEntropy.cosineCube d, ∀ i : Fin d,
      ConvexOn ℝ (Set.Icc (-1 : ℝ) 1) (fun t => V (Function.update v i t)))
    (hmono : ∀ v ∈ ConditionalEntropy.cosineCube d, ∀ i : Fin d,
      MonotoneOn (fun t => V (Function.update v i t)) (Set.Icc (-1 : ℝ) 1))
    (f : Torus d → ℝ) (hrep : ∀ x, f x = Real.exp (V (ConditionalEntropy.cosineVector x)))
    (i : Fin d) (x : Torus d) :
    ∃ F : ℝ → ℝ, ContinuousOn F (Set.Icc (-1 : ℝ) 1) ∧
      ConvexOn ℝ (Set.Icc (-1 : ℝ) 1) F ∧ MonotoneOn F (Set.Icc (-1 : ℝ) 1) ∧
      ∀ z : UnitAddCircle, ConditionalEntropy.conditionalDensity f i x z = Real.exp (F (fourier 1 z).re) := by
  sorry

theorem conditional_fourier_smoothness (d : ℕ) (a : Frequency d → ℂ)
    (ha : ∀ m : ℕ, Summable (fun k => (1 + frequencyLength k)^m * ‖a k‖))
    (f : Torus d → ℝ)
    (he : ∀ x, (f x : ℂ) = ∑' k, a k * UnitAddTorus.mFourier k x)
    (i : Fin d) (x : Torus d) :
    ContDiff ℝ ∞ (fun t : ℝ => ConditionalEntropy.conditionalDensity f i x (t : UnitAddCircle)) := by
  sorry

theorem conditional_circle_gamma {d : ℕ} (V : (Fin d → ℝ) → ℝ)
    (hc : ContinuousOn V (ConditionalEntropy.cosineCube d))
    (hconv : ∀ v ∈ ConditionalEntropy.cosineCube d, ∀ i : Fin d,
      ConvexOn ℝ (Set.Icc (-1 : ℝ) 1) (fun t => V (Function.update v i t)))
    (hmono : ∀ v ∈ ConditionalEntropy.cosineCube d, ∀ i : Fin d,
      MonotoneOn (fun t => V (Function.update v i t)) (Set.Icc (-1 : ℝ) 1))
    (f : Torus d → ℝ) (hrep : ∀ x, f x = Real.exp (V (ConditionalEntropy.cosineVector x)))
    (a : Frequency d → ℂ) (ha : ∀ m : ℕ, Summable (fun k => (1 + frequencyLength k)^m * ‖a k‖))
    (he : ∀ x, (f x : ℂ) = ∑' k, a k * UnitAddTorus.mFourier k x)
    (i : Fin d) (x : Torus d) :
    2 * Spin.binaryCost (ConditionalEntropy.conditionalCosineMoment f i 1 x) +
      CircleScalar.gamma (ConditionalEntropy.conditionalCosineMoment f i 1 x) +
      (21/1000) * (ConditionalEntropy.conditionalCosineMoment f i 2 x)^2 +
      (27/40) * (∑' n : ℕ, (ConditionalEntropy.conditionalCosineMoment f i (n+3) x)^2 / (n+3 : ℝ)) ≤
        ConditionalEntropy.conditionalEntropy f i x := by
  sorry

theorem spin_channel_gamma_entropy (ρ : ProbabilityDensity 12) (V : (Fin 12 → ℝ) → ℝ)
    (hcV : ContinuousOn V (ConditionalEntropy.cosineCube 12))
    (hconv : ∀ v ∈ ConditionalEntropy.cosineCube 12, ∀ i : Fin 12,
      ConvexOn ℝ (Set.Icc (-1 : ℝ) 1) (fun t => V (Function.update v i t)))
    (hmono : ∀ v ∈ ConditionalEntropy.cosineCube 12, ∀ i : Fin 12,
      MonotoneOn (fun t => V (Function.update v i t)) (Set.Icc (-1 : ℝ) 1))
    (hrep : ∀ x, ρ.value x = Real.exp (V (ConditionalEntropy.cosineVector x)))
    (a : Frequency 12 → ℂ) (ha : ∀ m : ℕ, Summable (fun k => (1 + frequencyLength k)^m * ‖a k‖))
    (he : ∀ x, (ρ.value x : ℂ) = ∑' k, a k * UnitAddTorus.mFourier k x)
    (ψ : ℝ → ℝ) (hc : ContinuousOn ψ (Set.Icc (0 : ℝ) 1))
    (hcv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) ψ)
    (hminor : ∀ t ∈ Set.Ico (0 : ℝ) 1, ψ t ≤ CircleScalar.gamma t) :
    (∀ i : Fin 12, Summable (fun n : ℕ =>
      (∫ x, ρ.value x * (fourier (n+3 : ℤ) (x i)).re ∂torusMeasure 12)^2 / (n+3 : ℝ))) ∧
    2 * (∑ σ : Spin.Configuration, Spin.channelLaw ρ σ * Real.log (Spin.channelLaw ρ σ / (1/4096))) +
      (∑ i : Fin 12, ψ (∫ x, ρ.value x * (fourier 1 (x i)).re ∂torusMeasure 12)) +
      (21/1000) * (∑ i : Fin 12, (∫ x, ρ.value x * (fourier 2 (x i)).re ∂torusMeasure 12)^2) +
      (27/40) * (∑ i : Fin 12, ∑' n : ℕ,
        (∫ x, ρ.value x * (fourier (n+3 : ℤ) (x i)).re ∂torusMeasure 12)^2 / (n+3 : ℝ)) ≤ entropy ρ := by
  sorry

theorem scalar_tail_small :
    EntropyTail.scalarTail 2 < 41963/500000 ∧
      ∀ n : ℕ, n ≤ 2 → EntropyTail.scalarTail n ≤ EntropyTail.scalarBudget n := by
  sorry

theorem scalar_tail_monotonicity :
    Monotone EntropyTail.scalarBudget ∧
    AntitoneOn EntropyTail.heatIntegral (Set.Ioi (0 : ℝ)) ∧
    AntitoneOn EntropyTail.heatComplement (Set.Ioi (0 : ℝ)) ∧
    ∀ n : ℕ, EntropyTail.scalarBudget (n+1)-EntropyTail.scalarBudget n =
      12*(n:ℝ)*((27/40)*((n:ℝ)-1)+4*(21/500)) /
        (((n:ℝ)+1)*((n:ℝ)+2)*((n:ℝ)+3)) := by
  sorry

theorem scalar_tail_heat_reduction :
    (∀ n : ℕ, 0 < n → EntropyTail.scalarTail n ≤ EntropyTail.heatIntegral (1/((n:ℝ)+1/2))) ∧
    ∀ η : ℝ, 0 < η →
      Summable (fun k : Frequency 12 => EntropyTail.scalarTailWeight k *
        Real.exp (-η * ∑ i : Fin 12, (k i : ℝ)^2)) ∧
      IntegrableOn (fun s : ℝ => (s-η)^5*EntropyTail.heatComplement s) (Set.Ioi η) ∧
      EntropyTail.heatIntegral η = EntropyTail.gaussianTail η := by
  sorry

theorem scalar_heat_series (s : ℝ) (hs : 0 < s) :
    Summable (fun k : Frequency 12 => if EntropyTail.outsideCube k then
      Real.exp (-s * ∑ i : Fin 12, (k i : ℝ)^2) else 0) ∧
    EntropyTail.heatComplement s = (∑' k : Frequency 12, if EntropyTail.outsideCube k then
      Real.exp (-s * ∑ i : Fin 12, (k i : ℝ)^2) else 0) ∧
    0 ≤ EntropyTail.heatComplement s := by
  sorry

theorem scalar_heat_large_bounds :
    (∀ s : ℝ, 1 ≤ s → EntropyTail.heatComplement s ≤
      12*(1007/500)*Real.exp (-4*s)*(1+(2101/1000)*Real.exp (-s))^11) ∧
    (∀ s : ℝ, 20 ≤ s → EntropyTail.heatComplement s < 26*Real.exp (-4*s)) := by
  sorry

theorem scalar_heat_global_bound (s : ℝ) (hs : 0 < s) :
    0 ≤ EntropyTail.heatComplement s ∧ EntropyTail.heatComplement s ≤ Real.pi^6/s^6 := by
  sorry

theorem scalar_heat_panel (v w η : ℝ) (hv : 0 < v) (hvw : v ≤ w) :
    (1/120 : ℝ)*(∫ s in v..w, (max (s-η) 0)^5*EntropyTail.heatComplement s) ≤
      (EntropyTail.heatComplement v/720)*((max (w-η) 0)^6-(max (v-η) 0)^6) := by
  sorry

theorem scalar_heat_infinite_tail (η : ℝ) (hη : 0 < η) (hη20 : η ≤ 20) :
    (1/120 : ℝ)*(∫ s in Set.Ioi (20 : ℝ), (s-η)^5*EntropyTail.heatComplement s) <
      667/(2*10^32) := by
  sorry

theorem scalar_heat_derivative (η : ℝ) (hη : 0 < η) :
    HasDerivAt EntropyTail.heatIntegral
      (-(∑' k : Frequency 12, EntropyTail.scalarTailWeight k *
        (∑ i : Fin 12, (k i : ℝ)^2) * Real.exp (-η*(∑ i : Fin 12, (k i : ℝ)^2)))) η ∧
    η*(∑' k : Frequency 12, EntropyTail.scalarTailWeight k *
      (∑ i : Fin 12, (k i : ℝ)^2) * Real.exp (-η*(∑ i : Fin 12, (k i : ℝ)^2))) ≤ Real.pi^6/120 := by
  sorry

theorem scalar_heat_log_growth (η ξ : ℝ) (hη : 0 < η) (hηξ : η ≤ ξ) :
    EntropyTail.heatIntegral η ≤ EntropyTail.heatIntegral ξ +
      (Real.pi^6/120)*Real.log (ξ/η) := by
  sorry

theorem scalar_unequal_indices (L : Fin 12 → ℕ) :
    (∑' k : Frequency 12, EntropyTail.scalarTailWeight k *
      ∏ i : Fin 12, EntropyTail.scalarCoefficient (L i) (k i).natAbs) ≤
      (1/12 : ℝ)*∑ i : Fin 12, EntropyTail.scalarTail (L i) := by
  sorry

theorem scalar_harmonic_tail (n : ℕ) :
    (harmonic n : ℝ)-2*EntropyTail.scalarCoefficient n 1-EntropyTail.scalarCoefficient n 2 =
      2*∑' j : ℕ, EntropyTail.scalarCoefficient n (j+3)/(j+3 : ℝ) := by
  sorry

/-- A transfer lemma parameterized by the scalar inequality.
The independent scalar_tail_all theorem proves this premise. -/
theorem scalar_to_countable_mixture
    (hscalar : ∀ n : ℕ, EntropyTail.scalarTail n ≤ EntropyTail.scalarBudget n)
    (w : ℕ → ℝ) (N : ℕ → Fin 12 → ℕ) (hw : ∀ n, 0 ≤ w n) (hs : Summable w)
    (hSup : Summable (fun n => w n*EntropyTail.cosineTensor (N n) 0)) :
    (1/2 : ℝ)*(∑' k : Frequency 12,
      EntropyTail.scalarTailWeight k*‖fourierCoeff (EntropyTail.countableCosineMixture w N) k‖^2) ≤
      ∑ i : Fin 12, ((21/1000)*‖fourierCoeff (EntropyTail.countableCosineMixture w N) (Pi.single i (2 : ℤ))‖^2+
        (27/40)*∑' j : ℕ, ‖fourierCoeff (EntropyTail.countableCosineMixture w N) (Pi.single i (j+3 : ℤ))‖^2/(j+3 : ℝ)) := by
  sorry

/-- Conditional assembly of the manuscript's entropy route. Both numerical inputs
are explicit premises for reuse; the unconditional density_endpoint theorem
instantiates this assembly with the proved certificates. -/
theorem entropy_route_density_endpoint
    (hscalar : ∀ n : ℕ, EntropyTail.scalarTail n ≤ EntropyTail.scalarBudget n)
    (ψ : ℝ → ℝ) (hc : ContinuousOn ψ (Set.Icc (0 : ℝ) 1))
    (hcv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) ψ)
    (hminor : ∀ t ∈ Set.Ico (0 : ℝ) 1, ψ t ≤ CircleScalar.gamma t)
    (hspin : ∀ q : Spin.Count → ℝ, Spin.Feasible q → Spin.mean q ∈ Set.Icc (0 : ℝ) 1 →
      (Spin.mean q)^4/250 ≤ Spin.functional q+12*ψ (Spin.mean q))
    (d : ℕ) (hd : 12 ≤ d) (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    spectralEnergy ρ ≤ ENNReal.ofReal (2*entropy ρ) := by
  sorry

/-- The manuscript's scalar singular-tail inequality, with every numerical
row and the infinite large-index range proved in the solution. -/
theorem scalar_tail_all (n : ℕ) :
    EntropyTail.scalarTail n ≤ EntropyTail.scalarBudget n := by
  sorry

/-- Auxiliary assembly parameterized by the spin/minorant certificate.
The unconditional main targets instantiate it with the proved certificate;
this conditional lemma does not add assumptions to those main statements. -/
theorem entropy_route_endpoint_from_spin
    (ψ : ℝ → ℝ) (hc : ContinuousOn ψ (Set.Icc (0 : ℝ) 1))
    (hcv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) ψ)
    (hminor : ∀ t ∈ Set.Ico (0 : ℝ) 1, ψ t ≤ CircleScalar.gamma t)
    (hspin : ∀ q : Spin.Count → ℝ, Spin.Feasible q → Spin.mean q ∈ Set.Icc (0 : ℝ) 1 →
      (Spin.mean q)^4/250 ≤ Spin.functional q+12*ψ (Spin.mean q))
    (d : ℕ) (hd : 12 ≤ d) (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    spectralEnergy ρ ≤ ENNReal.ofReal (2*entropy ρ) := by
  sorry

end BecknerOnofri.Target


/-! Full-manuscript extension: exact dimension-eleven targets from Theorem 1.2
and Section 4 of the 20260921T180354Z manuscript. The high-dimensional
131-target baseline has been frozen separately. -/
namespace BecknerOnofri.Target
open HighDim
open Set

/-- The explicitly specified periodization, including its actual mass/domain. -/
theorem eleven_profile_regular :
    ∃ ρ : ProbabilityDensity 11, ρ.value = Eleven.periodizedProfile ∧
      ρ.FiniteEntropy ∧ SmoothOnTorus ρ.value ∧ ∀ x, 0 < ρ.value x := by
  sorry

/-- The entropy bound applies to exactly the manuscript's profile. -/
theorem eleven_competitor_entropy (ρ : ProbabilityDensity 11)
    (hρ : ρ.value = Eleven.periodizedProfile) :
    entropy ρ < (8653 : ℝ)/600 := by
  sorry

/-- Extended Fourier energy: the sharp certified lower bound is not a
finite-shell substitute for the mathematical energy. -/
theorem eleven_competitor_energy (ρ : ProbabilityDensity 11)
    (hρ : ρ.value = Eleven.periodizedProfile) :
    ENNReal.ofReal (2*((14475384292906 : ℝ)/10^12)) < spectralEnergy ρ := by
  sorry

theorem eleven_spectral_pressure :
    (1/30 : EReal) < pressure 11 (spectralThreshold 11) ∧
      coefficientDefect 11 (spectralCoefficient 11) = pressure 11 (spectralThreshold 11) := by
  sorry

theorem eleven_transition_interval :
    (3543 : ℝ)/200 < Eleven.globalTransition ∧
    Eleven.globalTransition < 2063/100 ∧
    (2063 : ℝ)/100 < spectralThreshold 11 ∧ spectralThreshold 11 < 22 := by
  sorry

theorem eleven_uniform_unique (β : ℝ) (hβ : 0 ≤ β) (hβ₀ : β ≤ 3543/200)
    (ρ : ProbabilityDensity 11) (hρ : ρ.FiniteEntropy) :
    IsGlobalMinimizer β ρ ↔ ρ.value =ᵐ[torusMeasure 11] (fun _ => 1) := by
  sorry

theorem eleven_coexistence :
    IsGlobalMinimizer Eleven.globalTransition (uniformDensity 11) ∧
    ∃ ρ : ProbabilityDensity 11, IsGlobalMinimizer Eleven.globalTransition ρ ∧
      SmoothOnTorus ρ.value ∧ (∀ x, 0 < ρ.value x) ∧
      ¬ (ρ.value =ᵐ[torusMeasure 11] (fun _ => 1)) := by
  sorry

/-- Actual second derivative of free energy, not a renamed quadratic form. -/
theorem eleven_uniform_hessian :
    0 < 1 - Eleven.globalTransition / spectralThreshold 11 ∧
    ∀ h : Torus 11 → ℝ, SmoothOnTorus h → MeanZero h →
      (1 - Eleven.globalTransition / spectralThreshold 11) *
          (∫ x, (h x)^2 ∂torusMeasure 11) ≤ Eleven.uniformHessian Eleven.globalTransition h := by
  sorry

/-- Finiteness around the transition is included so real projections cannot
hide infinite pressure or defect in a differentiability statement. -/
theorem eleven_pressure_corner :
    (∀ β : ℝ, 0 < β → β < 22 → pressure 11 β = (Eleven.pressureReal β : EReal)) ∧
    ¬ DifferentiableAt ℝ Eleven.pressureReal Eleven.globalTransition := by
  sorry

theorem eleven_defect_corner :
    (∃ ε : ℝ, 0 < ε ∧ ε < Eleven.zeroDefectCoefficient ∧
      ∀ A : ℝ, |A - Eleven.zeroDefectCoefficient| < ε →
        coefficientDefect 11 A = (Eleven.defectReal A : EReal)) ∧
    ¬ DifferentiableAt ℝ Eleven.defectReal Eleven.zeroDefectCoefficient := by
  sorry

/-- Exact spectral constant and strict chain needed in the dimension-eleven proof. -/
theorem eleven_spectral_constants :
    spectralThreshold 11 = 64 * Real.pi^5 / 945 ∧
      (2063 : ℝ)/100 < spectralThreshold 11 ∧ spectralThreshold 11 < 22 := by
  sorry

end BecknerOnofri.Target

/-! Full-manuscript low-dimensional endpoint and the finite d=11 scalar range. -/
namespace BecknerOnofri.Target
open HighDim
open scoped ComplexConjugate

theorem low_density_endpoint (d : ℕ) (hd : 1 ≤ d) (hd10 : d ≤ 10)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    (((d : ℝ) / spectralThreshold d : ℝ) : EReal) * (spectralEnergy ρ).toEReal ≤ (entropy ρ : EReal) := by
  sorry

theorem low_potential_endpoint (d : ℕ) (hd : 1 ≤ d) (hd10 : d ≤ 10)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    Integrable (fun x => Real.exp (centered u x)) (torusMeasure d) ∧
      logPartition u ≤ ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal) := by
  sorry

theorem low_density_rigidity (d : ℕ) (hd : 2 ≤ d) (hd10 : d ≤ 10)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    ((((d : ℝ) / spectralThreshold d : ℝ) : EReal) * (spectralEnergy ρ).toEReal = (entropy ρ : EReal) ↔
      ρ.value =ᵐ[torusMeasure d] fun _ => 1) := by
  sorry

theorem low_potential_rigidity (d : ℕ) (hd : 2 ≤ d) (hd10 : d ≤ 10)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    (logPartition u = ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal) ↔
      ∃ c : ℝ, u =ᵐ[torusMeasure d] fun _ => c) := by
  sorry

theorem low_circle_potential (u : Torus 1 → ℝ) (hu : InCriticalSobolev u) :
    (logPartition u = ((collapseCoefficient 1 * potentialEnergy u : ℝ) : EReal) ↔
      ∃ a : ℂ, ‖a‖ < 1 ∧ ∃ c : ℝ,
        u =ᵐ[torusMeasure 1] fun x => -2 * Real.log ‖1-conj a*fourier 1 (x 0)‖+c) := by
  sorry

theorem low_circle_density (ρ : ProbabilityDensity 1) (hρ : ρ.FiniteEntropy) :
    ((((1 : ℝ) / spectralThreshold 1 : ℝ) : EReal) * (spectralEnergy ρ).toEReal = (entropy ρ : EReal) ↔
      ∃ a : ℂ, ‖a‖ < 1 ∧ ρ.value =ᵐ[torusMeasure 1]
        fun x => (1-‖a‖^2)/‖fourier 1 (x 0)-a‖^2) := by
  sorry

theorem low_coefficient_sharp (d : ℕ) (hd : 1 ≤ d) (hd10 : d ≤ 10) :
    IsLeast {A : ℝ | ∀ u : Torus d → ℝ, InCriticalSobolev u →
      logPartition u ≤ ((A * potentialEnergy u : ℝ) : EReal)} (collapseCoefficient d) := by
  sorry

theorem low_pressure_formula (d : ℕ) (hd : 1 ≤ d) (hd10 : d ≤ 10) (β : ℝ) :
    pressure d β = if β ≤ 2 * (d : ℝ) then 0 else ⊤ := by
  sorry

theorem low_coefficient_formula (d : ℕ) (hd : 1 ≤ d) (hd10 : d ≤ 10) (A : ℝ) :
    coefficientDefect d A = if collapseCoefficient d ≤ A then 0 else ⊤ := by
  sorry

theorem low_physical_density_endpoint (d : ℕ) (hd : 1 ≤ d) (hd10 : d ≤ 10)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    Integrable (fun z : Torus d × Torus d =>
      Legacy.TorusEndpoint.GreenKernelReal.realGreen d (z.1-z.2) * ρ.value z.1 * ρ.value z.2)
        ((torusMeasure d).prod (torusMeasure d)) ∧
    (d : ℝ) * (∫ x, ∫ y, Legacy.TorusEndpoint.GreenKernelReal.realGreen d (x-y) *
      ρ.value x * ρ.value y ∂torusMeasure d ∂torusMeasure d) ≤ entropy ρ := by
  sorry

theorem eleven_scalar_finite (n : ℕ) (hn : 1 ≤ n) (hn21 : n ≤ 21) :
    (1/2000 : ℝ) < 11 * (harmonic n : ℝ) -
      ((3543 : ℝ)/200) / spectralThreshold 11 * Eleven.scalarEnergy n := by
  sorry

end BecknerOnofri.Target

namespace BecknerOnofri.Target
open HighDim

theorem eleven_scalar_all (n : ℕ) (hn : 1 ≤ n) :
    (1/2000 : ℝ) < 11 * (harmonic n : ℝ) -
      ((3543 : ℝ)/200) / spectralThreshold 11 * Eleven.scalarEnergy n := by
  sorry

theorem eleven_theta_integral :
    IntegrableOn (Legacy.BecknerOnofri.ThetaDomination.thetaIntegrand
      Legacy.BecknerOnofri.ThetaDomination.realTheta 11) (Set.Ici (1 : ℝ)) ∧
    Legacy.BecknerOnofri.ThetaDomination.thetaIntegral
      Legacy.BecknerOnofri.ThetaDomination.realTheta 11 < (5/2 : ℝ) := by
  sorry

end BecknerOnofri.Target

namespace BecknerOnofri.Target
open HighDim

theorem student_beta_integral (d : ℕ) (a c : ℝ) (ha : (d:ℝ)/2 < a) (hc : 0 < c) :
    (∫ x : Fin d → ℝ, (1+c*∑ i, (x i)^2)^(-a)) =
      (Real.pi/c)^((d:ℝ)/2) * Real.Gamma (a-(d:ℝ)/2) / Real.Gamma a := by
  sorry

theorem eleven_profile_mass  :
    (∀ x, 0 < Eleven.periodizedProfile x) ∧
      Integrable Eleven.periodizedProfile (torusMeasure 11) ∧
      (∫ x, Eleven.periodizedProfile x ∂torusMeasure 11) = 1 := by
  sorry

theorem eleven_euclidean_entropy  :
    Integrable (fun x : Fin 11 → ℝ => Eleven.euclideanProfile x * Real.log (Eleven.euclideanProfile x)) ∧
      (∫ x : Fin 11 → ℝ, Eleven.euclideanProfile x * Real.log (Eleven.euclideanProfile x)) =
        Real.log (3*5^12/(2^9*Real.pi^6)) + 17897/2520 ∧
      (∫ x : Fin 11 → ℝ, Eleven.euclideanProfile x * Real.log (Eleven.euclideanProfile x)) < 721/50 := by
  sorry

end BecknerOnofri.Target

namespace BecknerOnofri.Target
open HighDim

theorem eleven_coordinate_marginal (t : ℝ) :
    (∫ x : Fin 10 → ℝ, Eleven.euclideanProfile (Fin.cons t x)) =
      1280/(63*Real.pi) * (1+25*t^2)^(-6 : ℤ) := by
  sorry

theorem eleven_entropy_chain  :
    (∀ y ∈ Eleven.labelCube, (∑' n : Frequency 11, Eleven.conditionalLabel y n) = 1) ∧
    IntegrableOn (fun y : Fin 11 → ℝ => Eleven.periodizedProfile (fun i => (y i : UnitAddCircle)) *
      ∑' n : Frequency 11, Eleven.conditionalLabel y n * Real.log (Eleven.conditionalLabel y n)) Eleven.labelCube ∧
    (∫ y, Eleven.periodizedProfile y * Real.log (Eleven.periodizedProfile y) ∂torusMeasure 11) =
      (∫ x : Fin 11 → ℝ, Eleven.euclideanProfile x * Real.log (Eleven.euclideanProfile x)) +
        Eleven.conditionalLabelEntropy := by
  sorry

end BecknerOnofri.Target

namespace BecknerOnofri.Target
open HighDim

theorem eleven_label_moment  :
    HasSum Eleven.coordinateLabelProbability 1 ∧
      Summable (fun n : ℤ => Eleven.coordinateLabelProbability n*(n.natAbs:ℝ)) ∧
      Eleven.coordinateLabelMoment < (83927/8121093750:ℝ) := by
  sorry

theorem eleven_coordinate_label_entropy  :
    Summable (fun n : ℤ => Eleven.coordinateLabelProbability n*Real.log (Eleven.coordinateLabelProbability n)) ∧
      11 * (-(∑' n : ℤ, Eleven.coordinateLabelProbability n*Real.log (Eleven.coordinateLabelProbability n))) < (1/600:ℝ) := by
  sorry

end BecknerOnofri.Target

namespace BecknerOnofri.Target
open HighDim

theorem eleven_label_entropy_chain  :
    HasSum Eleven.labelProbability 1 ∧
    Summable (fun n : Frequency 11 => Eleven.labelProbability n * Real.log (Eleven.labelProbability n)) ∧
    Eleven.conditionalLabelEntropy ≤ Eleven.labelEntropy ∧
    Eleven.labelEntropy ≤ 11 * (-(∑' n : ℤ,
      Eleven.coordinateLabelProbability n * Real.log (Eleven.coordinateLabelProbability n))) ∧
    Eleven.conditionalLabelEntropy < (1/600:ℝ) := by
  sorry

theorem eleven_competitor_entropy_fine (ρ : ProbabilityDensity 11)
    (hρ : ρ.value = Eleven.periodizedProfile) :
    entropy ρ < (7305164/10^6 + 17897/2520 + 1/600:ℝ) := by
  sorry

end BecknerOnofri.Target

/-! Section 4: the actual Gamma-Gaussian Fourier transform and periodization. -/
namespace BecknerOnofri.Target
open HighDim

theorem eleven_half_integer_laplace (z : ℝ) (hz : 0 ≤ z) :
    (∫ t in Set.Ioi (0:ℝ), t^((9:ℝ)/2)*Real.exp (-t-z^2/(4*t))) =
      Real.sqrt Real.pi*Real.exp (-z)*Eleven.fourierPolynomial z/32 := by
  sorry

theorem eleven_euclidean_fourier (w : EuclideanSpace ℝ (Fin 11)) :
    (∫ x : EuclideanSpace ℝ (Fin 11),
      Complex.exp (-((2*Real.pi*inner ℝ w x):ℝ)*Complex.I) *
        (Eleven.euclideanProfile (fun i => x i):ℂ)) =
          (Eleven.fourierProfile (2*Real.pi*‖w‖/5):ℂ) := by
  sorry

theorem eleven_periodized_fourier (k : Frequency 11) :
    fourierCoeff Eleven.periodizedProfile k =
      (Eleven.fourierProfile (2*Real.pi*frequencyLength k/5):ℂ) ∧
    0 < (fourierCoeff Eleven.periodizedProfile k).re := by
  sorry

theorem eleven_curve_convexity :
    ConvexOn ℝ (Set.Ioo 0 22) Eleven.pressureReal ∧
    ∃ ε : ℝ, 0 < ε ∧ ConvexOn ℝ
      (Set.Ioo (Eleven.zeroDefectCoefficient-ε) (Eleven.zeroDefectCoefficient+ε)) Eleven.defectReal := by
  sorry

theorem eleven_pressure_derivative_jump : ∃ p : ℝ, 0 < p ∧
    HasDerivWithinAt Eleven.pressureReal 0 (Set.Iio Eleven.globalTransition) Eleven.globalTransition ∧
    HasDerivWithinAt Eleven.pressureReal p (Set.Ioi Eleven.globalTransition) Eleven.globalTransition := by
  sorry

theorem eleven_defect_derivative_jump : ∃ q : ℝ, q < 0 ∧
    HasDerivWithinAt Eleven.defectReal q (Set.Iio Eleven.zeroDefectCoefficient) Eleven.zeroDefectCoefficient ∧
    HasDerivWithinAt Eleven.defectReal 0 (Set.Ioi Eleven.zeroDefectCoefficient) Eleven.zeroDefectCoefficient := by
  sorry

theorem finite_entropy_physical_bound (d : ℕ) (hd : 0 < d)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy)
    (a : ℝ) (ha : 0 < a) (had : a < (d:ℝ)) :
    Integrable (fun z : Torus d × Torus d =>
      Legacy.TorusEndpoint.GreenKernelReal.realGreen d (z.1-z.2)*ρ.value z.1*ρ.value z.2)
      ((torusMeasure d).prod (torusMeasure d)) ∧
    0 ≤ (∫ x, ∫ y, Legacy.TorusEndpoint.GreenKernelReal.realGreen d (x-y)*
      ρ.value x*ρ.value y ∂torusMeasure d ∂torusMeasure d) ∧
    (∫ x, ∫ y, Legacy.TorusEndpoint.GreenKernelReal.realGreen d (x-y)*
      ρ.value x*ρ.value y ∂torusMeasure d ∂torusMeasure d) ≤
      2/a*entropy ρ + 1/a*Real.log
        (∫ x, ∫ y, Real.exp (a*Legacy.TorusEndpoint.GreenKernelReal.realGreen d (x-y))
          ∂torusMeasure d ∂torusMeasure d) := by
  sorry

theorem heat_regularization_smooth (d : ℕ) (ρ : ProbabilityDensity d)
    (t : ℝ) (ht : 0 < t) :
    ∃ η : ProbabilityDensity d, η.value = heatRegularization ρ t ∧ η.FiniteEntropy ∧
      SmoothOnTorus η.value ∧ ∀ x, 0 < η.value x := by
  sorry

theorem heat_interaction_limit (d : ℕ) (hd : 0 < d)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy)
    (t : ℕ → ℝ) (ht : ∀ n, 0 < t n) (ht0 : Filter.Tendsto t Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫ x, ∫ y,
      Legacy.TorusEndpoint.GreenKernelReal.realGreen d (x-y)*
      heatRegularization ρ (t n) x*heatRegularization ρ (t n) y ∂torusMeasure d ∂torusMeasure d)
      Filter.atTop (nhds (∫ x, ∫ y, Legacy.TorusEndpoint.GreenKernelReal.realGreen d (x-y)*
        ρ.value x*ρ.value y ∂torusMeasure d ∂torusMeasure d)) := by
  sorry


theorem eleven_local_uniqueness (β₀ : ℝ) (hβ : 0 < β₀) (hβσ : β₀ < spectralThreshold 11) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (β : ℝ) (u : Torus 11 → ℝ),
      |β-β₀| < ε → InSobolev 11 u → MeanZero u → sobolevNorm 11 u < ε →
      (u =ᵐ[torusMeasure 11] fun x => β*(∫ y,
        Legacy.TorusEndpoint.GreenKernelReal.realGreen 11 y*
          (normalizedGibbs u (x-y)-1) ∂torusMeasure 11)) →
      u =ᵐ[torusMeasure 11] (fun _ => 0) := by
  sorry

theorem closed_cube_positive_taylor (d : ℕ) (f : ClosedCubeTaylor.Space d → ℝ)
    (hf : ContDiffOn ℝ ∞ f (Set.Icc (0 : ClosedCubeTaylor.Space d) 1))
    (hpos : ClosedCubeTaylor.nonnegativePartials f) :
    (∀ a, 0 ≤ ClosedCubeTaylor.coefficient f a) ∧
    HasSum (ClosedCubeTaylor.coefficient f) (f 1) ∧
    (∀ y : ClosedCubeTaylor.Cube d,
      HasSum (fun a => ClosedCubeTaylor.coefficient f a * ClosedCubeTaylor.monomial a y)
        (f (fun i => (y i : ℝ)))) ∧
    TendstoUniformly (fun s : Finset (ClosedCubeTaylor.Index d) =>
      fun y : ClosedCubeTaylor.Cube d =>
        ∑ a ∈ s, ClosedCubeTaylor.coefficient f a * ClosedCubeTaylor.monomial a y)
      (fun y => f (fun i => (y i : ℝ))) Filter.atTop := by
  sorry

theorem pressure_smooth_sup (d : ℕ) (hd : 0 < d) (β : ℝ) (hβ : 0 < β) :
    pressure d β = ⨆ (ρ : ProbabilityDensity d) (_ : ρ.FiniteEntropy)
      (_ : SmoothOnTorus ρ.value) (_ : ∀ x, 0 < ρ.value x),
      (β / (2 * spectralThreshold d) : ℝ) * (spectralEnergy ρ).toEReal -
        (entropy ρ : EReal) := by
  sorry


theorem heat_entropy_limit (d : ℕ) (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy)
    (t : ℕ → ℝ) (ht : ∀ n, 0 < t n) (ht0 : Filter.Tendsto t Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫ x, heatRegularization ρ (t n) x *
      Real.log (heatRegularization ρ (t n) x) ∂torusMeasure d)
      Filter.atTop (nhds (entropy ρ)) := by
  sorry

theorem heat_l1_limit (d : ℕ) (ρ : ProbabilityDensity d)
    (t : ℕ → ℝ) (ht : ∀ n, 0 < t n) (ht0 : Filter.Tendsto t Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫ x, ‖heatRegularization ρ (t n) x - ρ.value x‖ ∂torusMeasure d)
      Filter.atTop (nhds 0) := by
  sorry

end BecknerOnofri.Target

namespace BecknerOnofri.Target
open HighDim Filter
open scoped Topology BigOperators

theorem low_scalar_gap (d n : ℕ) (hd2 : 2 ≤ d) (hd10 : d ≤ 10) (hn : 1 ≤ n) :
    (3/1100 : ℝ) < (d:ℝ)*(_root_.harmonic n:ℝ) -
      (2*(d:ℝ)/spectralThreshold d)*LowScalar.energy d n := by
  sorry

theorem low_hypergeometric_identity (n m : ℕ) :
    (∀ l, 0 ≤ LowScalar.mixingWeight n m l) ∧
    (∑ l ∈ Finset.range (n+1), LowScalar.mixingWeight n m l) = 1 ∧
    (∀ l, min n m < l → LowScalar.mixingWeight n m l = 0) ∧
    ∀ j : ℤ, EntropyTail.scalarCoefficient n j.natAbs * EntropyTail.scalarCoefficient m j.natAbs =
      ∑ l ∈ Finset.range (n+1), LowScalar.mixingWeight n m l * EntropyTail.scalarCoefficient l j.natAbs := by
  sorry

theorem low_harmonic_identity (n : ℕ) :
    HasSum (fun j : ℕ => EntropyTail.scalarCoefficient n (j+1)/(j+1:ℝ))
      ((_root_.harmonic n:ℝ)/2) := by
  sorry

theorem low_theta_integral : LowScalar.thetaIntegral 10 < (41/25 : ℝ) := by
  sorry

theorem low_theta_dimension_bound (d : ℕ) (hd : 0 < d) (hd10 : d ≤ 10) :
    LowScalar.thetaIntegral d < (d:ℝ)/10*(41/25 : ℝ) := by
  sorry

theorem first_shell_order_parameter (d : ℕ) (f : Torus d → ℝ) :
    (firstShellOrderParameter f)^2 =
      ∑' k : Frequency d, if frequencyLength k = 1 then ‖fourierCoeff f k‖^2 else 0 := by
  sorry

theorem order_parameter_onset (d : ℕ) (hd : 12 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ β in 𝓝[>] (spectralThreshold d),
      ∀ ρ : ProbabilityDensity d, IsGlobalMinimizer β ρ →
        |firstShellOrderParameter ρ.value -
          Real.sqrt (2*(d:ℝ)/kappa d)*Real.sqrt (onsetDelta d β)| ≤ C*onsetDelta d β := by
  sorry

theorem pressure_derivative_at_threshold (d : ℕ) (hd : 12 ≤ d) :
    HasDerivAt (fun β => (pressure d β).toReal) 0 (spectralThreshold d) := by
  sorry

end BecknerOnofri.Target

namespace BecknerOnofri.Target
open HighDim

theorem finite_entropy_green_potential (d : ℕ) (hd : 0 < d) (β : ℝ) (hβ : 0 < β)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    InCriticalSobolev (Gap.densityPotential β ρ.value) ∧
      MeanZero (Gap.densityPotential β ρ.value) := by
  sorry

theorem primal_gap_identity (d : ℕ) (hd : 0 < d) (A : ℝ) (hA : 0 < A)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) (hm : MeanZero u) :
    Real.log (∫ x,Real.exp (u x) ∂torusMeasure d)-A*potentialEnergy u =
      Gap.densityValue (Gap.coefficient d A) (normalizedGibbs u) -
        A*potentialEnergy (u-Gap.densityPotential (Gap.coefficient d A) (normalizedGibbs u)) := by
  sorry

theorem dual_gap_identity (d : ℕ) (hd : 0 < d) (A : ℝ) (hA : 0 < A)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    Gap.densityValue (Gap.coefficient d A) ρ.value =
      Real.log (∫ x,Real.exp (Gap.densityPotential (Gap.coefficient d A) ρ.value x) ∂torusMeasure d)-
        A*potentialEnergy (Gap.densityPotential (Gap.coefficient d A) ρ.value)-
        Gap.relativeEntropy ρ.value (normalizedGibbs (Gap.densityPotential (Gap.coefficient d A) ρ.value)) := by
  sorry

end BecknerOnofri.Target

namespace BecknerOnofri.Target
open HighDim
open Filter Asymptotics
open scoped Topology

theorem local_quartic_signs (d : ℕ) (hd : 11 ≤ d) :
    0 < kappa d ∧ quarticA d < 0 ∧ 0 < quarticB d ∧
    ∀ n : ℕ, 0 < n → n ≤ d → (quarticA d+quarticB d/2*((n:ℝ)-1))/(n:ℝ) < 0 := by
  sorry

theorem local_quartic_pressure_order (d m n : ℕ) (hd : 11 ≤ d)
    (hm : 0 < m) (hmn : m < n) (hnd : n ≤ d) :
    -1/(4*((quarticA d+quarticB d/2*((m:ℝ)-1))/(m:ℝ))) <
    -1/(4*((quarticA d+quarticB d/2*((n:ℝ)-1))/(n:ℝ))) := by
  sorry

theorem pressure_first_derivative_limits (d : ℕ) (hd : 12 ≤ d) :
    Tendsto (deriv (fun β => (pressure d β).toReal)) (𝓝[<] (spectralThreshold d)) (𝓝 0) ∧
    Tendsto (deriv (fun β => (pressure d β).toReal)) (𝓝[>] (spectralThreshold d)) (𝓝 0) := by
  sorry

theorem pressure_second_derivative_limits (d : ℕ) (hd : 12 ≤ d) :
    Tendsto (deriv (deriv (fun β => (pressure d β).toReal)))
      (𝓝[<] (spectralThreshold d)) (𝓝 0) ∧
    Tendsto (deriv (deriv (fun β => (pressure d β).toReal)))
      (𝓝[>] (spectralThreshold d)) (𝓝 ((d:ℝ)/(kappa d*(spectralThreshold d)^2))) ∧
    0 < (d:ℝ)/(kappa d*(spectralThreshold d)^2) := by
  sorry

theorem pressure_first_derivative_expansion (d : ℕ) (hd : 12 ≤ d) :
    (fun β => deriv (fun γ => (pressure d γ).toReal) β-
      (d:ℝ)/(kappa d*spectralThreshold d)*onsetDelta d β)
      =O[𝓝[>] (spectralThreshold d)] (fun β => (onsetDelta d β)^2) := by
  sorry

theorem pressure_second_derivative_expansion (d : ℕ) (hd : 12 ≤ d) :
    (fun β => deriv (deriv (fun γ => (pressure d γ).toReal)) β-
      (d:ℝ)/(kappa d*(spectralThreshold d)^2))
      =O[𝓝[>] (spectralThreshold d)] (onsetDelta d) := by
  sorry

theorem pressure_concentration_divergence (d : ℕ) (hd : 0 < d) (β : ℝ) (hβ : 2*(d:ℝ) < β) :
    pressure d β = ⊤ := by
  sorry

theorem coefficient_concentration_divergence (d : ℕ) (hd : 0 < d) (A : ℝ)
    (hA : A < collapseCoefficient d) : coefficientDefect d A = ⊤ := by
  sorry

end BecknerOnofri.Target

namespace BecknerOnofri.Target
open HighDim

theorem general_pressure_geometry (d : ℕ) (hd : 0 < d) :
    MonotoneOn (pressure d) (Set.Icc 0 (2*(d:ℝ))) ∧
    (∀ β ∈ Set.Icc (0:ℝ) (2*(d:ℝ)), 0 ≤ pressure d β) ∧
    ∀ β ∈ Set.Icc (0:ℝ) (2*(d:ℝ)), ∀ γ ∈ Set.Icc (0:ℝ) (2*(d:ℝ)),
    ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a+b=1 →
      pressure d (a*β+b*γ) ≤ (a:EReal)*pressure d β+(b:EReal)*pressure d γ := by
  sorry

theorem general_coefficient_geometry (d : ℕ) (hd : 0 < d) :
    AntitoneOn (coefficientDefect d) (Set.Ioi 0) ∧
    (∀ A ∈ Set.Ioi (0:ℝ), 0 ≤ coefficientDefect d A) ∧
    ∀ A ∈ Set.Ioi (0:ℝ), ∀ B ∈ Set.Ioi (0:ℝ),
    ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a+b=1 →
      coefficientDefect d (a*A+b*B) ≤ (a:EReal)*coefficientDefect d A+(b:EReal)*coefficientDefect d B := by
  sorry

theorem interaction_physical_positive (d : ℕ) (hd : 0 < d) (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    VariationalCurves.interaction ρ = (1/2:ℝ)*(∫ x,∫ y,
      Legacy.TorusEndpoint.GreenKernelReal.realGreen d (x-y)*ρ.value x*ρ.value y
        ∂torusMeasure d ∂torusMeasure d) ∧
    (0 < VariationalCurves.interaction ρ ↔ ¬ (ρ.value =ᵐ[torusMeasure d] (fun _ => 1))) := by
  sorry

theorem general_transition_quotient (d : ℕ) (hd : 0 < d) :
    VariationalCurves.globalTransition d = sInf (VariationalCurves.entropyInteractionQuotients d) := by
  sorry

theorem general_pressure_zero_set (d : ℕ) (hd : 0 < d) (β : ℝ) (hβ : 0 ≤ β) :
    pressure d β = 0 ↔ β ≤ VariationalCurves.globalTransition d := by
  sorry

theorem general_coefficient_zero_set (d : ℕ) (hd : 0 < d) (A : ℝ) (hA : 0 < A) :
    coefficientDefect d A = 0 ↔ VariationalCurves.zeroDefectCoefficient d ≤ A := by
  sorry

theorem general_threshold_bounds (d : ℕ) (hd : 0 < d) :
    0 < VariationalCurves.globalTransition d ∧
    VariationalCurves.globalTransition d ≤ min (2*(d:ℝ)) (spectralThreshold d) ∧
    max (collapseCoefficient d) (spectralCoefficient d) ≤ VariationalCurves.zeroDefectCoefficient d := by
  sorry

theorem eleven_unscaled_fourier (w : EuclideanSpace ℝ (Fin 11)) :
    (∫ x : EuclideanSpace ℝ (Fin 11),
      Complex.exp (-((2*Real.pi*inner ℝ w x):ℝ)*Complex.I) * (((122880/Real.pi^6)*(1+‖x‖^2)^(-(11:ℝ)):ℝ):ℂ)) =
        (Eleven.fourierProfile (2*Real.pi*‖w‖):ℂ) := by
  sorry

end BecknerOnofri.Target

namespace BecknerOnofri.Target

theorem coordinate_marginal_entropy (d : ℕ) (ρ : HighDim.ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) (I : Finset (Fin d)) :
    Integrable (fun x => HighDim.coordinateMarginal ρ I x * Real.log (HighDim.coordinateMarginal ρ I x))
      (HighDim.torusMeasure d) ∧ HighDim.coordinateMarginalEntropy ρ I ≤ HighDim.entropy ρ := by
  sorry

theorem entropy_shearer_all_subsets (d r : ℕ) (hr : 1 ≤ r) (hrd : r ≤ d)
    (ρ : HighDim.ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    (d:ℝ) / ((r:ℝ)*(d.choose r:ℝ)) *
      (∑ I ∈ (Finset.univ : Finset (Fin d)).powersetCard r, HighDim.coordinateMarginalEntropy ρ I)
      ≤ HighDim.entropy ρ := by
  sorry

end BecknerOnofri.Target

namespace BecknerOnofri.Target

theorem circle_entropy_full_domain (ρ : HighDim.ProbabilityDensity 1) :
    (ρ.FiniteEntropy → HighDim.extendedEntropy ρ = (HighDim.entropy ρ:EReal)) ∧
    (¬ ρ.FiniteEntropy → HighDim.extendedEntropy ρ = ⊤) ∧
    (HighDim.circlePositiveEnergy ρ).toEReal ≤ HighDim.extendedEntropy ρ := by
  sorry

end BecknerOnofri.Target

namespace BecknerOnofri.Target

theorem cosine_mixture_deletion_energy (d : ℕ) (hd : 12 ≤ d)
    (ρ : HighDim.ProbabilityDensity d) (hρ : HighDim.IsCountableCosineMixture ρ) :
    HighDim.spectralEnergy ρ ≤ ENNReal.ofReal (1/((d:ℝ)-1)) *
      ∑ i : Fin d, HighDim.inversePowerEnergy (d-1)
        (HighDim.coordinateMarginal ρ (Finset.univ.erase i)) := by
  sorry

theorem cosine_mixture_subset_energy (d r : ℕ) (hr : 12 ≤ r) (hrd : r ≤ d)
    (ρ : HighDim.ProbabilityDensity d) (hρ : HighDim.IsCountableCosineMixture ρ) :
    HighDim.spectralEnergy ρ ≤ ENNReal.ofReal ((d:ℝ)/((r:ℝ)*(d.choose r:ℝ))) *
      ∑ I ∈ (Finset.univ : Finset (Fin d)).powersetCard r,
        HighDim.inversePowerEnergy r (HighDim.coordinateMarginal ρ I) := by
  sorry

end BecknerOnofri.Target

namespace BecknerOnofri.Target

theorem primal_extremizer_correspondence (d : ℕ) (hd : 0 < d) (β : ℝ) (hβ : 0 < β)
    (u : HighDim.Torus d → ℝ) (hu : HighDim.InCriticalSobolev u) (hm : HighDim.MeanZero u) :
    (∀ v : HighDim.Torus d → ℝ, HighDim.InCriticalSobolev v →
      HighDim.dualFunctional β v ≤ HighDim.dualFunctional β u) ↔
      (∃ ρ : HighDim.ProbabilityDensity d,
        ρ.value =ᵐ[HighDim.torusMeasure d] HighDim.normalizedGibbs u ∧
        HighDim.IsGlobalMinimizer β ρ) ∧
      u =ᵐ[HighDim.torusMeasure d] HighDim.Gap.densityPotential β (HighDim.normalizedGibbs u) := by
  sorry

theorem dual_extremizer_correspondence (d : ℕ) (hd : 0 < d) (β : ℝ) (hβ : 0 < β)
    (ρ : HighDim.ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    HighDim.IsGlobalMinimizer β ρ ↔
      (∀ v : HighDim.Torus d → ℝ, HighDim.InCriticalSobolev v →
        HighDim.dualFunctional β v ≤
          HighDim.dualFunctional β (HighDim.Gap.densityPotential β ρ.value)) ∧
      ρ.value =ᵐ[HighDim.torusMeasure d]
        HighDim.normalizedGibbs (HighDim.Gap.densityPotential β ρ.value) := by
  sorry

theorem optimizer_euler_equation (d : ℕ) (hd : 0 < d) (β : ℝ) (hβ : 0 < β)
    (u : HighDim.Torus d → ℝ) (hu : HighDim.InCriticalSobolev u) (hm : HighDim.MeanZero u)
    (hmax : ∀ v : HighDim.Torus d → ℝ, HighDim.InCriticalSobolev v →
      HighDim.dualFunctional β v ≤ HighDim.dualFunctional β u) :
    ∀ k : HighDim.NonzeroFrequency d,
      (HighDim.frequencyLength k.val^d : ℂ)*HighDim.fourierCoeff u k.val =
        (β/HighDim.spectralThreshold d : ℝ)*HighDim.fourierCoeff (HighDim.normalizedGibbs u) k.val := by
  sorry

theorem optimizer_smooth_kirkwood (d : ℕ) (hd : 0 < d) (β : ℝ) (hβ : 0 < β)
    (ρ : HighDim.ProbabilityDensity d) (hρ : HighDim.IsGlobalMinimizer β ρ) :
    (∃ q : HighDim.Torus d → ℝ, ρ.value =ᵐ[HighDim.torusMeasure d] q ∧
      HighDim.SmoothOnTorus q ∧ ∀ x, 0 < q x) ∧
    ρ.value =ᵐ[HighDim.torusMeasure d]
      HighDim.normalizedGibbs (HighDim.Gap.densityPotential β ρ.value) ∧
    (∀ k : HighDim.NonzeroFrequency d,
      (HighDim.frequencyLength k.val^d : ℂ)*
        HighDim.fourierCoeff (HighDim.Gap.densityPotential β ρ.value) k.val =
      (β/HighDim.spectralThreshold d : ℝ)*HighDim.fourierCoeff ρ.value k.val) := by
  sorry

end BecknerOnofri.Target

namespace BecknerOnofri.Target

theorem all_optimizer_cubic_symmetry (d : ℕ) (hd : 0 < d)
    (u : HighDim.Torus d → ℝ) (hu : HighDim.InCriticalSobolev u)
    (hm : HighDim.MeanZero u) (hs : HighDim.SmoothOnTorus u)
    (hN : ∀ k : HighDim.Frequency d,
      (HighDim.fourierCoeff u k).im=0 ∧ 0≤(HighDim.fourierCoeff u k).re)
    (hmax : ∀ v : HighDim.Torus d → ℝ, HighDim.InCriticalSobolev v →
      HighDim.dualFunctional (HighDim.spectralThreshold d) v ≤
        HighDim.dualFunctional (HighDim.spectralThreshold d) u)
    (σ : Equiv.Perm (Fin d)) (ε : Fin d → ℤ) (hε : ∀ i,ε i=1 ∨ ε i= -1)
    (x : HighDim.Torus d) : u (fun i => ε i • x (σ i))=u x := by
  sorry

theorem smooth_mixture_singular_tail (ρ : HighDim.ProbabilityDensity 12)
    (hs : HighDim.SmoothOnTorus ρ.value) (hρ : HighDim.IsCountableCosineMixture ρ) :
    (1/2 : ℝ)*(∑' k : HighDim.Frequency 12,
      HighDim.EntropyTail.scalarTailWeight k*‖HighDim.fourierCoeff ρ.value k‖^2) ≤
      ∑ i : Fin 12,((21/1000)*‖HighDim.fourierCoeff ρ.value (Pi.single i (2 : ℤ))‖^2+
        (27/40)*∑' j : ℕ,‖HighDim.fourierCoeff ρ.value (Pi.single i (j+3 : ℤ))‖^2/(j+3 : ℝ)) := by
  sorry

end BecknerOnofri.Target

namespace BecknerOnofri.Target

theorem global_shape_entropy (ρ : HighDim.ProbabilityDensity 12) (hs : HighDim.SmoothOnTorus ρ.value)
    (hp : ∀ x,0<ρ.value x)
    (hperm : ∀ (π : Equiv.Perm (Fin 12)) (x : HighDim.Torus 12),ρ.value (fun i => x (π i))=ρ.value x)
    (hmix : HighDim.IsCountableCosineMixture ρ)
    (V : (Fin 12 → ℝ) → ℝ) (hV : ContDiffOn ℝ ∞ V (HighDim.ConditionalEntropy.cosineCube 12))
    (hlog : ∀ x,Real.log (ρ.value x)=V (HighDim.ConditionalEntropy.cosineVector x))
    (h1 : ∀ v∈HighDim.ConditionalEntropy.cosineCube 12,∀ i : Fin 12,0≤HighDim.cosinePartial i V v)
    (h2 : ∀ v∈HighDim.ConditionalEntropy.cosineCube 12,∀ i : Fin 12,0≤HighDim.cosinePartial i (HighDim.cosinePartial i V) v) :
    (HighDim.fourierCoeff ρ.value (Pi.single (0 : Fin 12) (1 : ℤ))).im=0 ∧
    0≤(HighDim.fourierCoeff ρ.value (Pi.single (0 : Fin 12) (1 : ℤ))).re ∧
    (HighDim.fourierCoeff ρ.value (Pi.single (0 : Fin 12) (1 : ℤ))).re^4/250≤
      HighDim.entropy ρ-(1/2 : ℝ)*(∑' k : HighDim.Frequency 12, (HighDim.frequencyLength k^12)⁻¹*‖HighDim.fourierCoeff ρ.value k‖^2) ∧
    ((HighDim.fourierCoeff ρ.value (Pi.single (0 : Fin 12) (1 : ℤ))).re=0 → ρ.value=(fun _ => 1)) := by
  sorry

end BecknerOnofri.Target

namespace BecknerOnofri.Target
open HighDim Set

theorem global_spin_entropy :
    ∃ ψ : ℝ → ℝ,
      ContinuousOn ψ (Icc (0 : ℝ) 1) ∧ ConvexOn ℝ (Icc (0 : ℝ) 1) ψ ∧
      MonotoneOn ψ (Icc (0 : ℝ) 1) ∧ (∀ t∈Icc (0 : ℝ) 1,0≤ψ t) ∧
      (∀ t∈Icc (0 : ℝ) (1/16),ψ t=(3/40 : ℝ)*t^4) ∧
      (∀ (ρ : ProbabilityDensity 12), SmoothOnTorus ρ.value →
        (∀ x,0<ρ.value x) →
        (∀ (π : Equiv.Perm (Fin 12)) (x : Torus 12),ρ.value (fun i => x (π i))=ρ.value x) →
        IsCountableCosineMixture ρ →
        ∀ (V : (Fin 12 → ℝ) → ℝ), ContDiffOn ℝ ∞ V (ConditionalEntropy.cosineCube 12) →
        (∀ x,Real.log (ρ.value x)=V (ConditionalEntropy.cosineVector x)) →
        (∀ v∈ConditionalEntropy.cosineCube 12,∀ i : Fin 12,0≤cosinePartial i V v) →
        (∀ v∈ConditionalEntropy.cosineCube 12,∀ i : Fin 12,0≤cosinePartial i (cosinePartial i V) v) →
        (∀ σ,0≤Spin.channelLaw ρ σ) ∧ (∑ σ : Spin.Configuration,Spin.channelLaw ρ σ)=1 ∧
        Spin.Exchangeable (Spin.channelLaw ρ) ∧
        (∀ i : Fin 12,(∑ σ : Spin.Configuration,Spin.channelLaw ρ σ*Spin.jointSpin {i} σ)=
          (fourierCoeff ρ.value (Pi.single (0 : Fin 12) (1 : ℤ))).re) ∧
        Spin.channelLaw ρ ∅≤1/4096 ∧
        2*(∑ σ : Spin.Configuration,Spin.channelLaw ρ σ*Real.log (Spin.channelLaw ρ σ/(1/4096)))+
          12*ψ (fourierCoeff ρ.value (Pi.single (0 : Fin 12) (1 : ℤ))).re+
          (∑ i : Fin 12,((21/1000)*‖fourierCoeff ρ.value (Pi.single i (2 : ℤ))‖^2+
            (27/40)*∑' n : ℕ,‖fourierCoeff ρ.value (Pi.single i (n+3 : ℤ))‖^2/(n+3 : ℝ)))≤entropy ρ) ∧
      (∀ (ν : Spin.Configuration → ℝ), (∀ σ,0≤ν σ) →
        (∑ σ : Spin.Configuration,ν σ)=1 → Spin.Exchangeable ν →
        ν ∅≤1/4096 → ∀ t∈Icc (0 : ℝ) 1,
        (∀ i : Fin 12,(∑ σ : Spin.Configuration,ν σ*Spin.jointSpin {i} σ)=t) →
        t^4/250≤2*(∑ σ : Spin.Configuration,ν σ*Real.log (ν σ/(1/4096)))-
          (∑ s : Spin.Order,Spin.weight s*(∑ σ : Spin.Configuration,ν σ*Spin.jointSpin (Spin.firstCoordinates s) σ)^2)+
          12*ψ t) := by
  sorry

end BecknerOnofri.Target

namespace BecknerOnofri.Target
open MeasureTheory ProbabilityTheory Legacy.TorusEndpoint Circle
open scoped ENNReal

theorem circle_rearrangement (f g : Torus 1 → ℝ)
    (hf : Integrable f (torusMeasure 1)) (hg : Integrable g (torusMeasure 1))
    (hf0 : ∀ᵐ x ∂torusMeasure 1,0≤f x) (hg0 : ∀ᵐ x ∂torusMeasure 1,0≤g x)
    (q : UnitAddCircle → ℝ) {C : ℝ} (hq0 : ∀ z,0≤q z) (hqC : ∀ z,q z≤C)
    (hq : ∀ x y,‖x‖≤‖y‖ → q y≤q x) :
    (∀ᵐ x ∂torusMeasure 1,rearrange f x≠ (⊤ : ℝ≥0∞)) ∧
    (∀ᵐ x ∂torusMeasure 1,rearrange g x≠ (⊤ : ℝ≥0∞)) ∧
    Integrable (realRearrange f) (torusMeasure 1) ∧
    Integrable (realRearrange g) (torusMeasure 1) ∧
    IdentDistrib (realRearrange f) f (torusMeasure 1) (torusMeasure 1) ∧
    IdentDistrib (realRearrange g) g (torusMeasure 1) (torusMeasure 1) ∧
    (∀ x y : Torus 1,‖x 0‖≤‖y 0‖ → rearrange f y≤rearrange f x) ∧
    (∀ x y : Torus 1,‖x 0‖≤‖y 0‖ → rearrange g y≤rearrange g x) ∧
    interaction q f g ≤ interaction q (realRearrange f) (realRearrange g) ∧
    (∫ x,|realRearrange f x-realRearrange g x| ∂torusMeasure 1)≤
      ∫ x,|f x-g x| ∂torusMeasure 1 ∧
    ((∀ x,f x≤g x) → ∀ x,rearrange f x≤rearrange g x) := by
  sorry

end BecknerOnofri.Target

namespace BecknerOnofri.Target
open HighDim

theorem critical_adams_bound (d : ℕ) (hd : 0 < d) :
    ∃ B : ℝ, ∀ u : Torus d → ℝ, InCriticalSobolev u →
      logPartition u ≤ ((collapseCoefficient d * potentialEnergy u + B : ℝ) : EReal) := by
  sorry

theorem pressure_at_collapse_finite (d : ℕ) (hd : 0 < d) :
    0 ≤ pressure d (2 * (d : ℝ)) ∧ pressure d (2 * (d : ℝ)) < (⊤ : EReal) := by
  sorry

theorem coefficient_at_collapse_finite (d : ℕ) (hd : 0 < d) :
    0 ≤ coefficientDefect d (collapseCoefficient d) ∧
      coefficientDefect d (collapseCoefficient d) < (⊤ : EReal) := by
  sorry

end BecknerOnofri.Target

namespace BecknerOnofri.Target
open HighDim

theorem smooth_fourier_moments (d : ℕ) (u : Torus d → ℝ) (hu : SmoothOnTorus u) (m : ℕ) :
    Summable (fun k : Frequency d => (1+frequencyLength k)^m * ‖fourierCoeff u k‖) := by
  sorry

theorem smooth_sobolev_domain (d : ℕ) (u : Torus d → ℝ) (hu : SmoothOnTorus u) :
    (∀ s : ℝ, InSobolev s u) ∧ InCriticalSobolev u := by
  sorry

end BecknerOnofri.Target

/-! Local auxiliary assertions, including d=11. These do not replace the
remaining all-support branch classification or local-maximum assertions. -/
namespace BecknerOnofri.Target
open HighDim

theorem local_continuous_quartic_reduction (d : ℕ) (hd : 11 ≤ d) :
    LocalReductionStatement.GraphQuarticReduction d := by
  sorry

theorem local_fullmode_stationary_hessian (d : ℕ) (hd : 11 ≤ d) :
    LocalReductionStatement.FullModeStationaryBranch d := by
  sorry

theorem smooth_angular_power (d : ℕ) (u : Torus d → ℝ) (hu : SmoothOnTorus u) (s : ℝ) (hs : 0 ≤ s) :
    ∃ v : Torus d → ℝ, SmoothOnTorus v ∧ ∀ k : Frequency d,
      fourierCoeff v k = ((frequencyLength k^(2*s):ℝ):ℂ)*fourierCoeff u k := by
  sorry

end BecknerOnofri.Target

/-! Existence assertion from the local critical-branch proposition; the
exhaustiveness and Hessian sign assertions remain separate. -/
namespace BecknerOnofri.Target
theorem local_supported_stationary_branch (d : ℕ) (hd : 11≤d) (I : Finset (Fin d))
    (hI : I.Nonempty) : HighDim.LocalReductionStatement.SupportedStationaryBranch d I := by
  sorry
end BecknerOnofri.Target

namespace BecknerOnofri.Target
/-- Same analytic squared amplitude for all supports of size n, and actual PDE branch energies. -/
theorem local_supported_energy_family (d n : ℕ) (hd : 11≤d) (hn : 0<n) (hnd : n≤d) :
    HighDim.LocalReductionStatement.SupportedEnergyFamily d n := by
  sorry
end BecknerOnofri.Target

namespace BecknerOnofri.Target
open Filter HighDim
open scoped Topology
/-- The paper's equal-active-amplitude divisibility conclusion for actual Fourier Euler solutions. -/
theorem local_equal_active_fourier_modes (d : ℕ) (hd : 11≤d) :
    ∀ᶠ x : ℝ × HighDim.ContinuousGibbs.Space d in 𝓝 (1,0), MeanZero x.2 →
      (∀ k : HighDim.NonzeroFrequency d,
        ((HighDim.frequencyLength k.val^d:ℝ):ℂ)*fourierCoeff x.2 k.val =
          (x.1:ℂ)*fourierCoeff (normalizedGibbs x.2) k.val) →
      ∀ i j : Fin d,fourierCoeff x.2 (HighDim.axisFrequency i)≠0 →
        fourierCoeff x.2 (HighDim.axisFrequency j)≠0 →
        ‖fourierCoeff x.2 (HighDim.axisFrequency i)‖^2=
          ‖fourierCoeff x.2 (HighDim.axisFrequency j)‖^2 := by
  sorry
end BecknerOnofri.Target

namespace BecknerOnofri.Target
/-- The common analytic amplitude family, actual branch energies, and exhaustiveness of all small Euler solutions. Stability is stated separately. -/
theorem local_supported_classification (d : ℕ) (hd : 11≤d) :
    HighDim.LocalReductionStatement.SupportedClassification d := by
  sorry
end BecknerOnofri.Target

namespace BecknerOnofri.Target
open Filter HighDim
open scoped Topology
/-- Actual small nonzero Euler solutions with a missing first-shell coordinate have both signs of the physical Hessian. -/
theorem local_proper_support_saddle (d : ℕ) (hd : 11≤d) :
    ∀ᶠ x : ℝ × HighDim.ContinuousGibbs.Space d in 𝓝 (1,0),MeanZero x.2 →
      (∀ k : HighDim.NonzeroFrequency d,
        ((HighDim.frequencyLength k.val^d:ℝ):ℂ)*fourierCoeff x.2 k.val =
          (x.1:ℂ)*fourierCoeff (normalizedGibbs x.2) k.val) → x.2≠0 →
      (∃ j : Fin d,fourierCoeff x.2 (HighDim.axisFrequency j)=0) →
      ∃ v q : HighDim.ContinuousGibbs.Space d,
        InCriticalSobolev v ∧ MeanZero v ∧ InCriticalSobolev q ∧ MeanZero q ∧
        0<HighDim.secondVariation (x.1*HighDim.spectralThreshold d) x.2 v ∧
        HighDim.secondVariation (x.1*HighDim.spectralThreshold d) x.2 q<0 := by
  sorry
end BecknerOnofri.Target

namespace BecknerOnofri.Target
/-- The full-mode branch is genuinely locally maximal in every H^s topology above d/2, with the full physical Morse--Bott Hessian and uniform Sobolev profile. -/
theorem local_fullmode_morse_bott (d : ℕ) (hd : 11≤d) :
    HighDim.LocalReductionStatement.FullModeLocalBranch d := by
  sorry
end BecknerOnofri.Target

namespace BecknerOnofri.Target
/-- One common branch family: analytic amplitudes, exact support and physical energy, exhaustive raw H^s classification, proper-support saddles, full-mode Morse--Bott local maxima and strict energy ordering. -/
theorem local_stable_supported_classification (d : ℕ) (hd : 11≤d) :
    HighDim.LocalReductionStatement.StableSupportedClassification d := by
  sorry
end BecknerOnofri.Target

namespace BecknerOnofri.Target
/-- The actual quadratic complementary term, with its exact Fourier resolvent formula and both physical H^s cubic Taylor remainders for every fixed s. -/
theorem local_sobolev_quadratic_slaving (d : ℕ) (hd : 11≤d) :
    HighDim.LocalReductionStatement.SobolevQuadraticReduction d := by
  sorry
end BecknerOnofri.Target

namespace BecknerOnofri.Target
/-- One actual locally unique complement graph is analytic in every fixed physical Sobolev Hilbert norm, with exact Fourier identification and zero value and derivative at the base point. -/
theorem local_sobolev_analytic_graph (d : ℕ) (hd : 11≤d) :
    HighDim.LocalReductionStatement.SobolevAnalyticComplementGraph d := by
  sorry
end BecknerOnofri.Target

namespace BecknerOnofri.Target
/-- Actual reduced physical Hessian in active squared amplitudes: both eigenvalue expansions, negative signs, and exact multiplicities, on one locally unique complement graph and one analytic branch amplitude for every support size. -/
theorem local_active_squared_hessian (d : ℕ) (hd : 11≤d) :
    HighDim.LocalReductionStatement.ActiveSquaredHessian.Family d := by
  sorry
end BecknerOnofri.Target

namespace BecknerOnofri.Target
/-- Equimeasurable smooth Steiner--Gibbs selection for every prescribed finite-entropy subcritical minimizer. This auxiliary statement does not identify the output with the canonical finite successive coordinate rearrangements. -/
theorem prescribed_equimeasurable_selection (d : ℕ) (hd : 0 < d) :
    HighDim.PrescribedSelection.EquimeasurableSelection d := by
  sorry
end BecknerOnofri.Target

namespace BecknerOnofri.Target
/-- Finite successive canonical coordinate Steiner rearrangement of every prescribed full finite-entropy minimizer, including equimeasurability, Gibbs/Green identification, entropy and value preservation, cosine mixture, and nonnegative Fourier coefficients of both density and potential. -/
theorem prescribed_canonical_selection (d : ℕ) (hd : 0 < d) :
    HighDim.PrescribedSelection.CanonicalSelection d := by
  sorry
end BecknerOnofri.Target

namespace BecknerOnofri.Target
/-- Every smooth monotone mean-zero Euler pair has nonnegative actual mixed partials on the closed cosine cube and a normalized countable cosine mixture; no variational optimality assumption. -/
theorem smooth_monotone_euler_cosine (d : ℕ) (hd : 0 < d) :
    HighDim.SmoothEulerStatement.CosineRepresentation d := by
  sorry
end BecknerOnofri.Target

namespace BecknerOnofri.Target
theorem spatial_form_closability (m : ℕ) :
    Set.InjOn (fun v : Friedrichs.SpatialForm.EnergySpace => v.1) (Friedrichs.SpatialForm.formClosure m) := by
  sorry

theorem angular_closed_form_conjugation (m : ℕ) (hm : 0 < m) :
    Friedrichs.SpatialForm.AngularClosedFormConjugation m := by
  sorry

end BecknerOnofri.Target

namespace BecknerOnofri.Target
theorem spatial_jacobi_spectral_identification (m : ℕ) (hm : 0 < m) (f g : Friedrichs.SpatialForm.H) :
    Friedrichs.SpatialForm.operatorGraph m f g ↔ ∀ n,
      inner ℝ g (Legacy.BecknerOnofri.JacobiEigenfunctions.normalizedVector m n) =
        Legacy.BecknerOnofri.JacobiEigenfunctions.eigenvalue m n *
          inner ℝ f (Legacy.BecknerOnofri.JacobiEigenfunctions.normalizedVector m n) := by
  sorry

theorem spatial_jacobi_selfadjoint (m : ℕ) (hm : 0 < m) (h k : Friedrichs.SpatialForm.H) :
    Friedrichs.SpatialForm.operatorGraph m h k ↔
      ∀ f g : Friedrichs.SpatialForm.H, Friedrichs.SpatialForm.operatorGraph m f g →
        inner ℝ g h = inner ℝ f k := by
  sorry

end BecknerOnofri.Target

namespace BecknerOnofri.Target
/-- Actual mixed Dirichlet/periodic spatial form membership of sine-weighted tensor profiles, including simultaneous active boundary faces. -/
theorem mixed_tensor_spatial_form_domain (d : ℕ) :
    Friedrichs.MixedSpatial.TensorFormDomain d := by
  sorry
end BecknerOnofri.Target

namespace BecknerOnofri.Target
theorem mixed_tensor_spatial_operator (d : ℕ) :
    Friedrichs.MixedSpatial.TensorOperatorConjugation d := by
  sorry
end BecknerOnofri.Target

namespace BecknerOnofri.Target
theorem mixed_chebyshev_spatial_eigenvectors (d : ℕ) :
    Friedrichs.MixedSpatial.ChebyshevSpatialEigenvectors d := by
  sorry
end BecknerOnofri.Target

namespace BecknerOnofri.Target
theorem mixed_spatial_form_closability (d : ℕ) (α : Friedrichs.MixedSpatial.MultiIndex d) :
    Set.InjOn (fun v : Friedrichs.MixedSpatial.EnergySpace α => v.1) (Friedrichs.MixedSpatial.formClosure α) := by
  sorry
end BecknerOnofri.Target

namespace BecknerOnofri.Target
theorem mixed_spatial_operator_closed (d : ℕ) (α : Friedrichs.MixedSpatial.MultiIndex d) :
    IsClosed {p : Friedrichs.MixedSpatial.H α × Friedrichs.MixedSpatial.H α |
      Friedrichs.MixedSpatial.operatorGraph α p.1 p.2} := by
  sorry
end BecknerOnofri.Target

namespace BecknerOnofri.Target
/-- Every coordinate has positive multi-index a_i+1; this auxiliary theorem is restricted to the full Dirichlet case. -/
theorem active_spatial_spectral_identification (d : ℕ) (a : Friedrichs.MixedSpatial.MultiIndex d)
    (f g : Friedrichs.MixedSpatial.H (fun i => a i+1)) :
    Friedrichs.MixedSpatial.operatorGraph (fun i => a i+1) f g ↔
      ∀ n,inner ℝ g (Legacy.BecknerOnofri.JacobiTensor.tensorVector (fun i => a i+1) n)=
        Legacy.BecknerOnofri.JacobiTensor.tensorEigenvalue (fun i => a i+1) n*
          inner ℝ f (Legacy.BecknerOnofri.JacobiTensor.tensorVector (fun i => a i+1) n) := by
  sorry
end BecknerOnofri.Target

namespace BecknerOnofri.Target
/-- Every coordinate has positive multi-index a_i+1; this auxiliary theorem is restricted to the full Dirichlet case. -/
theorem active_spatial_selfadjoint (d : ℕ) (a : Friedrichs.MixedSpatial.MultiIndex d)
    (f g : Friedrichs.MixedSpatial.H (fun i => a i+1)) :
    Friedrichs.MixedSpatial.operatorGraph (fun i => a i+1) f g ↔
      ∀ u v : Friedrichs.MixedSpatial.H (fun i => a i+1),
        Friedrichs.MixedSpatial.operatorGraph (fun i => a i+1) u v →
          inner ℝ v f=inner ℝ u g := by
  sorry
end BecknerOnofri.Target

namespace BecknerOnofri.Target
theorem mixed_full_spatial_eigenvectors (d : ℕ) :
    Friedrichs.MixedSpatial.FullSpatialEigenvectors d := by
  sorry
end BecknerOnofri.Target

namespace BecknerOnofri.Target
theorem mixed_coordinate_spectral_totality  :
    Friedrichs.MixedSpatial.FullCoordinateTotality := by
  sorry
end BecknerOnofri.Target

namespace BecknerOnofri.Target
theorem periodic_full_hilbert_basis  :
    Friedrichs.MixedSpatial.FullPeriodicHilbertBasis := by
  sorry
end BecknerOnofri.Target

namespace BecknerOnofri.Target
theorem mixed_spatial_spectral_identification (d : ℕ) (α : Friedrichs.MixedSpatial.MultiIndex d)
    (f g : Friedrichs.MixedSpatial.H α) :
    Friedrichs.MixedSpatial.operatorGraph α f g ↔
      ∀ n,inner ℝ g (Friedrichs.MixedSpatial.basisTensorVector α n)=
        Friedrichs.MixedSpatial.mixedEigenvalue α n*
          inner ℝ f (Friedrichs.MixedSpatial.basisTensorVector α n) := by
  sorry
end BecknerOnofri.Target

namespace BecknerOnofri.Target
theorem mixed_spatial_selfadjoint (d : ℕ) (α : Friedrichs.MixedSpatial.MultiIndex d)
    (f g : Friedrichs.MixedSpatial.H α) :
    Friedrichs.MixedSpatial.operatorGraph α f g ↔
      ∀ u v : Friedrichs.MixedSpatial.H α,
        Friedrichs.MixedSpatial.operatorGraph α u v → inner ℝ v f=inner ℝ u g := by
  sorry
end BecknerOnofri.Target

namespace BecknerOnofri.Target
theorem fractional_intertwining (d : ℕ) :
    Friedrichs.MixedSpatial.FractionalIntertwining d := by
  sorry
end BecknerOnofri.Target
