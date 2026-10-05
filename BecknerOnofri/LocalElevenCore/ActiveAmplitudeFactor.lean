module

public import BecknerOnofri.AnalyticLinearFactor
public import BecknerOnofri.LocalElevenCore.RescaledReducedEquation
public import BecknerOnofri.LocalElevenCore.FirstShellOrbits

@[expose] public section

/-! Actual analytic coordinate factors of the real reduced Euler equation.
No division by a possibly zero amplitude occurs in their definitions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.ActiveAmplitudeFactor
open ContinuousFirstShell AmplitudeLinearization RescaledReducedEquation ReducedEquation

def realEmbedding (d : ℕ) : ℝ × Amplitudes d →L[ℝ] ℝ × Coordinates d :=
  (ContinuousLinearMap.fst ℝ ℝ (Amplitudes d)).prod
    ((realCoordinates d).comp (ContinuousLinearMap.snd ℝ ℝ (Amplitudes d)))

@[simp] theorem realEmbedding_apply (d : ℕ) (x : ℝ × Amplitudes d) :
    realEmbedding d x=(x.1,realCoordinates d x.2) := rfl

theorem realEmbedding_tendsto (d : ℕ) :
    Tendsto (realEmbedding d) (𝓝 (1,0)) (𝓝 (1,(0 : Coordinates d))) := by
  simpa only [realEmbedding_apply,map_zero] using
    (realEmbedding d).continuous.tendsto ((1,0) : ℝ × Amplitudes d)

def scalar {d : ℕ} (hd : 11≤d) (i : Fin d) (x : ℝ × Amplitudes d) : ℝ :=
  (reduced hd (realEmbedding d x) i).re

def coordinate (d : ℕ) (i : Fin d) : ℝ × Amplitudes d →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ ℝ (Amplitudes d))

@[simp] theorem coordinate_apply (d : ℕ) (i : Fin d) (x : ℝ × Amplitudes d) :
    coordinate d i x=x.2 i := rfl

theorem scalar_analytic {d : ℕ} (hd : 11≤d) (i : Fin d) :
    AnalyticAt ℝ (scalar hd i) (1,0) := by
  have ho : AnalyticAt ℝ (reduced hd) (realEmbedding d (1,0)) := by
    simpa only [realEmbedding_apply,map_zero] using reduced_analytic hd
  let ev : Coordinates d →L[ℝ] ℝ := Complex.reCLM.comp (ContinuousLinearMap.proj i)
  exact (ev.analyticAt _).comp (f := fun x => reduced hd (realEmbedding d x))
    (ho.comp (f := realEmbedding d) ((realEmbedding d).analyticAt _))

theorem scalar_inactive {d : ℕ} (hd : 11≤d) (i : Fin d) :
    ∀ᶠ x : ℝ × Amplitudes d in 𝓝 (1,0),x.2 i=0 → scalar hd i x=0 := by
  filter_upwards [(realEmbedding_tendsto d).eventually
    (ContinuousSymmetry.reduced_zero_on_inactive hd)] with x hx hi
  have h := hx i (by simp only [realEmbedding_apply,realCoordinates_apply,hi,Complex.ofReal_zero])
  exact congrArg Complex.re h

theorem exists_analytic_coordinate_factor {d : ℕ} (hd : 11≤d) (i : Fin d) :
    ∃ G : ℝ × Amplitudes d → ℝ, AnalyticAt ℝ G (1,0) ∧
      ∀ᶠ x : ℝ × Amplitudes d in 𝓝 (1,0),scalar hd i x=x.2 i*G x := by
  apply AnalyticParameterDivision.exists_analytic_linear_factor (coordinate d i)
    (e := (0,Pi.single i 1))
  · simp [coordinate_apply]
  · rfl
  · exact scalar_analytic hd i
  · exact scalar_inactive hd i

def factor {d : ℕ} (hd : 11≤d) (i : Fin d) : ℝ × Amplitudes d → ℝ :=
  (exists_analytic_coordinate_factor hd i).choose

theorem factor_analytic {d : ℕ} (hd : 11≤d) (i : Fin d) :
    AnalyticAt ℝ (factor hd i) (1,0) :=
  (exists_analytic_coordinate_factor hd i).choose_spec.1

theorem scalar_eq_coordinate_mul_factor {d : ℕ} (hd : 11≤d) (i : Fin d) :
    ∀ᶠ x : ℝ × Amplitudes d in 𝓝 (1,0),scalar hd i x=x.2 i*factor hd i x :=
  (exists_analytic_coordinate_factor hd i).choose_spec.2

#print axioms scalar_eq_coordinate_mul_factor
end BecknerOnofri.HighDim.LocalEleven.ActiveAmplitudeFactor
