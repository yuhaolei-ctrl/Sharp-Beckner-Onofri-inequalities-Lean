module

public import BecknerOnofri.LocalElevenCore.ActiveAmplitudeEquations
public import BecknerOnofri.AnalyticLinearFactorUnique

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.ActiveAmplitudeFactor
open ContinuousFirstShell AmplitudeLinearization RescaledReducedEquation ReducedEquation ContinuousSymmetry

def permuteInput {d : ℕ} (p : Equiv.Perm (Fin d)) :
    ℝ × Amplitudes d →L[ℝ] ℝ × Amplitudes d :=
  (ContinuousLinearMap.fst ℝ ℝ (Amplitudes d)).prod
    (ContinuousLinearMap.pi (fun i => coordinate d (p i)))

@[simp] theorem permuteInput_apply {d : ℕ} (p : Equiv.Perm (Fin d)) (x : ℝ × Amplitudes d) :
    permuteInput p x=(x.1,fun i => x.2 (p i)) := rfl

@[simp] theorem permuteInput_base {d : ℕ} (p : Equiv.Perm (Fin d)) :
    permuteInput p (1,0)=(1,0) := rfl

theorem permuteInput_tendsto {d : ℕ} (p : Equiv.Perm (Fin d)) :
    Tendsto (permuteInput p) (𝓝 ((1,0) : ℝ × Amplitudes d)) (𝓝 (1,0)) := by
  simpa only [permuteInput_base] using (permuteInput p).continuous.tendsto (1,0)

theorem scalar_permutation {d : ℕ} (hd : 11≤d) (p : Equiv.Perm (Fin d)) (i : Fin d) :
    ∀ᶠ x : ℝ × Amplitudes d in 𝓝 (1,0), scalar hd i (permuteInput p x)=scalar hd (p i) x := by
  filter_upwards [(realEmbedding_tendsto d).eventually (reduced_permutation hd)] with x hx
  exact congrArg Complex.re (congrFun (hx p) i)

theorem factor_permutation {d : ℕ} (hd : 11≤d) (p : Equiv.Perm (Fin d)) (i : Fin d) :
    ∀ᶠ x : ℝ × Amplitudes d in 𝓝 (1,0), factor hd i (permuteInput p x)=factor hd (p i) x := by
  have ha : AnalyticAt ℝ (fun x => factor hd i (permuteInput p x)) (1,0) := by
    have ho : AnalyticAt ℝ (factor hd i) (permuteInput p (1,0)) := by
      simpa only [permuteInput_base] using factor_analytic hd i
    exact ho.comp (f := permuteInput p) ((permuteInput p).analyticAt _)
  apply AnalyticParameterDivision.linear_factor_unique (coordinate d (p i))
    (e := (0,Pi.single (p i) 1)) (by simp) rfl ha (factor_analytic hd (p i))
  filter_upwards [(permuteInput_tendsto p).eventually (scalar_eq_coordinate_mul_factor hd i),
    scalar_eq_coordinate_mul_factor hd (p i),scalar_permutation hd p i] with x hp hi hs
  change x.2 (p i)*factor hd i (permuteInput p x)=x.2 (p i)*factor hd (p i) x
  exact hp.symm.trans (hs.trans hi)

#print axioms factor_permutation
end BecknerOnofri.HighDim.LocalEleven.ActiveAmplitudeFactor
