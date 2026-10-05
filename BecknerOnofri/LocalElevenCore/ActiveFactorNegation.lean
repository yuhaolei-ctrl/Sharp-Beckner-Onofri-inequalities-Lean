module

public import BecknerOnofri.LocalElevenCore.ActiveFactorDifferential
public import BecknerOnofri.AnalyticProductFactorUnique

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.ActiveAmplitudeFactor
open ContinuousFirstShell AmplitudeLinearization RescaledReducedEquation ReducedEquation

def negateInput (d : ℕ) : Input d →L[ℝ] Input d :=
  (ContinuousLinearMap.fst ℝ ℝ (Amplitudes d)).prod
    (-ContinuousLinearMap.snd ℝ ℝ (Amplitudes d))

@[simp] theorem negateInput_apply {d : ℕ} (x : Input d) : negateInput d x=(x.1,-x.2) := rfl
@[simp] theorem negateInput_base (d : ℕ) : negateInput d (1,0)=(1,0) := by simp

theorem negateInput_tendsto (d : ℕ) :
    Tendsto (negateInput d) (𝓝 (1,0)) (𝓝 (1,0)) := by
  simpa only [negateInput_base] using (negateInput d).continuous.tendsto (1,0)

theorem scalar_negation {d : ℕ} (hd : 11≤d) (i : Fin d) :
    ∀ᶠ x : Input d in 𝓝 (1,0),scalar hd i (negateInput d x) = -scalar hd i x := by
  filter_upwards [(realEmbedding_tendsto d).eventually (ContinuousSymmetry.reduced_neg hd)] with x hx
  have h := congrArg (fun z : Coordinates d => (z i).re) hx
  simpa only [scalar,realEmbedding_apply,negateInput_apply,map_neg,Pi.neg_apply,Complex.neg_re] using h

theorem factor_negation {d : ℕ} (hd : 11≤d) (i : Fin d) :
    ∀ᶠ x : Input d in 𝓝 (1,0),factor hd i (negateInput d x)=factor hd i x := by
  have ha : AnalyticAt ℝ (fun x => factor hd i (negateInput d x)) (1,0) := by
    have ho : AnalyticAt ℝ (factor hd i) (negateInput d (1,0)) := by
      simpa only [negateInput_base] using factor_analytic hd i
    exact ho.comp (f := negateInput d) ((negateInput d).analyticAt _)
  apply AnalyticParameterDivision.linear_factor_unique (coordinate d i)
    (e := (0,Pi.single i 1)) (by simp) rfl ha (factor_analytic hd i)
  filter_upwards [(negateInput_tendsto d).eventually (scalar_eq_coordinate_mul_factor hd i),
    scalar_eq_coordinate_mul_factor hd i,scalar_negation hd i] with x hp hi hs
  change x.2 i*factor hd i (negateInput d x)=x.2 i*factor hd i x
  change scalar hd i (negateInput d x)=(-x.2 i)*factor hd i (negateInput d x) at hp
  rw [hi] at hs
  linarith

/-- The analytic divided difference inherits evenness of the actual factors. -/
theorem squared_difference_factor_negation {d : ℕ} (hd : 11≤d) (i j : Fin d) (hij : i≠j)
    {H : Input d → ℝ} (hH : AnalyticAt ℝ H (1,0))
    (he : ∀ᶠ x : Input d in 𝓝 (1,0),
      factor hd i x-factor hd j x=(x.2 i^2-x.2 j^2)*H x) :
    ∀ᶠ x : Input d in 𝓝 (1,0), H (negateInput d x)=H x := by
  have hn : AnalyticAt ℝ (fun x => H (negateInput d x)) (1,0) := by
    have ho : AnalyticAt ℝ H (negateInput d (1,0)) := by simpa only [negateInput_base] using hH
    exact ho.comp (f := negateInput d) ((negateInput d).analyticAt _)
  apply AnalyticParameterDivision.two_linear_factors_unique
    (coordinate d i-coordinate d j) (coordinate d i+coordinate d j)
    (e₁ := (0,Pi.single i 1)) (e₂ := (0,Pi.single i 1))
    (by simp [hij.symm]) (by simp [hij.symm]) (by simp) (by simp) hn hH
  filter_upwards [he,(negateInput_tendsto d).eventually he,
    factor_negation hd i,factor_negation hd j] with x hx hn hi hj
  simp only [negateInput_apply,Pi.neg_apply,neg_sq] at hn hi hj ⊢
  rw [hi,hj] at hn
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,coordinate_apply]
  nlinarith [hx,hn]

#print axioms squared_difference_factor_negation
end BecknerOnofri.HighDim.LocalEleven.ActiveAmplitudeFactor
