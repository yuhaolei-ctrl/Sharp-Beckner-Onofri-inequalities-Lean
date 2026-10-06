module

public import BecknerOnofri.LocalElevenCore.ActiveFactorPermutation

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.ActiveAmplitudeFactor
open ContinuousFirstShell AmplitudeLinearization RescaledReducedEquation ReducedEquation ContinuousSymmetry

def flipInput {d : ℕ} (j : Fin d) : ℝ × Amplitudes d →L[ℝ] ℝ × Amplitudes d :=
  (ContinuousLinearMap.fst ℝ ℝ (Amplitudes d)).prod
    (ContinuousLinearMap.pi (fun i => if i=j then -(coordinate d i) else coordinate d i))

@[simp] theorem flipInput_apply {d : ℕ} (j : Fin d) (x : ℝ × Amplitudes d) :
    flipInput j x=(x.1,fun i => if i=j then -x.2 i else x.2 i) := by
  apply Prod.ext
  · rfl
  · funext i
    simp only [flipInput,ContinuousLinearMap.prod_apply,ContinuousLinearMap.pi_apply]
    split_ifs <;> rfl

@[simp] theorem flipInput_base {d : ℕ} (j : Fin d) :
    flipInput j (1,0)=(1,0) := by
  rw [flipInput_apply]
  simp
  rfl

theorem flipInput_tendsto {d : ℕ} (j : Fin d) :
    Tendsto (flipInput j) (𝓝 ((1,0) : ℝ × Amplitudes d)) (𝓝 (1,0)) := by
  simpa only [flipInput_base] using (flipInput j).continuous.tendsto (1,0)

theorem realCoordinates_flip {d : ℕ} (j : Fin d) (x : ℝ × Amplitudes d) :
    realCoordinates d (flipInput j x).2=BecknerOnofri.HighDim.ContinuousSymmetry.phaseCoordinates (halfTranslation j) (realCoordinates d x.2) := by
  ext i
  rw [realCoordinates_apply,phase_halfTranslation,flipInput_apply]
  by_cases hij : i=j <;> simp [hij,realCoordinates_apply]

theorem scalar_flip {d : ℕ} (hd : 11≤d) (j i : Fin d) :
    ∀ᶠ x : ℝ × Amplitudes d in 𝓝 (1,0),
      scalar hd i (flipInput j x)=if i=j then -scalar hd i x else scalar hd i x := by
  filter_upwards [(realEmbedding_tendsto d).eventually (reduced_translation hd)] with x hx
  have h := congrArg Complex.re (congrFun (hx (halfTranslation j)) i)
  simp only [realEmbedding_apply,← realCoordinates_flip j x,phase_halfTranslation] at h
  by_cases hij : i=j <;> simpa [scalar,realEmbedding_apply,flipInput_apply,hij,Complex.neg_re] using h

theorem factor_flip {d : ℕ} (hd : 11≤d) (j i : Fin d) :
    ∀ᶠ x : ℝ × Amplitudes d in 𝓝 (1,0),factor hd i (flipInput j x)=factor hd i x := by
  have ha : AnalyticAt ℝ (fun x => factor hd i (flipInput j x)) (1,0) := by
    have ho : AnalyticAt ℝ (factor hd i) (flipInput j (1,0)) := by
      simpa only [flipInput_base] using factor_analytic hd i
    exact ho.comp (f := flipInput j) ((flipInput j).analyticAt _)
  apply AnalyticParameterDivision.linear_factor_unique (coordinate d i)
    (e := (0,Pi.single i 1)) (by simp) rfl ha (factor_analytic hd i)
  filter_upwards [(flipInput_tendsto j).eventually (scalar_eq_coordinate_mul_factor hd i),
    scalar_eq_coordinate_mul_factor hd i,scalar_flip hd j i] with x hp hi hs
  change x.2 i*factor hd i (flipInput j x)=x.2 i*factor hd i x
  rw [flipInput_apply]
  by_cases hij : i=j
  · simp only [flipInput_apply,if_pos hij] at hp hs
    rw [hi] at hs
    nlinarith [hp,hs]
  · simp only [flipInput_apply,if_neg hij] at hp hs
    exact hp.symm.trans (hs.trans hi)

#print axioms factor_flip
end BecknerOnofri.HighDim.LocalEleven.ActiveAmplitudeFactor
