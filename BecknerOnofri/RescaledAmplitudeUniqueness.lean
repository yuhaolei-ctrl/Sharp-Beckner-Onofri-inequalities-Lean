module

public import BecknerOnofri.RescaledReducedEquation
public import Mathlib.Analysis.Calculus.ImplicitContDiff

@[expose] public section

/-! Actual analytic full-amplitude implicit branch near the all-active limiting
point, and uniqueness of its real amplitudes by permutation symmetry. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology ContDiff BigOperators
namespace BecknerOnofri.HighDim.RescaledReducedEquation
open AmplitudeLinearization

/-- The genuine analytic implicit solution to the fully rescaled reduced equation. -/
theorem exists_amplitude_branch {d : ℕ} (hd : 12 ≤ d) :
    ∃ r : ℝ → Amplitudes d, AnalyticAt ℝ r 0 ∧ r 0=(fun _ => 1) ∧
      (∀ᶠ t in 𝓝 (0:ℝ), extension hd (r t,t)=0) ∧
      (∀ᶠ x in 𝓝 ((fun _ : Fin d => (1:ℝ)),(0:ℝ)),
        extension hd x=0 ↔ r x.2=x.1) := by
  let f : ℝ × Amplitudes d → Amplitudes d := fun x => extension hd (x.2,x.1)
  let o : Amplitudes d := fun _ => 1
  have hf : AnalyticAt ℝ f (0,o) := by
    have hi : AnalyticAt ℝ (fun x : ℝ × Amplitudes d => (x.2,x.1)) (0,o) :=
      analyticAt_snd.prod analyticAt_fst
    exact (extension_analytic hd).comp (f := fun x : ℝ × Amplitudes d => (x.2,x.1)) hi
  have hf0 : f (0,o)=0 := extension_base hd
  have hslice : HasFDerivAt (𝕜 := ℝ) (fun r : Amplitudes d => f (0,r)) (jacobian d) o :=
    (limitingEquation_hasFDerivAt d).congr_of_eventuallyEq (extension_axis hd)
  have hp : (fderiv ℝ f (0,o)).comp (ContinuousLinearMap.inr ℝ ℝ (Amplitudes d)) = jacobian d :=
    ((hf.differentiableAt.hasFDerivAt).comp o
      ((ContinuousLinearMap.inr ℝ ℝ (Amplitudes d)).hasFDerivAt)).unique hslice
  have hi : ((fderiv ℝ f (0,o)).comp (ContinuousLinearMap.inr ℝ ℝ (Amplitudes d))).IsInvertible := by
    rw [hp]
    exact ContinuousLinearMap.isInvertible_equiv (f := jacobianEquiv hd)
  have hc : ContDiffAt ℝ ω f (0,o) := hf.contDiffAt
  have hn : (ω : ℕ∞ω)≠0 := by simp
  let r := hc.implicitFunction hn hi
  refine ⟨r,(hc.contDiffAt_implicitFunction hn hi).analyticAt,
    hc.implicitFunction_apply_self hn hi,?_,?_⟩
  · simpa only [hf0] using hc.eventually_apply_implicitFunction hn hi
  · have ht : Tendsto (fun x : Amplitudes d × ℝ => (x.2,x.1))
        (𝓝 (o,(0:ℝ))) (𝓝 ((0:ℝ),o)) := (continuous_snd.prodMk continuous_fst).continuousAt
    simpa only [hf0] using ht.eventually (hc.eventually_apply_eq_iff_implicitFunction hn hi)

def amplitudeBranch {d : ℕ} (hd : 12 ≤ d) : ℝ → Amplitudes d :=
  (exists_amplitude_branch hd).choose

theorem amplitudeBranch_analytic {d : ℕ} (hd : 12 ≤ d) :
    AnalyticAt ℝ (amplitudeBranch hd) 0 := (exists_amplitude_branch hd).choose_spec.1

@[simp] theorem amplitudeBranch_base {d : ℕ} (hd : 12 ≤ d) :
    amplitudeBranch hd 0=(fun _ => 1) := (exists_amplitude_branch hd).choose_spec.2.1

theorem amplitudeBranch_solves {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ t in 𝓝 (0:ℝ), extension hd (amplitudeBranch hd t,t)=0 :=
  (exists_amplitude_branch hd).choose_spec.2.2.1

theorem amplitudeBranch_unique {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ x in 𝓝 ((fun _ : Fin d => (1:ℝ)),(0:ℝ)),
      extension hd x=0 ↔ amplitudeBranch hd x.2=x.1 :=
  (exists_amplitude_branch hd).choose_spec.2.2.2

theorem amplitudeBranch_pair_tendsto {d : ℕ} (hd : 12 ≤ d) :
    Tendsto (fun t : ℝ => (amplitudeBranch hd t,t)) (𝓝 0)
      (𝓝 ((fun _ : Fin d => (1:ℝ)),(0:ℝ))) := by
  have ht : Tendsto (amplitudeBranch hd) (𝓝 0) (𝓝 (fun _ => 1)) := by
    simpa only [amplitudeBranch_base] using (amplitudeBranch_analytic hd).continuousAt.tendsto
  exact ht.prodMk_nhds tendsto_id

/-- Local uniqueness and actual coordinate-permutation symmetry force every
entry of the all-active real-amplitude branch to be identical. -/
theorem amplitudeBranch_permutation {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ t in 𝓝 (0:ℝ), ∀ σ : Equiv.Perm (Fin d),
      (fun i => amplitudeBranch hd t (σ i))=amplitudeBranch hd t := by
  apply Filter.eventually_all.mpr
  intro σ
  have ht : Tendsto (fun t : ℝ => ((fun i => amplitudeBranch hd t (σ i)),t)) (𝓝 0)
      (𝓝 ((fun _ : Fin d => (1:ℝ)),(0:ℝ))) := by
    have hc : Continuous (fun x : Amplitudes d × ℝ => ((fun i => x.1 (σ i)),x.2)) :=
      (continuous_pi (fun i => (continuous_apply (σ i)).comp continuous_fst)).prodMk continuous_snd
    exact (hc.continuousAt.tendsto (x := ((fun _ => 1),(0:ℝ)))).comp (amplitudeBranch_pair_tendsto hd)
  have hinput := (rescaleInput_tendsto d).comp (amplitudeBranch_pair_tendsto hd)
  filter_upwards [amplitudeBranch_solves hd,
    (amplitudeBranch_pair_tendsto hd).eventually (reduced_zero_iff_extension hd),
    ht.eventually (reduced_zero_iff_extension hd),ht.eventually (amplitudeBranch_unique hd),
    hinput.eventually (ContinuousSymmetry.reduced_permutation hd)] with t hs hz hpz hu hp
  by_cases ht0 : t=0
  · simp only [ht0,amplitudeBranch_base]
  · have hR : ReducedEquation.reduced hd (rescaleInput d (amplitudeBranch hd t,t))=0 :=
      (hz ht0).mpr hs
    have hperm : ReducedEquation.reduced hd
        (rescaleInput d ((fun i => amplitudeBranch hd t (σ i)),t)) =
        ContinuousSymmetry.permuteCoordinates σ
          (ReducedEquation.reduced hd (rescaleInput d (amplitudeBranch hd t,t))) := by
      exact hp σ
    have hRP : ReducedEquation.reduced hd
        (rescaleInput d ((fun i => amplitudeBranch hd t (σ i)),t))=0 := by
      rw [hperm,hR]
      rfl
    exact (hu.mp ((hpz ht0).mp hRP)).symm

theorem amplitudeBranch_equal_coordinates {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ t in 𝓝 (0:ℝ), ∀ i j : Fin d, amplitudeBranch hd t i=amplitudeBranch hd t j := by
  filter_upwards [amplitudeBranch_permutation hd] with t ht
  intro i j
  have h := congrFun (ht (Equiv.swap i j)) i
  simpa only [Equiv.swap_apply_left] using h.symm

/-- Any actual nonzero rescaled reduced zero near the all-active limiting
point has equal real amplitudes in every coordinate. -/
theorem reduced_zero_equal_amplitudes {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ x in 𝓝 ((fun _ : Fin d => (1:ℝ)),(0:ℝ)), x.2≠0 →
      ReducedEquation.reduced hd (rescaleInput d x)=0 → ∀ i j : Fin d, x.1 i=x.1 j := by
  have ht : Tendsto (Prod.snd : Amplitudes d × ℝ → ℝ)
      (𝓝 ((fun _ : Fin d => (1:ℝ)),(0:ℝ))) (𝓝 0) := continuous_snd.continuousAt
  filter_upwards [reduced_zero_iff_extension hd,amplitudeBranch_unique hd,
    ht.eventually (amplitudeBranch_equal_coordinates hd)] with x hz hu he
  intro ht0 hR
  have hr := hu.mp ((hz ht0).mp hR)
  simpa only [hr] using he

#print axioms amplitudeBranch_equal_coordinates
#print axioms reduced_zero_equal_amplitudes
#print axioms exists_amplitude_branch
end BecknerOnofri.HighDim.RescaledReducedEquation
