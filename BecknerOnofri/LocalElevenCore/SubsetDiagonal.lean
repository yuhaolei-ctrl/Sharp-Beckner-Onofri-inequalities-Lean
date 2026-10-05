import BecknerOnofri.LocalElevenCore.RealDiagonalReduction
import BecknerOnofri.LocalElevenCore.FirstShellOrbits

/-! Equal-amplitude directions for every nonempty coordinate support. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.LocalEleven.SubsetDiagonal
open ContinuousFirstShell ContinuousSymmetry ReducedEquation ReducedCubicExpansion

def line {d : ℕ} (I : Finset (Fin d)) : ℝ →L[ℝ] Coordinates d :=
  ContinuousLinearMap.pi (fun j => if j∈I then Complex.ofRealCLM else 0)

@[simp] theorem line_apply {d : ℕ} (I : Finset (Fin d)) (t : ℝ) (j : Fin d) :
    line I t j = if j∈I then (t:ℂ) else 0 := by
  simp only [line,ContinuousLinearMap.pi_apply]
  split_ifs <;> rfl

def embedding {d : ℕ} (I : Finset (Fin d)) : ℝ × ℝ →L[ℝ] ℝ × Coordinates d :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).prod ((line I).comp (ContinuousLinearMap.snd ℝ ℝ ℝ))

@[simp] theorem embedding_apply {d : ℕ} (I : Finset (Fin d)) (x : ℝ × ℝ) :
    embedding I x=(x.1,line I x.2) := rfl

theorem embedding_tendsto {d : ℕ} (I : Finset (Fin d)) :
    Tendsto (embedding I) (𝓝 (1,0)) (𝓝 (1,(0 : Coordinates d))) := by
  simpa only [embedding_apply,map_zero] using
    (embedding I).continuous.continuousAt.tendsto (x := ((1,0):ℝ×ℝ))

theorem permutation_line_swap {d : ℕ} {I : Finset (Fin d)} {i j : Fin d}
    (hi : i∈I) (hj : j∈I) (t : ℝ) :
    permuteCoordinates (Equiv.swap i j) (line I t)=line I t := by
  ext k
  change line I t (Equiv.swap i j k)=line I t k
  by_cases hki : k=i
  · subst k; simp [hi,hj]
  by_cases hkj : k=j
  · subst k; simp [hi,hj]
  rw [Equiv.swap_apply_of_ne_of_ne hki hkj]

@[simp] theorem conjugate_line {d : ℕ} (I : Finset (Fin d)) (t : ℝ) :
    conjugateCoordinates (line I t)=line I t := by
  ext i
  simp only [conjugateCoordinates_apply,line_apply]
  split_ifs <;> simp

def residual {d : ℕ} (hd : 11≤d) (I : Finset (Fin d)) (j : Fin d) (x : ℝ × ℝ) : ℝ :=
  (reduced hd (embedding I x) j).re

theorem residual_analytic {d : ℕ} (hd : 11≤d) (I : Finset (Fin d)) (j : Fin d) :
    AnalyticAt ℝ (residual hd I j) (1,0) := by
  have ho : AnalyticAt ℝ (reduced hd) (embedding I (1,0)) := by
    simpa only [embedding_apply,map_zero] using reduced_analytic hd
  let ev : Coordinates d →L[ℝ] ℝ := Complex.reCLM.comp (ContinuousLinearMap.proj j)
  exact (ev.analyticAt _).comp (ho.comp ((embedding I).analyticAt (1,0)))

/-- On a supported real diagonal, the whole genuine reduced equation is one scalar equation. -/
theorem reduced_line {d : ℕ} (hd : 11≤d) (I : Finset (Fin d)) (j : Fin d) (hj : j∈I) :
    ∀ᶠ x : ℝ × ℝ in 𝓝 (1,0),
      reduced hd (embedding I x)=line I (residual hd I j x) := by
  filter_upwards [(embedding_tendsto I).eventually (reduced_permutation hd),
    (embedding_tendsto I).eventually (reduced_reflection hd),
    (embedding_tendsto I).eventually (reduced_zero_on_inactive hd)] with x hp hr hz
  ext i
  by_cases hi : i∈I
  · have he : reduced hd (embedding I x) i=reduced hd (embedding I x) j := by
      have h := hp (Equiv.swap i j)
      simp only [embedding_apply,permutation_line_swap hi hj] at h
      simpa only [embedding_apply,permuteCoordinates,Equiv.swap_apply_left] using congrFun h i
    have him : (reduced hd (embedding I x) i).im=0 := by
      simp only [embedding_apply,conjugate_line] at hr
      have h := congrArg Complex.im (congrFun hr i)
      simp only [conjugateCoordinates_apply,Complex.conj_im] at h
      change (reduced hd (x.1,line I x.2) i).im=0
      linarith
    rw [line_apply,if_pos hi]
    apply Complex.ext
    · change (reduced hd (embedding I x) i).re = (reduced hd (embedding I x) j).re
      exact congrArg Complex.re he
    · simpa only [Complex.ofReal_im] using him
  · rw [line_apply,if_neg hi]
    exact hz i (by simp [hi])

def coefficient {d : ℕ} (I : Finset (Fin d)) : ℝ :=
  -(2*quarticA d+quarticB d*((I.card:ℝ)-1))

theorem coefficient_pos {d : ℕ} (hd : 11≤d) (I : Finset (Fin d)) (hI : I.Nonempty) :
    0<coefficient I := by
  have hcard : 0<I.card := Finset.card_pos.mpr hI
  have hle : I.card≤d := by simpa using Finset.card_le_card (Finset.subset_univ I)
  have h := BecknerOnofri.HighDim.LocalQuartic.coefficient_negative hd hcard hle
  have hc : (0:ℝ)<I.card := Nat.cast_pos.mpr hcard
  unfold branchQuarticCoefficient at h
  have hn := (div_lt_iff₀ hc).mp h
  unfold coefficient
  nlinarith

#print axioms reduced_line
#print axioms coefficient_pos
end BecknerOnofri.HighDim.LocalEleven.SubsetDiagonal
