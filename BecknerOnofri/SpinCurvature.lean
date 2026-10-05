module

public import BecknerOnofri.SpinNormEstimate

@[expose] public section

/-! Lemma 5.18 of the 2026-09-21 manuscript: global fixed-mean and
unrestricted-mean curvature bounds on the actual thirteen-state domain. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin

theorem curvature_cauchy (y a S : ℝ) (hS : y^2+4096*a^2≤S) :
    (Real.sqrt (7/8)*y+(35/11)*a)^2≤(434889/495616)*S := by
  have hs : Real.sqrt (7/8)^2=(7/8:ℝ) := Real.sq_sqrt (by norm_num)
  have he : (434889/495616)*(y^2+4096*a^2)-
      (Real.sqrt (7/8)*y+(35/11)*a)^2=
      (64*Real.sqrt (7/8)*a-(35/704)*y)^2 := by
    ring_nf
    rw [hs]
    ring
  have hh := sq_nonneg (64*Real.sqrt (7/8)*a-(35/704)*y)
  rw [← he] at hh
  linarith

theorem curvature_young (U b S : ℝ) (hU : U^2≤(434889/495616)*S) :
    (U+(56/11)*b)^2≤(19/20)*S+350*b^2 := by
  have hsq := mul_nonneg
    (by norm_num : (0:ℝ)≤((19/20)-(434889/495616))/(434889/495616))
    (sq_nonneg (U-(56/11)*(434889/495616)/((19/20)-(434889/495616))*b))
  norm_num at hsq
  nlinarith [sq_nonneg b]

/-- Fixed mean, exactly the first inequality of Lemma 5.18. -/
theorem fixed_mean_curvature {p q : Count → ℝ}
    (hp : Feasible p) (hpos : ∀ j,0<p j)
    (hmass : (∑ j : Count,q j)=0) (hmean : mean q=0) :
    quadratic q≤(9/10)*(∑ j : Count,q j^2/p j) := by
  let y := ∑ j ∈ Finset.univ.erase (0:Count),|q j|
  let S := ∑ j : Count,q j^2/p j
  have hy : 0≤y := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hS : 0≤S := Finset.sum_nonneg (fun j _ => div_nonneg (sq_nonneg _) (hpos j).le)
  have hc := curvature_cauchy y |q 0| S (curvature_denominator_lower hp hpos)
  have hn := corrected_seminorm_bound q hmass
  rw [hmean,abs_zero,mul_zero,add_zero] at hn
  have hu : 0≤Real.sqrt (7/8)*y+(35/11)*|q 0| := by positivity
  have hsq := (sq_le_sq₀ (Real.sqrt_nonneg (quadratic q)) hu).mpr hn
  rw [Real.sq_sqrt (quadratic_nonneg q)] at hsq
  change quadratic q≤(9/10)*S
  linarith

/-- Arbitrary mean, exactly the second inequality of Lemma 5.18. -/
theorem all_mean_curvature {p q : Count → ℝ}
    (hp : Feasible p) (hpos : ∀ j,0<p j)
    (hmass : (∑ j : Count,q j)=0) :
    quadratic q≤(19/20)*(∑ j : Count,q j^2/p j)+350*(mean q)^2 := by
  let y := ∑ j ∈ Finset.univ.erase (0:Count),|q j|
  let S := ∑ j : Count,q j^2/p j
  have hy : 0≤y := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hc := curvature_cauchy y |q 0| S (curvature_denominator_lower hp hpos)
  have hY := curvature_young (Real.sqrt (7/8)*y+(35/11)*|q 0|) |mean q| S hc
  have hn := corrected_seminorm_bound q hmass
  have hu : 0≤Real.sqrt (7/8)*y+(35/11)*|q 0|+(56/11)*|mean q| := by positivity
  have hsq := (sq_le_sq₀ (Real.sqrt_nonneg (quadratic q)) hu).mpr hn
  rw [Real.sq_sqrt (quadratic_nonneg q)] at hsq
  rw [sq_abs] at hY
  exact hsq.trans hY

#print axioms fixed_mean_curvature
#print axioms all_mean_curvature
end BecknerOnofri.HighDim.Spin
