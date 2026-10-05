module

public import Legacy.BecknerOnofri.CircleHeatLargeTime

@[expose] public section

/-! Real Gaussian derivative estimates used in the small-time circle heat proof. -/
noncomputable section
open Set MeasureTheory Legacy.TorusEndpoint
open scoped BigOperators
namespace Legacy.BecknerOnofri.CircleHeat
open CircleHeatDerivativeTail

def gaussianSlope (A y : ℝ) : ℝ := y*Real.exp (-A*y^2)

theorem hasDerivAt_gaussianSlope (A y : ℝ) :
    HasDerivAt (gaussianSlope A) (Real.exp (-A*y^2)*(1-2*A*y^2)) y := by
  have h := (hasDerivAt_id y).mul (((hasDerivAt_id y).pow 2).const_mul (-A)).exp
  convert! h using 1; dsimp [gaussianSlope]; ring

theorem gaussianSlope_antitone {A : ℝ} (hA : 12 ≤ A) :
    AntitoneOn (gaussianSlope A) (Ici (1/4:ℝ)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · intro y _; exact (hasDerivAt_gaussianSlope A y).continuousAt.continuousWithinAt
  · intro y _; exact (hasDerivAt_gaussianSlope A y).differentiableAt.differentiableWithinAt
  · intro y hy
    have hyq : 1/4 ≤ y := interior_subset hy
    rw [(hasDerivAt_gaussianSlope A y).deriv]
    apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _)
    have hy2 : (1/4:ℝ)^2 ≤ y^2 := sq_le_sq₀ (by norm_num) (by linarith) |>.mpr hyq
    nlinarith

theorem gaussianSlope_derivative_bound {A n x y : ℝ} (hA : 12 ≤ A) (hn : 1 ≤ n)
    (hx : x ∈ Icc (0:ℝ) (1/4)) (hy : y ∈ Icc (n-x) (n+x)) :
    ‖Real.exp (-A*y^2)*(1-2*A*y^2)‖ ≤
      2*A*(n+x)^2*Real.exp (-A*(n-x)^2) := by
  rcases hx with ⟨hx0,hx1⟩
  rcases hy with ⟨hy0,hy1⟩
  have hnmx : 0 ≤ n-x := by linarith
  have hypos : 0 ≤ y := by linarith
  have hsq0 : (n-x)^2 ≤ y^2 := (sq_le_sq₀ hnmx hypos).mpr hy0
  have hsq1 : y^2 ≤ (n+x)^2 := (sq_le_sq₀ hypos (by linarith)).mpr hy1
  have hsqy : (3/4:ℝ)^2 ≤ y^2 := (sq_le_sq₀ (by norm_num) hypos).mpr (by linarith)
  have hneg : 1-2*A*y^2 ≤ 0 := by nlinarith
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_nonpos hneg]
  have he := Real.exp_le_exp.mpr (show -A*y^2 ≤ -A*(n-x)^2 by nlinarith)
  have hp : 0 ≤ 2*A*y^2-1 := by linarith
  have hb : 2*A*y^2-1 ≤ 2*A*(n+x)^2 := by nlinarith
  have hm := mul_le_mul he hb hp (Real.exp_nonneg _)
  nlinarith only [hm]

theorem gaussianSlope_difference_bound {A n x : ℝ} (hA : 12 ≤ A) (hn : 1 ≤ n)
    (hx : x ∈ Icc (0:ℝ) (1/4)) :
    gaussianSlope A (n-x)-gaussianSlope A (n+x) ≤
      4*A*x*(n+x)^2*Real.exp (-A*(n-x)^2) := by
  have hh := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := gaussianSlope A) (f' := fun y => Real.exp (-A*y^2)*(1-2*A*y^2))
    (a := n-x) (b := n+x)
    (fun y _ => (hasDerivAt_gaussianSlope A y).hasDerivWithinAt)
    (fun y hy => gaussianSlope_derivative_bound hA hn hx (Ico_subset_Icc_self hy))
    (n+x) (by constructor <;> linarith [hx.1])
  rw [Real.norm_eq_abs] at hh
  have hab := neg_abs_le (gaussianSlope A (n+x)-gaussianSlope A (n-x))
  nlinarith only [hh, hab]

theorem gaussianSlope_difference_relative {A x : ℝ} (hA : 12 ≤ A)
    (hx : x ∈ Icc (0:ℝ) (1/4)) (m : ℕ) :
    gaussianSlope A ((m:ℝ)+1-x)-gaussianSlope A ((m:ℝ)+1+x) ≤
      (x*Real.exp (-A*x^2))*((25/4)*A*poissonTerm A m) := by
  let n : ℝ := (m:ℝ)+1
  have hn : 1 ≤ n := by dsimp [n]; linarith [Nat.cast_nonneg (α := ℝ) m]
  have hnx0 : 0 ≤ n+x := by linarith [hx.1]
  have hnx : n+x ≤ 5*n/4 := by linarith [hx.2]
  have hs : (n+x)^2 ≤ 25/16*n^2 := by nlinarith [sq_nonneg (5*n/4-(n+x))]
  have hsq : n^2/2 ≤ (n-x)^2-x^2 := by
    have hm := mul_nonneg (show 0 ≤ n by linarith) (show 0 ≤ n/2-2*x by linarith [hx.2])
    nlinarith only [hm]
  have he : Real.exp (-A*(n-x)^2) ≤ Real.exp (-A*x^2)*Real.exp (-A*n^2/2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hh := gaussianSlope_difference_bound hA hn hx
  have hp := mul_le_mul hs he (Real.exp_nonneg _) (by positivity : 0 ≤ 25/16*n^2)
  have hp' := mul_le_mul_of_nonneg_left hp (mul_nonneg (by linarith : 0 ≤ 4*A) hx.1)
  dsimp [poissonTerm]
  change gaussianSlope A (n-x)-gaussianSlope A (n+x) ≤ _
  nlinarith only [hh, hp']

#print axioms gaussianSlope_difference_relative
end Legacy.BecknerOnofri.CircleHeat
