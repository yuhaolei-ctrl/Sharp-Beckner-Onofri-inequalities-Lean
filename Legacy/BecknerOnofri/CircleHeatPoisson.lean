import Legacy.BecknerOnofri.CircleHeatPoissonAux

/-! Monotonicity of the genuine periodized Gaussian from finite sums and their limits. -/
noncomputable section
open Set Filter MeasureTheory Legacy.TorusEndpoint TorusHeatPositivity
open scoped BigOperators Topology
namespace Legacy.BecknerOnofri.CircleHeat
open CircleHeatDerivativeTail

def poissonSeries (A x : ℝ) : ℝ := ∑' n : ℤ, Real.exp (-A*((n:ℝ)-x)^2)
def symmetricGaussian (A : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-A*((m:ℝ)+1-x)^2)+Real.exp (-A*((m:ℝ)+1+x)^2)
def adjacentGaussian (A : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-A*((m:ℝ)+x)^2)+Real.exp (-A*((m:ℝ)+1-x)^2)
def finiteSymmetricGaussian (A : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-A*x^2)+∑ m ∈ Finset.range N, symmetricGaussian A m x

theorem summable_gaussian_nat_shift {A : ℝ} (hA : 0 < A) (x : ℝ) :
    Summable (fun m : ℕ => Real.exp (-A*((m:ℝ)+1-x)^2)) := by
  have hs := (shifted_gaussian_summable hA x).comp_injective
      (show Function.Injective (fun m : ℕ => (m:ℤ)+1) by intro a b hab; exact_mod_cast add_right_cancel hab)
  apply hs.congr
  intro m
  dsimp
  push_cast
  rfl

theorem summable_symmetricGaussian {A : ℝ} (hA : 0 < A) (x : ℝ) :
    Summable (fun m : ℕ => symmetricGaussian A m x) := by
  simpa only [symmetricGaussian, sub_neg_eq_add] using
    (summable_gaussian_nat_shift hA x).add (summable_gaussian_nat_shift hA (-x))

theorem poissonSeries_eq_symmetric {A : ℝ} (hA : 0 < A) (x : ℝ) :
    poissonSeries A x = Real.exp (-A*x^2)+∑' m : ℕ, symmetricGaussian A m x := by
  let f : ℤ → ℝ := fun n => Real.exp (-A*((n:ℝ)-x)^2)
  have hs1 : Summable (fun m : ℕ => f ((m:ℤ)+1)) := by
    simpa only [f, Int.cast_add, Int.cast_natCast, Int.cast_one] using summable_gaussian_nat_shift hA x
  have heq (m : ℕ) : f (-((m:ℤ)+1)) = Real.exp (-A*((m:ℝ)+1+x)^2) := by
    dsimp [f]
    push_cast
    congr 2
    ring
  have hs2 : Summable (fun m : ℕ => f (-((m:ℤ)+1))) := by
    simpa only [heq, sub_neg_eq_add] using summable_gaussian_nat_shift hA (-x)
  change (∑' n, f n) = _
  rw [tsum_of_add_one_of_neg_add_one hs1 hs2]
  have hz : f 0 = Real.exp (-A*x^2) := by simp [f]
  rw [hz]
  have hc := hs1.add hs2
  have ht := hs1.tsum_add hs2
  have ht' : (∑' m : ℕ, symmetricGaussian A m x) =
      (∑' m : ℕ, f ((m:ℤ)+1))+(∑' m : ℕ, f (-((m:ℤ)+1))) := by
    simpa only [symmetricGaussian, heq, f, Int.cast_add, Int.cast_natCast, Int.cast_one] using ht
  rw [ht']
  ring

theorem finiteSymmetricGaussian_tendsto {A : ℝ} (hA : 0 < A) (x : ℝ) :
    Tendsto (fun N => finiteSymmetricGaussian A N x) atTop (𝓝 (poissonSeries A x)) := by
  rw [poissonSeries_eq_symmetric hA x]
  exact tendsto_const_nhds.add (summable_symmetricGaussian hA x).hasSum.tendsto_sum_nat

theorem hasDerivAt_symmetricGaussian (A : ℝ) (m : ℕ) (x : ℝ) :
    HasDerivAt (symmetricGaussian A m)
      (2*A*(gaussianSlope A ((m:ℝ)+1-x)-gaussianSlope A ((m:ℝ)+1+x))) x := by
  have h1 := (((((hasDerivAt_id x).const_sub ((m:ℝ)+1)).pow 2).const_mul (-A)).exp)
  have h2 := (((((hasDerivAt_id x).const_add ((m:ℝ)+1)).pow 2).const_mul (-A)).exp)
  convert! h1.add h2 using 1; dsimp [symmetricGaussian, gaussianSlope]; ring

theorem hasDerivAt_finiteSymmetricGaussian (A : ℝ) (N : ℕ) (x : ℝ) :
    HasDerivAt (finiteSymmetricGaussian A N)
      (-2*A*gaussianSlope A x+2*A*∑ m ∈ Finset.range N,
        (gaussianSlope A ((m:ℝ)+1-x)-gaussianSlope A ((m:ℝ)+1+x))) x := by
  have hh := ((((hasDerivAt_id x).pow 2).const_mul (-A)).exp).add
    (HasDerivAt.fun_sum (fun m (_ : m ∈ Finset.range N) => hasDerivAt_symmetricGaussian A m x))
  convert! hh using 1
  rw [Finset.mul_sum]
  dsimp [gaussianSlope]
  ring

theorem finite_slope_sum_le {A x : ℝ} (hA : 12 ≤ A) (hx : x ∈ Icc (0:ℝ) (1/4)) (N : ℕ) :
    (∑ m ∈ Finset.range N, (gaussianSlope A ((m:ℝ)+1-x)-gaussianSlope A ((m:ℝ)+1+x))) ≤
      gaussianSlope A x := by
  have hsum := Finset.sum_le_sum (s := Finset.range N) (fun m _ => gaussianSlope_difference_relative hA hx m)
  simp only [← Finset.mul_sum] at hsum
  have hp := (summable_poissonTail hA).sum_le_tsum (Finset.range N) (fun m _ => by dsimp [poissonTerm]; positivity)
  have hscale := mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ (25/4)*A)
  change (25/4)*A*(∑ m ∈ Finset.range N, poissonTerm A m) ≤ (25/4)*A*poissonTail A at hscale
  have hbound := le_trans hscale (le_of_lt (poissonTail_scaled_lt_one hA))
  have hn : 0 ≤ x*Real.exp (-A*x^2) := mul_nonneg hx.1 (Real.exp_nonneg _)
  have hh := mul_le_mul_of_nonneg_left hbound hn
  change _ ≤ x*Real.exp (-A*x^2)
  nlinarith only [hsum, hh]

theorem finiteSymmetricGaussian_antitone {A : ℝ} (hA : 12 ≤ A) (N : ℕ) :
    AntitoneOn (finiteSymmetricGaussian A N) (Icc (0:ℝ) (1/4)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · intro x _; exact (hasDerivAt_finiteSymmetricGaussian A N x).continuousAt.continuousWithinAt
  · intro x _; exact (hasDerivAt_finiteSymmetricGaussian A N x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(hasDerivAt_finiteSymmetricGaussian A N x).deriv]
    have hh := finite_slope_sum_le hA (interior_subset hx) N
    nlinarith

theorem poissonSeries_antitone_near {A : ℝ} (hA : 12 ≤ A) :
    AntitoneOn (poissonSeries A) (Icc (0:ℝ) (1/4)) := by
  apply antitoneOn_of_frequently_antitoneOn_of_tendsto (l := atTop) (F := finiteSymmetricGaussian A)
    ((Filter.Eventually.of_forall (fun N => finiteSymmetricGaussian_antitone hA N)).frequently)
  intro x _
  exact finiteSymmetricGaussian_tendsto (by linarith) x

theorem adjacentGaussian_hasSum {A : ℝ} (hA : 0 < A) (x : ℝ) :
    HasSum (fun m : ℕ => adjacentGaussian A m x) (poissonSeries A x) := by
  let f : ℤ → ℝ := fun n => Real.exp (-A*((n:ℝ)-x)^2)
  have hs : Summable (fun n : ℤ => f (-n)) :=
    (shifted_gaussian_summable hA x).comp_injective (neg_injective : Function.Injective (Neg.neg : ℤ → ℤ))
  have he : (∑' n : ℤ, f (-n)) = poissonSeries A x := (Equiv.neg ℤ).tsum_eq f
  have hh := hs.hasSum.nat_add_neg_add_one
  rw [he] at hh
  convert! hh using 1
  funext m
  dsimp [adjacentGaussian, f]
  push_cast
  congr 1 <;> congr 2 <;> ring

theorem hasDerivAt_adjacentGaussian (A : ℝ) (m : ℕ) (x : ℝ) :
    HasDerivAt (adjacentGaussian A m)
      (-2*A*(gaussianSlope A ((m:ℝ)+x)-gaussianSlope A ((m:ℝ)+1-x))) x := by
  have h1 := (((((hasDerivAt_id x).const_add (m:ℝ)).pow 2).const_mul (-A)).exp)
  have h2 := (((((hasDerivAt_id x).const_sub ((m:ℝ)+1)).pow 2).const_mul (-A)).exp)
  convert! h1.add h2 using 1; dsimp [adjacentGaussian, gaussianSlope]; ring

theorem adjacentGaussian_antitone {A : ℝ} (hA : 12 ≤ A) (m : ℕ) :
    AntitoneOn (adjacentGaussian A m) (Icc (1/4:ℝ) (1/2)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · intro x _; exact (hasDerivAt_adjacentGaussian A m x).continuousAt.continuousWithinAt
  · intro x _; exact (hasDerivAt_adjacentGaussian A m x).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : x ∈ Icc (1/4:ℝ) (1/2) := interior_subset hx
    have hmono := gaussianSlope_antitone hA
      (show (m:ℝ)+x ∈ Ici (1/4:ℝ) by change 1/4 ≤ (m:ℝ)+x; linarith [Nat.cast_nonneg (α := ℝ) m, hx'.1])
      (show (m:ℝ)+1-x ∈ Ici (1/4:ℝ) by change 1/4 ≤ (m:ℝ)+1-x; linarith [Nat.cast_nonneg (α := ℝ) m, hx'.2])
      (show (m:ℝ)+x ≤ (m:ℝ)+1-x by linarith [hx'.2])
    rw [(hasDerivAt_adjacentGaussian A m x).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (sub_nonneg.mpr hmono)

theorem poissonSeries_antitone_far {A : ℝ} (hA : 12 ≤ A) :
    AntitoneOn (poissonSeries A) (Icc (1/4:ℝ) (1/2)) := by
  intro x hx y hy hxy
  rw [← (adjacentGaussian_hasSum (by linarith : 0 < A) x).tsum_eq,
    ← (adjacentGaussian_hasSum (by linarith : 0 < A) y).tsum_eq]
  exact Summable.tsum_le_tsum (fun m => adjacentGaussian_antitone hA m hx hy hxy)
    (adjacentGaussian_hasSum (by linarith) y).summable
    (adjacentGaussian_hasSum (by linarith) x).summable

theorem poissonSeries_antitone {A : ℝ} (hA : 12 ≤ A) :
    AntitoneOn (poissonSeries A) (Icc (0:ℝ) (1/2)) := by
  intro x hx y hy hxy
  by_cases hyq : y ≤ 1/4
  · exact poissonSeries_antitone_near hA ⟨hx.1, hxy.trans hyq⟩ ⟨hy.1, hyq⟩ hxy
  by_cases hxq : 1/4 ≤ x
  · exact poissonSeries_antitone_far hA ⟨hxq,hx.2⟩ ⟨hxq.trans hxy,hy.2⟩ hxy
  exact le_trans
    (poissonSeries_antitone_far hA (show (1/4:ℝ) ∈ Icc (1/4:ℝ) (1/2) by norm_num) ⟨by linarith,hy.2⟩ (by linarith))
    (poissonSeries_antitone_near hA ⟨hx.1,by linarith⟩ (show (1/4:ℝ) ∈ Icc (0:ℝ) (1/4) by norm_num) (by linarith))

theorem realHeat_antitone_small {t : ℝ} (ht : 0 < t) (htq : t ≤ 1/4) :
    AntitoneOn (realHeat t) (Icc (0:ℝ) (1/2)) := by
  have hA : 12 ≤ Real.pi/t := (le_div_iff₀ ht).mpr (by nlinarith [Real.pi_gt_three])
  intro x hx y hy hxy
  unfold realHeat
  rw [theta_coe_eq_shifted_gaussian ht, theta_coe_eq_shifted_gaussian ht, Complex.ofReal_re, Complex.ofReal_re]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [poissonSeries, neg_div] using poissonSeries_antitone hA hx hy hxy

theorem realHeat_antitone {t : ℝ} (ht : 0 < t) :
    AntitoneOn (realHeat t) (Icc (0:ℝ) (1/2)) := by
  by_cases htq : t ≤ 1/4
  · exact realHeat_antitone_small ht htq
  · exact realHeat_antitone_large (by linarith)

#print axioms realHeat_antitone
end Legacy.BecknerOnofri.CircleHeat
