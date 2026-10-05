module

public import BecknerOnofri.CirclePoissonKernel

@[expose] public section

/-! Normalization of the actual Poisson kernel and preservation of pointwise
bounds under convolution. All integrals use normalized Haar measure. -/
noncomputable section
open MeasureTheory
namespace BecknerOnofri.HighDim.CirclePoisson

theorem cosine_integral (n : ℕ) :
    (∫ x : UnitAddCircle,(fourier (n:ℤ) x).re ∂AddCircle.haarAddCircle)=
      if n=0 then 1 else 0 := by
  by_cases hn : n=0
  · simp [hn]
  · rw [if_neg hn]
    apply integral_eq_zero_of_add_right_eq_neg (μ:=AddCircle.haarAddCircle)
    intro x
    have h := fourier_add_half_inv_index (n:=(n:ℤ)) (by exact_mod_cast hn)
      (by norm_num : (0:ℝ)<1) x
    simpa only [Complex.neg_re] using congrArg Complex.re h

theorem kernel_mass (q : ℝ) (hq : 0≤q) (hq1 : q<1) :
    (∫ x : UnitAddCircle,kernel q x ∂AddCircle.haarAddCircle)=1 := by
  let F : ℕ → UnitAddCircle → ℝ := fun n x => q^n*(fourier (n:ℤ) x).re
  have hi (n : ℕ) : Integrable (F n) AddCircle.haarAddCircle := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    dsimp only [F]
    fun_prop
  have hn (n : ℕ) : (∫ x,‖F n x‖ ∂AddCircle.haarAddCircle)≤q^n := by
    calc
      _ ≤ ∫ _ : UnitAddCircle,q^n ∂AddCircle.haarAddCircle := by
        apply integral_mono (hi n).norm (integrable_const _)
        intro x
        dsimp only [F]
        rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hq _)]
        have h : ‖(fourier (n:ℤ) x).re‖≤1 := by
          simpa only [Real.norm_eq_abs,fourier_apply,Circle.norm_coe] using Complex.abs_re_le_norm (fourier (n:ℤ) x)
        simpa using mul_le_mul_of_nonneg_left h (pow_nonneg hq n)
      _ = _ := by simp
  have hsum : Summable (fun n => ∫ x,‖F n x‖ ∂AddCircle.haarAddCircle) :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg (fun x => norm_nonneg _)) hn
      (summable_geometric_of_lt_one hq hq1)
  have hswap := integral_tsum_of_summable_integral_norm hi hsum
  have hs : (fun x => ∑' n,F n x)=(fun x => (kernel q x+1)/2) := by
    funext x
    have h := kernel_series q hq hq1 x
    change (∑' n : ℕ,q^n*(fourier (n:ℤ) x).re)=_
    linarith
  have hsi : Integrable (fun x => ∑' n,F n x) AddCircle.haarAddCircle := by
    rw [hs]
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact ((kernel_continuous q hq hq1).add continuous_const).div_const 2
  have hFint (n : ℕ) : (∫ x,F n x ∂AddCircle.haarAddCircle)=if n=0 then 1 else 0 := by
    dsimp only [F]
    rw [integral_const_mul,cosine_integral]
    split_ifs with hn <;> simp [hn]
  have hS : (∫ x,∑' n,F n x ∂AddCircle.haarAddCircle)=1 := by
    rw [← hswap]
    simp_rw [hFint]
    simp
  have hk : kernel q=(fun x => 2*(∑' n,F n x)-1) := funext (kernel_series q hq hq1)
  rw [hk,integral_sub (hsi.const_mul 2) (integrable_const 1),integral_const_mul,hS]
  norm_num

theorem smoothing_bounds (q : ℝ) (hq : 0≤q) (hq1 : q<1)
    (p : UnitAddCircle → ℝ) (hp : Continuous p) (a b : ℝ)
    (hlo : ∀ x,a≤p x) (hhi : ∀ x,p x≤b) (x : UnitAddCircle) :
    a≤smoothing q p x ∧ smoothing q p x≤b := by
  have hk : Integrable (kernel q) AddCircle.haarAddCircle :=
    (kernel_continuous q hq hq1).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi : Integrable (fun y => kernel q y*p (x-y)) AddCircle.haarAddCircle := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact (kernel_continuous q hq hq1).mul (hp.comp (continuous_const.sub continuous_id))
  constructor
  · calc
      a = ∫ y,kernel q y*a ∂AddCircle.haarAddCircle := by rw [integral_mul_const,kernel_mass q hq hq1,one_mul]
      _ ≤ _ := integral_mono (hk.mul_const a) hi (fun y => mul_le_mul_of_nonneg_left (hlo (x-y)) (kernel_pos q hq hq1 y).le)
  · calc
      _ ≤ ∫ y,kernel q y*b ∂AddCircle.haarAddCircle :=
        integral_mono hi (hk.mul_const b) (fun y => mul_le_mul_of_nonneg_left (hhi (x-y)) (kernel_pos q hq hq1 y).le)
      _ = b := by rw [integral_mul_const,kernel_mass q hq hq1,one_mul]

#print axioms kernel_mass
#print axioms smoothing_bounds
end BecknerOnofri.HighDim.CirclePoisson
