import Legacy.BecknerOnofri.ChebyshevProfileBounds
import Legacy.BecknerOnofri.SmoothFourier

/-! Separate reflection symmetry identifies the actual torus Fourier series
with its closed-cube Chebyshev profile. -/

open scoped BigOperators ContDiff

namespace Legacy.BecknerOnofri.ChebyshevProfile

open Legacy.TorusEndpoint WienerFourier

set_option maxHeartbeats 800000

def SeparatelyEven {d : ℕ} (f : Torus d → ℂ) : Prop :=
  ∀ (i : Fin d) (x : Torus d), f (Function.update x i (-x i)) = f x

def signAction {d : ℕ} {X : Type*} [Neg X] (e : Fin d → Bool) (x : Fin d → X) : Fin d → X :=
  fun i => if e i then x i else -x i

theorem signAction_invariant {d : ℕ} {f : Torus d → ℂ} (hf : SeparatelyEven f)
    (e : Fin d → Bool) (x : Torus d) : f (signAction e x) = f x := by
  classical
  have hset (s : Finset (Fin d)) : f (fun i => if i ∈ s then -x i else x i) = f x := by
    induction s using Finset.induction with
    | empty => simp
    | @insert i s hi ih =>
      have he : (fun j => if j ∈ insert i s then -x j else x j) =
          Function.update (fun j => if j ∈ s then -x j else x j) i
            (-(if i ∈ s then -x i else x i)) := by
        funext j
        by_cases hj : j = i
        · subst j
          simp [hi]
        · simp [hj, hi]
      rw [he, hf, ih]
  convert hset (Finset.univ.filter (fun i => e i = false)) using 1
  congr 1
  funext i
  cases he : e i <;> simp [signAction, he]

theorem quotient_signAction {d : ℕ} (e : Fin d → Bool) (x : Space d) :
    SmoothFourier.quotient (signAction e x) = signAction e (SmoothFourier.quotient x) := by
  funext i
  cases he : e i <;> simp [signAction, SmoothFourier.quotient, he]

noncomputable def cosinePoint {d : ℕ} (x : Space d) : Space d :=
  fun i => Real.cos (2 * Real.pi * x i)

theorem cosinePoint_mem_closedCube {d : ℕ} (x : Space d) : cosinePoint x ∈ closedCube d := by
  apply mem_closedCube.mpr
  intro i
  exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

theorem tensor_cosinePoint {d : ℕ} (k : Frequency d) (x : Space d) :
    tensor k (cosinePoint x) = ∏ i, Real.cos (2*Real.pi*(k i:ℝ)*x i) := by
  unfold tensor cosinePoint
  apply Finset.prod_congr rfl
  intro i _
  rw [Polynomial.Chebyshev.T_real_cos]
  simp only [Int.cast_natCast]
  rw [Nat.cast_natAbs, Int.cast_abs]
  by_cases hk : 0 ≤ (k i : ℝ)
  · rw [abs_of_nonneg hk]
    congr 1
    ring
  · rw [abs_of_neg (lt_of_not_ge hk)]
    have he : -(k i : ℝ) * (2*Real.pi*x i) = -(2*Real.pi*(k i:ℝ)*x i) := by ring
    rw [he, Real.cos_neg]

theorem character_sign_sum {d : ℕ} (k : Frequency d) (x : Space d) :
    (∑ e : Fin d → Bool, UnitAddTorus.mFourier k (SmoothFourier.quotient (signAction e x))) =
      (2 : ℂ)^d * (tensor k (cosinePoint x) : ℂ) := by
  classical
  have he (i : Fin d) :
      (∑ b : Bool, fourier (k i) ((if b then x i else -x i : ℝ) : UnitAddCircle)) =
        2 * (Real.cos (2*Real.pi*(k i:ℝ)*x i) : ℂ) := by
    simp only [Fintype.sum_bool, Bool.false_eq_true, if_false, if_true, fourier_coe_apply,
      Complex.ofReal_one, div_one, Complex.ofReal_neg]
    rw [Complex.ofReal_cos, Complex.two_cos]
    push_cast
    ring_nf
  calc
    _ = ∏ i : Fin d, ∑ b : Bool,
        fourier (k i) ((if b then x i else -x i : ℝ) : UnitAddCircle) := by
      rw [Fintype.prod_sum]
      rfl
    _ = ∏ i : Fin d, 2 * (Real.cos (2*Real.pi*(k i:ℝ)*x i) : ℂ) := by
      apply Finset.prod_congr rfl
      intro i _
      exact he i
    _ = _ := by
      rw [Finset.prod_mul_distrib, tensor_cosinePoint, Complex.ofReal_prod]
      simp

theorem series_sign_sum {d : ℕ} (a : Frequency d → ℂ)
    (ha : Summable (fun k => ‖a k‖)) (x : Space d) :
    (∑ e : Fin d → Bool, absoluteFourierSeries a (SmoothFourier.quotient (signAction e x))) =
      (2 : ℂ)^d * ∑' k, a k * (tensor k (cosinePoint x) : ℂ) := by
  have hs (e : Fin d → Bool) : Summable (fun k =>
      a k * UnitAddTorus.mFourier k (SmoothFourier.quotient (signAction e x))) := by
    apply ha.of_norm_bounded
    intro k
    simp only [norm_mul, mFourier_norm_apply, mul_one, le_refl]
  calc
    _ = ∑' k, ∑ e : Fin d → Bool,
        a k * UnitAddTorus.mFourier k (SmoothFourier.quotient (signAction e x)) := by
      symm
      exact Summable.tsum_finsetSum (fun e _ => hs e)
    _ = ∑' k, a k * ((2 : ℂ)^d * (tensor k (cosinePoint x) : ℂ)) := by
      apply tsum_congr
      intro k
      rw [← Finset.mul_sum, character_sign_sum]
    _ = _ := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      ring

theorem cosine_tensor_norm_le_one {d : ℕ} (k : Frequency d) (x : Space d) :
    |tensor k (cosinePoint x)| ≤ 1 := by
  rw [tensor_cosinePoint, Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun _ _ => abs_le.mpr
    ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)

theorem profile_cosine_eq {d : ℕ} (a : Frequency d → ℂ)
    (ha : Summable (fun k => ‖a k‖)) (heven : SeparatelyEven (absoluteFourierSeries a))
    (x : Space d) :
    profile a (cosinePoint x) = (absoluteFourierSeries a (SmoothFourier.quotient x)).re := by
  have hsum := series_sign_sum a ha x
  have he : (∑ e : Fin d → Bool, absoluteFourierSeries a (SmoothFourier.quotient (signAction e x))) =
      (2 : ℂ)^d * absoluteFourierSeries a (SmoothFourier.quotient x) := by
    simp_rw [quotient_signAction, signAction_invariant heven]
    simp
  rw [he] at hsum
  have hcancel := mul_left_cancel₀ (pow_ne_zero d (by norm_num : (2 : ℂ) ≠ 0)) hsum
  have hs : Summable (fun k => a k * (tensor k (cosinePoint x) : ℂ)) := by
    apply ha.of_norm_bounded
    intro k
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    simpa using mul_le_mul_of_nonneg_left (cosine_tensor_norm_le_one k x) (norm_nonneg (a k))
  have hr := congrArg Complex.re hcancel
  rw [Complex.re_tsum hs] at hr
  simpa only [profile, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero] using hr.symm

open RadialWiener TorusSobolev

theorem continuous_eq_fourierSeries {d : ℕ} (u : Torus d → ℝ) (hu : Continuous u)
    (ha : Summable (fun k => ‖densityFourier u k‖)) :
    absoluteFourierSeries (densityFourier u) = fun x => (u x : ℂ) := by
  have hc : Continuous (fun x => (u x : ℂ)) := Complex.continuous_ofReal.comp hu
  have hm : MeasureTheory.MemLp (fun x => (u x : ℂ)) 2 (torusMeasure d) :=
    hc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let U : TorusL2 d := hm.toLp (fun x => (u x : ℂ))
  have he (k : Frequency d) : fourierIsometry d U k = densityFourier u k := by
    rw [fourierIsometry_apply]
    exact fourierCoeff_congr_ae hm.coeFn_toLp k
  have hs : Summable (fun k => ‖fourierIsometry d U k‖) := by simpa only [he] using ha
  have hre : representative U = absoluteFourierSeries (densityFourier u) := by
    funext x
    unfold representative absoluteFourierSeries
    simp only [he]
  have hae : absoluteFourierSeries (densityFourier u) =ᵐ[torusMeasure d] (fun x => (u x : ℂ)) := by
    rw [← hre]
    exact (representative_ae_eq U hs).trans hm.coeFn_toLp
  haveI : (torusMeasure d).IsOpenPosMeasure := by rw [torusMeasure_explicit]; infer_instance
  exact MeasureTheory.Measure.eq_of_ae_eq hae (absoluteFourierSeries_continuous _ ha) hc

theorem continuous_profile_factorization {d : ℕ} (u : Torus d → ℝ) (hu : Continuous u)
    (ha : ∀ m : ℕ, RadialSummable (densityFourier u) m)
    (heven : ∀ (i : Fin d) (x : Torus d), u (Function.update x i (-x i)) = u x) :
    ContDiffOn ℝ ∞ (profile (densityFourier u)) (closedCube d) ∧
      ∀ x : Space d, u (SmoothFourier.quotient x) = profile (densityFourier u) (cosinePoint x) := by
  have hs := (radialSummable_zero _).mp (ha 0)
  have heq := continuous_eq_fourierSeries u hu hs
  have hev : SeparatelyEven (absoluteFourierSeries (densityFourier u)) := by
    rw [heq]
    intro i x
    simp only [heven]
  refine ⟨profile_contDiffOn _ ha, fun x => ?_⟩
  have h := profile_cosine_eq (densityFourier u) hs hev x
  rw [heq] at h
  exact h.symm

#print axioms character_sign_sum
#print axioms profile_cosine_eq
#print axioms continuous_profile_factorization

end Legacy.BecknerOnofri.ChebyshevProfile
