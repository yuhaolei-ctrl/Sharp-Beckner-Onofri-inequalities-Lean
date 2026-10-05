import BecknerOnofri.CircleTorusFlow

/-! The actual Haar Poisson convolution satisfies ∂ₛpₛ = -Λpₛ for positive
times. Its derivative is obtained from uniformly summable Fourier derivatives. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory Set
namespace BecknerOnofri.HighDim.CirclePoisson
open CircleOuter CircleFisher Legacy.TorusEndpoint Legacy.BecknerOnofri.WeightedWiener

theorem torus_flow_hasDerivAt (p : Torus 1 → ℝ) (hp : Continuous p)
    (hw : Summable (fun k => linearWeight k*‖UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) k‖))
    (s : ℝ) (hs : 0<s) (x : Torus 1) :
    HasDerivAt (fun t => torusFlow t p x) (-lambda (torusFlow s p) x) s := by
  let a : Frequency 1 → ℂ := UnitAddTorus.mFourierCoeff (fun y => (p y:ℂ))
  let r : Frequency 1 → ℝ := fun k => |(k (0:Fin 1):ℝ)|
  have hr (k : Frequency 1) : 0≤r k := abs_nonneg _
  have he (k : Frequency 1) (t : ℝ) (ht : 0<t) : Real.exp (-r k*t)≤1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hr k)) ht.le)
  let F : Frequency 1 → ℝ → ℂ := fun k t => (Real.exp (-r k*t):ℂ)*a k*UnitAddTorus.mFourier k x
  let F' : Frequency 1 → ℝ → ℂ := fun k t =>
    ((Real.exp (-r k*t)*(-r k):ℝ):ℂ)*a k*UnitAddTorus.mFourier k x
  have hd (k : Frequency 1) (t : ℝ) (_ : t ∈ Ioi (0:ℝ)) : HasDerivAt (F k) (F' k t) t := by
    have h := ((((hasDerivAt_id t).const_mul (-r k)).exp).ofReal_comp.mul_const (a k)).mul_const
      (UnitAddTorus.mFourier k x)
    simpa only [id_eq,mul_one,F,F'] using h
  have hb (k : Frequency 1) (t : ℝ) (ht : t ∈ Ioi (0:ℝ)) : ‖F' k t‖≤r k*‖a k‖ := by
    simp only [F',norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_neg,
      abs_of_pos (Real.exp_pos _),abs_of_nonneg (hr k),mFourier_norm_apply,mul_one]
    calc
      Real.exp (-r k*t)*r k*‖a k‖=(r k*‖a k‖)*Real.exp (-r k*t) := by ring
      _ ≤ _ := mul_le_of_le_one_right (mul_nonneg (hr k) (norm_nonneg _)) (he k t ht)
  have h₀ := summable_norm linearWeight_isWeight hw
  have h₁ := first_moment_summable a hw
  have hstart : Summable (fun k => F k s) := by
    apply Summable.of_norm_bounded h₀
    intro k
    simp only [F,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
      mFourier_norm_apply,mul_one]
    exact mul_le_of_le_one_left (norm_nonneg _) (he k s hs)
  have h := hasDerivAt_tsum_of_isPreconnected h₁ isOpen_Ioi isPreconnected_Ioi hd hb hs hstart hs
  have hD : (∑' k,F' k s)= - (∑' k : Frequency 1,((|(k (0:Fin 1):ℝ)|:ℝ):ℂ)*
      UnitAddTorus.mFourierCoeff (fun y => (torusFlow s p y:ℂ)) k*UnitAddTorus.mFourier k x) := by
    rw [← tsum_neg]
    apply tsum_congr
    intro k
    rw [torus_flow_coefficient s hs p hp]
    dsimp only [F',r,a]
    push_cast
    ring
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s h
  change HasDerivAt (fun t => (∑' k,F k t).re) (∑' k,F' k s).re s at hre
  rw [hD,Complex.neg_re] at hre
  apply hre.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hs] with t ht
  have hrep := torus_flow_series t ht p hp hw x
  have hreal := congrArg Complex.re hrep
  simpa only [Complex.ofReal_re,F,r,a] using hreal

theorem smooth_torus_flow_hasDerivAt (p : Torus 1 → ℝ) (hp : Continuous p)
    (hsmooth : ContDiff ℝ 3 (fun x : ℝ => p (fun _ => (x:UnitAddCircle))))
    (s : ℝ) (hs : 0<s) (x : Torus 1) :
    HasDerivAt (fun t => torusFlow t p x) (-lambda (torusFlow s p) x) s := by
  apply torus_flow_hasDerivAt p hp _ s hs x
  exact CircleRegularity.torus_weighted_summable _ (Complex.ofRealCLM.contDiff.comp hsmooth)

#print axioms smooth_torus_flow_hasDerivAt
end BecknerOnofri.HighDim.CirclePoisson
