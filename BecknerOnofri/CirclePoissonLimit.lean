module

public import BecknerOnofri.CirclePoissonEntropyFisher
public import BecknerOnofri.CirclePoissonConvergence
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Normed.Group.Tannery

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
namespace BecknerOnofri.HighDim.CirclePoisson

theorem torus_flow_deviation (p : Torus 1 → ℝ) (hp : Continuous p)
    (hn : ∀ x,0≤p x) (hm : (∫ x,p x ∂torusMeasure 1)=1)
    (s : ℝ) (hs : 0<s) (hq : Real.exp (-s)≤1/2) (x : Torus 1) :
    |torusFlow s p x-1|≤12*Real.exp (-s) := by
  have hc : (∫ z : UnitAddCircle,p (fun _ => z) ∂AddCircle.haarAddCircle)=1 := by
    have h := CircleRegularity.torus_coefficient_circle (fun x => (p x:ℂ)) 0
    change UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) (0:Frequency 1)=
      _root_.fourierCoeff (fun z : UnitAddCircle => (p (fun _ => z):ℂ)) 0 at h
    simp only [UnitAddTorus.mFourierCoeff,_root_.fourierCoeff,Pi.neg_apply,neg_zero,
      UnitAddTorus.mFourier_zero,fourier_zero,ContinuousMap.one_apply,
      one_smul,integral_complex_ofReal] at h
    exact_mod_cast h.symm.trans (congrArg Complex.ofReal hm)
  have h := smoothing_deviation (Real.exp (-s)) (Real.exp_pos _).le hq
    (fun z : UnitAddCircle => p (fun _ => z)) (hp.comp (continuous_pi (fun _ => continuous_id)))
    (fun z => hn (fun _ => z)) hc (x 0)
  simpa only [torusFlow,if_neg hs.ne'] using h

theorem torus_flow_tendsto_one (p : Torus 1 → ℝ) (hp : Continuous p)
    (hn : ∀ x,0≤p x) (hm : (∫ x,p x ∂torusMeasure 1)=1) (x : Torus 1) :
    Tendsto (fun s : ℝ => torusFlow s p x) atTop (nhds 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hq := Real.tendsto_exp_neg_atTop_nhds_zero
  have hsmall : ∀ᶠ s : ℝ in atTop,Real.exp (-s)<1/2 := hq.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))
  apply squeeze_zero' (Eventually.of_forall (fun s => norm_nonneg _)) _ (by simpa using hq.const_mul 12)
  filter_upwards [eventually_gt_atTop (0:ℝ),hsmall] with s hs hqs
  exact torus_flow_deviation p hp hn hm s hs hqs.le x

theorem entropy_tendsto_zero (p : Torus 1 → ℝ) (hp : Continuous p)
    (hpos : ∀ x,0<p x) (hm : (∫ x,p x ∂torusMeasure 1)=1) :
    Tendsto (fun s : ℝ => ∫ x,torusFlow s p x*Real.log (torusFlow s p x) ∂torusMeasure 1)
      atTop (nhds 0) := by
  let P := fun s => torusFlow s p
  let B := (3/2:ℝ)*(|Real.log (1/2)|+|Real.log (3/2)|)
  have hposP (s : ℝ) (hs : 0<s) := torus_flow_positive p hp hpos s hs
  have hcont (s : ℝ) (hs : 0<s) : Continuous (fun x => P s x*Real.log (P s x)) :=
    (torus_flow_continuous s hs p hp).mul
      ((torus_flow_continuous s hs p hp).log (fun x => (hposP s hs x).ne'))
  have hmeas : ∀ᶠ s : ℝ in atTop,AEStronglyMeasurable
      (fun x => P s x*Real.log (P s x)) (torusMeasure 1) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with s hs
    exact (hcont s hs).aestronglyMeasurable
  have hsmall : ∀ᶠ s : ℝ in atTop,Real.exp (-s)<1/24 :=
    Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/24))
  have hbound : ∀ᶠ s : ℝ in atTop,∀ᵐ x ∂torusMeasure 1,‖P s x*Real.log (P s x)‖≤B := by
    filter_upwards [eventually_gt_atTop (0:ℝ),hsmall] with s hs hqs
    apply ae_of_all
    intro x
    have hb := torus_flow_deviation p hp (fun x => (hpos x).le) hm s hs (by linarith) x
    have hb' := abs_le.mp hb
    have hlo : (1/2:ℝ)≤P s x := by dsimp [P]; linarith
    have hhi : P s x≤(3/2:ℝ) := by dsimp [P]; linarith
    have hl := Real.log_le_log (by norm_num : (0:ℝ)<1/2) hlo
    have hu := Real.log_le_log (hposP s hs x) hhi
    have hab : |Real.log (P s x)|≤|Real.log (1/2)|+|Real.log (3/2)| := by
      apply abs_le.mpr
      constructor <;> linarith [neg_abs_le (Real.log (1/2)),le_abs_self (Real.log (3/2)),
        abs_nonneg (Real.log (1/2)),abs_nonneg (Real.log (3/2))]
    rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (hposP s hs x)]
    exact mul_le_mul hhi hab (abs_nonneg _) (by norm_num)
  have hlim : ∀ᵐ x ∂torusMeasure 1,Tendsto
      (fun s : ℝ => P s x*Real.log (P s x)) atTop (nhds (0:ℝ)) := by
    apply ae_of_all
    intro x
    have h := torus_flow_tendsto_one p hp (fun x => (hpos x).le) hm x
    have hl := (Real.continuousAt_log (by norm_num : (1:ℝ)≠0)).tendsto.comp h
    simpa only [Real.log_one,mul_zero,P,Function.comp_def] using h.mul hl
  have h := tendsto_integral_filter_of_dominated_convergence (fun _ => B) hmeas hbound
    (integrable_const B) hlim
  simpa only [integral_zero] using h

theorem fourier_energy_tendsto_zero (r : ℕ → ℝ)
    (hr : Summable (fun n : ℕ => (r (n+1))^2)) :
    Tendsto (fun s : ℝ => ∑' n : ℕ,Real.exp (-2*(n+1:ℝ)*s)*(r (n+1))^2/(n+1:ℝ))
      atTop (nhds 0) := by
  let F := fun s (n : ℕ) => Real.exp (-2*(n+1:ℝ)*s)*(r (n+1))^2/(n+1:ℝ)
  have hlim (n : ℕ) : Tendsto (fun s : ℝ => F s n) atTop (nhds (0:ℝ)) := by
    have hE := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (by positivity : (0:ℝ)<2*(n+1:ℝ)))
    have h := (hE.mul_const ((r (n+1))^2)).div_const (n+1:ℝ)
    simpa only [Function.comp_def,id_eq,neg_mul,F,zero_mul,zero_div] using h
  have hb : ∀ᶠ s : ℝ in atTop,∀ n : ℕ,‖F s n‖≤(r (n+1))^2 := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with s hs
    intro n
    have hE : Real.exp (-2*(n+1:ℝ)*s)≤1 := Real.exp_le_one_iff.mpr (by nlinarith [Nat.cast_nonneg (α:=ℝ) n])
    have hn : (0:ℝ)<n+1 := by positivity
    rw [Real.norm_eq_abs,abs_of_nonneg (by dsimp [F]; positivity)]
    dsimp only [F]
    apply (div_le_iff₀ hn).mpr
    calc
      _ ≤ (r (n+1))^2 := mul_le_of_le_one_left (sq_nonneg _) hE
      _ ≤ (r (n+1))^2*(n+1:ℝ) := le_mul_of_one_le_right (sq_nonneg _) (by linarith [Nat.cast_nonneg (α:=ℝ) n])
  have h := tendsto_tsum_of_dominated_convergence hr hlim hb
  simpa only [tsum_zero,F] using h

theorem deficit_tendsto_zero (p : Torus 1 → ℝ) (hp : Continuous p)
    (hpos : ∀ x,0<p x) (he : ∀ x,p (-x)=p x) (hm : (∫ x,p x ∂torusMeasure 1)=1) :
    let r : ℕ → ℝ := fun n =>
      (UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) (fun _ => (n:ℤ))).re
    Tendsto (fun s : ℝ => (∫ x,torusFlow s p x*Real.log (torusFlow s p x) ∂torusMeasure 1)-
      ∑' n : ℕ,Real.exp (-2*(n+1:ℝ)*s)*(r (n+1))^2/(n+1:ℝ)) atTop (nhds 0) := by
  dsimp only
  have hr : Summable (fun n : ℕ =>
      (UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) (fun _ => ((n+1:ℕ):ℤ))).re^2) := by
    simpa only [Nat.cast_add,Nat.cast_one] using (CircleOuter.density_parseval p hp he hm).1
  have h := (entropy_tendsto_zero p hp hpos hm).sub (fourier_energy_tendsto_zero
    (fun n : ℕ => (UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) (fun _ => (n:ℤ))).re) hr)
  simpa only [sub_zero] using h

#print axioms deficit_tendsto_zero
#print axioms entropy_tendsto_zero
#print axioms fourier_energy_tendsto_zero
end BecknerOnofri.HighDim.CirclePoisson
