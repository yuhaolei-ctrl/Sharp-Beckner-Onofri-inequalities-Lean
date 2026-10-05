module

public import BecknerOnofri.CirclePoissonEntropyFisher
public import BecknerOnofri.CirclePoissonLimit
public import BecknerOnofri.CircleDeficitDefinitions

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
namespace BecknerOnofri.HighDim.CirclePoisson
open CircleOuter Legacy.TorusEndpoint Legacy.BecknerOnofri.WeightedWiener

theorem torus_flow_series_nonneg (s : ℝ) (hs : 0≤s) (p : Torus 1 → ℝ) (hp : Continuous p)
    (hw : Summable (fun k => linearWeight k*‖UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) k‖))
    (x : Torus 1) :
    (torusFlow s p x:ℂ)=∑' k,(Real.exp (-|(k (0:Fin 1):ℝ)| * s):ℂ)*
      UnitAddTorus.mFourierCoeff (fun y => (p y:ℂ)) k*UnitAddTorus.mFourier k x := by
  rcases hs.eq_or_lt with h | h
  · subst s
    simp only [torusFlow,ite_true,mul_zero,Real.exp_zero,Complex.ofReal_one,one_mul]
    let P : C(Torus 1,ℂ) := ⟨fun x => (p x:ℂ),Complex.continuous_ofReal.comp hp⟩
    have h := UnitAddTorus.hasSum_mFourier_series_apply_of_summable (f:=P)
      (summable_norm linearWeight_isWeight hw).of_norm x
    simpa only [P,ContinuousMap.coe_mk,smul_eq_mul] using h.tsum_eq.symm
  · exact torus_flow_series s h p hp hw x

theorem torus_flow_tendsto_initial (p : Torus 1 → ℝ) (hp : Continuous p)
    (hw : Summable (fun k => linearWeight k*‖UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) k‖))
    (x : Torus 1) : Tendsto (fun s : ℝ => torusFlow s p x) (nhdsWithin 0 (Ici 0)) (nhds (p x)) := by
  let a : Frequency 1 → ℂ := UnitAddTorus.mFourierCoeff (fun y => (p y:ℂ))
  let F : ℝ → Frequency 1 → ℂ := fun s k => (Real.exp (-|(k (0:Fin 1):ℝ)| * s):ℂ)*a k*UnitAddTorus.mFourier k x
  have h₀ : Summable (fun k => ‖a k‖) := summable_norm linearWeight_isWeight hw
  have hlim (k : Frequency 1) : Tendsto (fun s => F s k) (nhdsWithin 0 (Ici 0))
      (nhds (a k*UnitAddTorus.mFourier k x)) := by
    have hc : Continuous (fun s : ℝ => F s k) := by dsimp [F]; fun_prop
    have ht : Tendsto (fun s => F s k) (nhdsWithin 0 (Ici 0)) (nhds (F 0 k)) :=
      hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [F,mul_zero,Real.exp_zero,Complex.ofReal_one,one_mul] using ht
  have hb : ∀ᶠ s : ℝ in nhdsWithin 0 (Ici 0),∀ k,‖F s k‖≤‖a k‖ := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    intro k
    simp only [F,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
      mFourier_norm_apply,mul_one]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (abs_nonneg _)) hs))
  have h := tendsto_tsum_of_dominated_convergence h₀ hlim hb
  have hzero := torus_flow_series_nonneg 0 le_rfl p hp hw x
  simp only [torusFlow,ite_true,mul_zero,Real.exp_zero,Complex.ofReal_one,one_mul] at hzero
  change (p x:ℂ)=∑' k,a k*UnitAddTorus.mFourier k x at hzero
  rw [← hzero] at h
  have H : Tendsto (fun s : ℝ => (torusFlow s p x:ℂ)) (nhdsWithin 0 (Ici 0)) (nhds (p x:ℂ)) := by
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (torus_flow_series_nonneg s hs p hp hw x).symm
  simpa only [Function.comp_def,Complex.ofReal_re] using Complex.continuous_re.continuousAt.tendsto.comp H

theorem torus_flow_bounds_nonneg (p : Torus 1 → ℝ) (hp : Continuous p) (a b : ℝ)
    (hlo : ∀ x,a≤p x) (hhi : ∀ x,p x≤b) (s : ℝ) (hs : 0≤s) (x : Torus 1) :
    a≤torusFlow s p x ∧ torusFlow s p x≤b := by
  rcases hs.eq_or_lt with h | h
  · subst s
    simpa only [torusFlow,ite_true] using And.intro (hlo x) (hhi x)
  · exact torus_flow_bounds p hp a b hlo hhi s h x

theorem entropy_tendsto_initial (p : Torus 1 → ℝ) (hp : Continuous p) (hpos : ∀ x,0<p x)
    (hw : Summable (fun k => linearWeight k*‖UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) k‖)) :
    Tendsto (fun s : ℝ => ∫ x,torusFlow s p x*Real.log (torusFlow s p x) ∂torusMeasure 1)
      (nhdsWithin 0 (Ici 0)) (nhds (∫ x,p x*Real.log (p x) ∂torusMeasure 1)) := by
  obtain ⟨xmin, _, hmin⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hp.continuousOn
  obtain ⟨xmax, _, hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hp.continuousOn
  let a := p xmin
  let b := p xmax
  let B := b*(|Real.log a|+|Real.log b|)
  have ha : 0<a := hpos xmin
  have hb : 0<b := hpos xmax
  have hbounds (s : ℝ) (hs : 0≤s) (x : Torus 1) : a≤torusFlow s p x ∧ torusFlow s p x≤b :=
    torus_flow_bounds_nonneg p hp a b (fun x => hmin (Set.mem_univ x))
      (fun x => hmax (Set.mem_univ x)) s hs x
  have hpositive (s : ℝ) (hs : 0≤s) (x : Torus 1) : 0<torusFlow s p x := ha.trans_le (hbounds s hs x).1
  have hcont (s : ℝ) (hs : 0≤s) : Continuous (torusFlow s p) := by
    rcases hs.eq_or_lt with h | h
    · subst s
      have hz : torusFlow (0:ℝ) p=p := by funext x; simp [torusFlow]
      rw [hz]
      exact hp
    · exact torus_flow_continuous s h p hp
  have hmeas : ∀ᶠ s : ℝ in nhdsWithin 0 (Ici 0),AEStronglyMeasurable
      (fun x => torusFlow s p x*Real.log (torusFlow s p x)) (torusMeasure 1) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact ((hcont s hs).mul ((hcont s hs).log (fun x => (hpositive s hs x).ne'))).aestronglyMeasurable
  have hbound : ∀ᶠ s : ℝ in nhdsWithin 0 (Ici 0),∀ᵐ x ∂torusMeasure 1,
      ‖torusFlow s p x*Real.log (torusFlow s p x)‖≤B := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    apply ae_of_all
    intro x
    obtain ⟨hl,hu⟩ := hbounds s hs x
    have hll := Real.log_le_log ha hl
    have hlu := Real.log_le_log (hpositive s hs x) hu
    have hlog : |Real.log (torusFlow s p x)|≤|Real.log a|+|Real.log b| := by
      apply abs_le.mpr
      constructor <;> linarith [neg_abs_le (Real.log a),le_abs_self (Real.log b),
        abs_nonneg (Real.log a),abs_nonneg (Real.log b)]
    rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (hpositive s hs x)]
    exact mul_le_mul hu hlog (abs_nonneg _) hb.le
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => B) hmeas hbound (integrable_const B)
  apply ae_of_all
  intro x
  have h := torus_flow_tendsto_initial p hp hw x
  have hl := (Real.continuousAt_log (hpos x).ne').tendsto.comp h
  simpa only [Function.comp_def] using h.mul hl

theorem fourier_energy_tendsto_initial (r : ℕ → ℝ)
    (hr : Summable (fun n : ℕ => (r (n+1))^2)) :
    Tendsto (fun s : ℝ => ∑' n : ℕ,Real.exp (-2*(n+1:ℝ)*s)*(r (n+1))^2/(n+1:ℝ))
      (nhdsWithin 0 (Ici 0)) (nhds (∑' n : ℕ,(r (n+1))^2/(n+1:ℝ))) := by
  let F := fun s (n : ℕ) => Real.exp (-2*(n+1:ℝ)*s)*(r (n+1))^2/(n+1:ℝ)
  have hlim (n : ℕ) : Tendsto (fun s => F s n) (nhdsWithin 0 (Ici 0)) (nhds ((r (n+1))^2/(n+1:ℝ))) := by
    have hc : Continuous (fun s => F s n) := by dsimp [F]; fun_prop
    have h : Tendsto (fun s => F s n) (nhdsWithin 0 (Ici 0)) (nhds (F 0 n)) :=
      hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [F,mul_zero,Real.exp_zero,one_mul] using h
  have hbound : ∀ᶠ s : ℝ in nhdsWithin 0 (Ici 0),∀ n : ℕ,‖F s n‖≤(r (n+1))^2 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    intro n
    have he : Real.exp (-2*(n+1:ℝ)*s)≤1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by nlinarith [Nat.cast_nonneg (α:=ℝ) n]) hs)
    rw [Real.norm_eq_abs,abs_of_nonneg (by dsimp [F]; positivity)]
    dsimp only [F]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<n+1)).mpr
    exact (mul_le_of_le_one_left (sq_nonneg _) he).trans
      (le_mul_of_one_le_right (sq_nonneg _) (by linarith [Nat.cast_nonneg (α:=ℝ) n]))
  exact tendsto_tsum_of_dominated_convergence hr hlim hbound

theorem smooth_deficit_continuous_initial (p : Torus 1 → ℝ) (hp : Continuous p)
    (hpos : ∀ x,0<p x) (he : ∀ x,p (-x)=p x) (hm : (∫ x,p x ∂torusMeasure 1)=1)
    (hsmooth : ContDiff ℝ 3 (fun x : ℝ => p (fun _ => (x:UnitAddCircle)))) :
    ContinuousWithinAt (deficit p) (Ici 0) 0 := by
  have hw := CircleRegularity.torus_weighted_summable (fun x => (p x:ℂ))
    (Complex.ofRealCLM.contDiff.comp hsmooth)
  have hr : Summable (fun n : ℕ => (moment p (n+1))^2) := by
    simpa only [moment,Nat.cast_add,Nat.cast_one] using (density_parseval p hp he hm).1
  have h := (entropy_tendsto_initial p hp hpos hw).sub (fourier_energy_tendsto_initial (moment p) hr)
  change Tendsto (deficit p) (nhdsWithin 0 (Ici 0)) (nhds (deficit p 0))
  have h0 : deficit p 0=(∫ x,p x*Real.log (p x) ∂torusMeasure 1)-
      ∑' n : ℕ,(moment p (n+1))^2/(n+1:ℝ) := by simp [deficit,torusFlow]
  rw [h0]
  exact h

#print axioms smooth_deficit_continuous_initial
#print axioms torus_flow_tendsto_initial
end BecknerOnofri.HighDim.CirclePoisson
