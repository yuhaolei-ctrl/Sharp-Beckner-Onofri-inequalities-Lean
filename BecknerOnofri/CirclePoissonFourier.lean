module

public import BecknerOnofri.CirclePoissonProbability

@[expose] public section

/-! Exact Fourier multipliers of the actual rational Poisson kernel. -/
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace BecknerOnofri.HighDim.CirclePoisson

theorem cosine_fourier_coefficient (m n : ℤ) :
    _root_.fourierCoeff (fun x : UnitAddCircle => ((fourier m x).re:ℂ)) n=
      ((if n=m then 1 else 0)+(if n= -m then 1 else 0))/2 := by
  have hf (k : ℤ) : Integrable (fourier k : UnitAddCircle → ℂ) AddCircle.haarAddCircle :=
    (fourier k).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he : (fun x : UnitAddCircle => ((fourier m x).re:ℂ))=
      (fun x => (1/2:ℂ)*(fourier m x+fourier (-m) x)) := by
    funext x
    rw [fourier_neg,Complex.re_eq_add_conj]
    ring
  rw [he,_root_.fourierCoeff.const_mul]
  have hadd := congrFun (_root_.fourierCoeff.add (hf m) (hf (-m))) n
  change _root_.fourierCoeff (fun x : UnitAddCircle => fourier m x+fourier (-m) x) n=_ at hadd
  rw [hadd,fourierCoeff_fourier,fourierCoeff_fourier]
  simp only [Pi.add_apply,Pi.single_apply]
  ring

theorem kernel_coefficient_pos (q : ℝ) (hq : 0≤q) (hq1 : q<1)
    (n : ℕ) (hn : 0<n) :
    _root_.fourierCoeff (fun x => (kernel q x:ℂ)) (n:ℤ)=(q^n:ℝ) := by
  let F : ℕ → UnitAddCircle → ℂ := fun m x =>
    fourier (-(n:ℤ)) x*((q^m:ℝ):ℂ)*((fourier (m:ℤ) x).re:ℂ)
  have hi (m : ℕ) : Integrable (F m) AddCircle.haarAddCircle := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    dsimp [F]
    fun_prop
  have hb (m : ℕ) (x : UnitAddCircle) : ‖F m x‖≤q^m := by
    dsimp only [F]
    rw [norm_mul,norm_mul,show ‖fourier (-(n:ℤ)) x‖=1 by simp only [fourier_apply,Circle.norm_coe],one_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hq _),Complex.norm_real,Real.norm_eq_abs]
    have hr : |(fourier (m:ℤ) x).re|≤1 := by
      simpa only [fourier_apply,Circle.norm_coe] using Complex.abs_re_le_norm (fourier (m:ℤ) x)
    simpa using mul_le_mul_of_nonneg_left hr (pow_nonneg hq m)
  have hnrm (m : ℕ) : (∫ x,‖F m x‖ ∂AddCircle.haarAddCircle)≤q^m := by
    calc
      _ ≤ ∫ _ : UnitAddCircle,q^m ∂AddCircle.haarAddCircle := integral_mono (hi m).norm (integrable_const _) (hb m)
      _ = _ := by simp
  have hsum : Summable (fun m => ∫ x,‖F m x‖ ∂AddCircle.haarAddCircle) :=
    Summable.of_nonneg_of_le (fun m => integral_nonneg (fun x => norm_nonneg _)) hnrm
      (summable_geometric_of_lt_one hq hq1)
  have hswap := integral_tsum_of_summable_integral_norm hi hsum
  have hterm (m : ℕ) : (∫ x,F m x ∂AddCircle.haarAddCircle)=
      if m=n then ((q^n:ℝ):ℂ)/2 else 0 := by
    have he : (fun x => F m x)=(fun x : UnitAddCircle =>
        ((q^m:ℝ):ℂ)*(fourier (-(n:ℤ)) x*((fourier (m:ℤ) x).re:ℂ))) := by
      funext x; dsimp [F]; ring
    rw [he,integral_const_mul]
    change ((q^m:ℝ):ℂ)*_root_.fourierCoeff (fun x : UnitAddCircle => ((fourier (m:ℤ) x).re:ℂ)) (n:ℤ)=_
    rw [cosine_fourier_coefficient]
    have hneg : (n:ℤ) ≠ -(m:ℤ) := by omega
    rw [if_neg hneg]
    by_cases hm : m=n
    · subst m; simp [div_eq_mul_inv]
    · have hne : (n:ℤ)≠(m:ℤ) := by omega
      simp [hm,hne]
  have hint : (∫ x,∑' m,F m x ∂AddCircle.haarAddCircle)=(q^n:ℝ)/2 := by
    rw [← hswap]
    simp_rw [hterm]
    simp
  have hpoint (x : UnitAddCircle) :
      (∑' m,F m x)=fourier (-(n:ℤ)) x*((kernel q x+1:ℝ):ℂ)/2 := by
    have hs := (Complex.ofRealCLM.hasSum (series_summable q hq hq1 x).hasSum).mul_left (fourier (-(n:ℤ)) x)
    have he : (∑' m,F m x)=fourier (-(n:ℤ)) x*((∑' m : ℕ,q^m*(fourier (m:ℤ) x).re:ℝ):ℂ) := by
      simpa only [Complex.ofRealCLM_apply,Complex.ofReal_mul,F,mul_assoc] using hs.tsum_eq
    rw [he]
    have hh := kernel_series q hq hq1 x
    have hh' : (∑' m : ℕ,q^m*(fourier (m:ℤ) x).re)=(kernel q x+1)/2 := by linarith
    rw [hh']
    push_cast
    ring
  have hki : Integrable (fun x : UnitAddCircle => fourier (-(n:ℤ)) x*(kernel q x:ℂ)) AddCircle.haarAddCircle := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact (fourier _).continuous.mul (Complex.continuous_ofReal.comp (kernel_continuous q hq hq1))
  have hfi : Integrable (fourier (-(n:ℤ)) : UnitAddCircle → ℂ) AddCircle.haarAddCircle :=
    (fourier _).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hz : (∫ x : UnitAddCircle,fourier (-(n:ℤ)) x ∂AddCircle.haarAddCircle)=0 := by
    have h := congrFun (fourierCoeff_fourier (T:=1) 0) (n:ℤ)
    simpa [_root_.fourierCoeff,smul_eq_mul,Pi.single_apply,hn.ne',show (n:ℤ)≠0 by omega] using h
  simp_rw [hpoint] at hint
  have hexp : (fun x : UnitAddCircle => fourier (-(n:ℤ)) x*((kernel q x+1:ℝ):ℂ)/2)=
      (fun x => (fourier (-(n:ℤ)) x*(kernel q x:ℂ)+fourier (-(n:ℤ)) x)/2) := by
    funext x; push_cast; ring
  rw [hexp,integral_div,integral_add hki hfi,hz,add_zero] at hint
  change (∫ x,fourier (-(n:ℤ)) x*(kernel q x:ℂ) ∂AddCircle.haarAddCircle)=_
  exact (div_left_inj' (by norm_num : (2:ℂ)≠0)).mp hint

theorem real_coefficient_neg (p : UnitAddCircle → ℝ) (n : ℤ) :
    _root_.fourierCoeff (fun x => (p x:ℂ)) (-n)=
      conj (_root_.fourierCoeff (fun x => (p x:ℂ)) n) := by
  unfold _root_.fourierCoeff
  rw [← integral_conj]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp only [smul_eq_mul,neg_neg,map_mul,fourier_neg,Complex.conj_conj,Complex.conj_ofReal]

theorem kernel_coefficient (q : ℝ) (hq : 0≤q) (hq1 : q<1) (n : ℤ) :
    _root_.fourierCoeff (fun x => (kernel q x:ℂ)) n=((q^n.natAbs:ℝ):ℂ) := by
  cases n with
  | ofNat n =>
    by_cases hn : n=0
    · subst n
      change _root_.fourierCoeff (fun x => (kernel q x:ℂ)) 0=1
      simp only [_root_.fourierCoeff,neg_zero,fourier_zero,one_smul,integral_complex_ofReal]
      rw [kernel_mass q hq hq1,Complex.ofReal_one]
    · exact kernel_coefficient_pos q hq hq1 n (Nat.pos_of_ne_zero hn)
  | negSucc n =>
    change _root_.fourierCoeff (fun x => (kernel q x:ℂ)) (-((n+1:ℕ):ℤ))=((q^(n+1):ℝ):ℂ)
    rw [real_coefficient_neg,kernel_coefficient_pos q hq hq1 (n+1) (by omega),Complex.conj_ofReal]

#print axioms kernel_coefficient
end BecknerOnofri.HighDim.CirclePoisson
