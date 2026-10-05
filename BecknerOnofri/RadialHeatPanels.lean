module

public import BecknerOnofri.RadialHeatTail
public import BecknerOnofri.RadialQuadrature

@[expose] public section

/-! Sign-aware theta-mode enclosures and the complete signed heat-panel rule. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators
namespace BecknerOnofri.HighDim.RadialThetaTail

def modeCosine (y : ℝ) (n : ℕ) : ℝ := Real.cos (2*Real.pi*((n:ℝ)+1)*y)

def upperMode (a b y : ℝ) (n : ℕ) : ℝ :=
  if 0≤modeCosine y n then Real.exp (-a*((n:ℝ)+1)^2)*modeCosine y n
  else Real.exp (-b*((n:ℝ)+1)^2)*modeCosine y n

def panelThetaUpper (M : ℕ) (a b y : ℝ) : ℝ :=
  1+2*∑ n∈Finset.range M,upperMode a b y n+
    2*Real.exp (-a*((M:ℝ)+1)^2)/(1-Real.exp (-a*(2*(M:ℝ)+3)))

def panelHeatUpper (a b y : ℝ) : ℝ := (panelThetaUpper 12 a b y)^12-1

theorem mode_le_upperMode {a b t : ℝ} (hat : a≤t) (htb : t≤b) (y : ℝ) (n : ℕ) :
    mode t y n≤upperMode a b y n := by
  unfold mode upperMode
  change Real.exp (-t*((n:ℝ)+1)^2)*modeCosine y n≤_
  split_ifs with h
  · apply mul_le_mul_of_nonneg_right _ h
    exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hat (sq_nonneg ((n:ℝ)+1))])
  · apply mul_le_mul_of_nonpos_right _ (le_of_not_ge h)
    exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right htb (sq_nonneg ((n:ℝ)+1))])

/-- Every retained mode uses the correct endpoint according to its cosine sign. -/
theorem theta_le_panelThetaUpper {a b t : ℝ} (ha : 0<a) (hat : a≤t) (htb : t≤b)
    (M : ℕ) (y : ℝ) : theta t y≤panelThetaUpper M a b y := by
  have htail := (abs_le.mp (theta_truncation_error ha hat M y)).2
  have hsum := Finset.sum_le_sum (s:=Finset.range M) (fun n _ => mode_le_upperMode hat htb y n)
  dsimp [partialTheta,panelThetaUpper] at *
  linarith

theorem panelThetaUpper_pos {a b : ℝ} (ha : 0<a) (hab : a≤b) (M : ℕ) (y : ℝ) :
    0<panelThetaUpper M a b y := (theta_pos ha y).trans_le (theta_le_panelThetaUpper ha le_rfl hab M y)

theorem heat_le_panelHeatUpper {a b t : ℝ} (ha : 0<a) (hat : a≤t) (htb : t≤b) (y : ℝ) :
    (theta t y)^12-1≤panelHeatUpper a b y := by
  exact sub_le_sub_right (pow_le_pow_left₀ (theta_pos (ha.trans_le hat) y).le
    (theta_le_panelThetaUpper ha hat htb 12 y) 12) 1

theorem heat_panel_integrable {a b : ℝ} (ha : 0<a) (hab : a≤b) (y : ℝ) :
    IntervalIntegrable (fun t : ℝ => t^5*((theta t y)^12-1)) volume a b :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
    ((heat_tail_integrable ha y).mono_set Ioc_subset_Ioi_self)

/-- Exact source heat-panel bound with twelve modes and the full omitted-mode remainder. -/
theorem heat_panel_bound {a b : ℝ} (ha : 0<a) (hab : a≤b) (y : ℝ) :
    (1/120:ℝ)*(∫ t in a..b,t^5*((theta t y)^12-1))≤
      ((b^6-a^6)/720)*panelHeatUpper a b y := by
  have h := RadialQuadrature.signed_heat_subinterval ha.le hab
    (fun t => (theta t y)^12-1) (heat_panel_integrable ha hab y)
    (fun t ht => heat_le_panelHeatUpper ha ht.1 ht.2 y)
  have hg : Real.Gamma 6=120 := by
    convert! Real.Gamma_nat_eq_factorial 5 using 1 <;> norm_num
  simpa only [hg] using h

/-- Directed rounding preserves the signed contribution of a negative panel upper bound. -/
theorem heat_panel_rounded_bound {a b L H : ℝ} (ha : 0<a) (hab : a≤b) (y : ℝ)
    (hL : L≤(b^6-a^6)/720) (hH : (b^6-a^6)/720≤H) :
    (1/120:ℝ)*(∫ t in a..b,t^5*((theta t y)^12-1))≤
      RadialQuadrature.roundedProduct L H (panelHeatUpper a b y) :=
  (heat_panel_bound ha hab y).trans (RadialQuadrature.mul_le_roundedProduct hL hH)

/-- Explicit complete tail term after the last heat panel. -/
def heatTailUpper (T : ℝ) : ℝ :=
  (12*heatConstant T*(1+heatConstant T*Real.exp (-T))^11/120)*
    Real.exp (-T)*120*∑ j∈Finset.range 6,T^j/(j.factorial : ℝ)

def diagonalHeat (y : ℝ) : ℝ := (1/120:ℝ)*(∫ t in Ioi 1,t^5*((theta t y)^12-1))

def heatFiniteUpper (a : ℕ → ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  (∑ i∈Finset.range n,((a (i+1)^6-a i^6)/720)*panelHeatUpper (a i) (a (i+1)) y)+
    heatTailUpper (a n)

/-- The true complete diagonal heat part is bounded by finitely many signed
panels and the explicit infinite tail; there is no unproved integrability premise. -/
theorem diagonalHeat_le_finite (a : ℕ → ℝ) (n : ℕ) (ha : Monotone a) (ha0 : a 0=1) (y : ℝ) :
    diagonalHeat y≤heatFiniteUpper a n y := by
  have hapos (i : ℕ) : 0<a i := by
    have hi := ha (Nat.zero_le i)
    rw [ha0] at hi
    linarith
  have hle (i : ℕ) : a i≤a (i+1) := ha (Nat.le_succ i)
  have h1T : (1:ℝ)≤a n := by simpa only [ha0] using ha (Nat.zero_le n)
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi
    (heat_tail_integrable (by norm_num : (0:ℝ)<1) y) h1T
  have hpanels := RadialQuadrature.finite_interval_upper (n:=n) a
    (fun t => (1/120:ℝ)*(t^5*((theta t y)^12-1)))
    (fun i => ((a (i+1)^6-a i^6)/720)*panelHeatUpper (a i) (a (i+1)) y)
    (fun i _ => (heat_panel_integrable (hapos i) (hle i) y).const_mul (1/120:ℝ))
    (fun i _ => by simpa only [intervalIntegral.integral_const_mul] using
      heat_panel_bound (hapos i) (hle i) y)
  rw [ha0,intervalIntegral.integral_const_mul] at hpanels
  have htail := heat_tail_integral_le (hapos n) y
  change (1/120:ℝ)*(∫ t in Ioi (a n),t^5*((theta t y)^12-1))≤heatTailUpper (a n) at htail
  dsimp [diagonalHeat,heatFiniteUpper]
  linarith

#print axioms theta_le_panelThetaUpper
#print axioms diagonalHeat_le_finite
#print axioms heat_panel_bound
#print axioms heat_panel_rounded_bound
end BecknerOnofri.HighDim.RadialThetaTail
