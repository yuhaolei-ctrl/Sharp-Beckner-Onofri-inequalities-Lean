import BecknerOnofri.RadialSeedIntegrability

/-! Finite origin/interior/endpoint evaluation of the actual radial integral.
The only inputs are elementary geometric properties of the finite grids. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators
namespace BecknerOnofri.HighDim.RadialSeedReduction
open RadialGreenHeat RadialQuadrature

def originTerm (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.exp ((7/10:ℝ)*originConstant a n)*sourceS₀^((6:ℝ)-(7/10:ℝ)*sourceC)/
    (((6:ℝ)-(7/10:ℝ)*sourceC)*Real.sqrt (1-sourceS₀))

def interiorTerm (a : ℕ → ℝ) (n : ℕ) (b : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ i∈Finset.range m,Real.exp ((7/10:ℝ)*upperProfile a n (b i))*
    (b (i+1)^6-b i^6)/(6*Real.sqrt (1-b (i+1)))

def endpointTerm (a : ℕ → ℝ) (n : ℕ) (v : ℕ → ℝ) (l : ℕ) : ℝ :=
  ∑ i∈Finset.range l,Real.exp ((7/10:ℝ)*upperProfile a n (1-v (i+1)^2))*
    (endpointPrimitive (v (i+1))-endpointPrimitive (v i))

theorem origin_term_bound (a : ℕ → ℝ) (n : ℕ) (ha : Monotone a) (ha0 : a 0=1) :
    (∫ S in 0..sourceS₀,profileIntegrand S)≤originTerm a n :=
  RadialOrigin.origin_integral_bound sourceS₀_pos (sourceS₀_lt.trans (by norm_num)) source_power_pos
    (radialGreen 12) (fun S hS => profile_origin_bound a n ha ha0 hS) (origin_integrable a n ha ha0)

theorem interior_term_bound (a : ℕ → ℝ) (n : ℕ) (ha : Monotone a) (ha0 : a 0=1)
    (b : ℕ → ℝ) (m : ℕ) (hb : Monotone b) (hb0 : b 0=sourceS₀) (hbm : b m=7/16) :
    (∫ S in sourceS₀..(7/16:ℝ),profileIntegrand S)≤interiorTerm a n b m := by
  have hpos (i : ℕ) : 0<b i := by
    have hh := hb (Nat.zero_le i)
    rw [hb0] at hh
    exact sourceS₀_pos.trans_le hh
  have hle (i : ℕ) (hi : i≤m) : b i≤7/16 := by simpa only [hbm] using hb hi
  have hstep (i : ℕ) : b i≤b (i+1) := hb (Nat.le_succ i)
  have hI (i : ℕ) (hi : i<m) : IntervalIntegrable profileIntegrand volume (b i) (b (i+1)) :=
    interior_integrable (hpos i) (hstep i) ((hle _ (by omega)).trans_lt (by norm_num))
  have hh := finite_interval_upper b profileIntegrand
    (fun i => Real.exp ((7/10:ℝ)*upperProfile a n (b i))*(b (i+1)^6-b i^6)/(6*Real.sqrt (1-b (i+1)))) hI (by
      intro i hi
      apply radial_subinterval_explicit (hpos i).le (hstep i) ((hle _ (by omega)).trans_lt (by norm_num))
        (radialGreen 12) _ _ (hI i hi)
      · apply (radialGreen_antitone (by norm_num : 0<12)).mono
        intro S hS
        exact ⟨(hpos i).trans_le hS.1,by norm_num; linarith [hS.2,hle (i+1) (by omega)]⟩
      · exact radialGreen_le_finite a n ha ha0 ⟨hpos i,by linarith [hle i (by omega)]⟩)
  simpa only [hb0,hbm,interiorTerm] using hh

theorem endpoint_term_bound (a : ℕ → ℝ) (n : ℕ) (ha : Monotone a) (ha0 : a 0=1)
    (v : ℕ → ℝ) (l : ℕ) (hv : Monotone v) (hv0 : v 0=0) (hvl : v l=3/4) :
    (∫ S in (7/16:ℝ)..1,profileIntegrand S)≤endpointTerm a n v l := by
  have hvnonneg (i : ℕ) : 0≤v i := by simpa only [hv0] using hv (Nat.zero_le i)
  have hvle (i : ℕ) (hi : i≤l) : v i≤3/4 := by simpa only [hvl] using hv hi
  have hstep (i : ℕ) : v i≤v (i+1) := hv (Nat.le_succ i)
  let f := fun t : ℝ => 2*(1-t^2)^5*Real.exp ((7/10:ℝ)*radialGreen 12 (1-t^2))
  have hI : IntervalIntegrable f volume 0 (3/4) :=
    endpoint_transformed_integrable (radialGreen 12) (radialGreen_measurable 12) (radialGreen_antitone (by norm_num))
  have hpanel (i : ℕ) (hi : i<l) : IntervalIntegrable f volume (v i) (v (i+1)) := by
    apply hI.mono_set
    rw [uIcc_of_le (hstep i),uIcc_of_le (by norm_num : (0:ℝ)≤3/4)]
    exact Icc_subset_Icc (hvnonneg i) (hvle (i+1) (by omega))
  have hh := finite_interval_upper v f
    (fun i => Real.exp ((7/10:ℝ)*upperProfile a n (1-v (i+1)^2))*
      (endpointPrimitive (v (i+1))-endpointPrimitive (v i))) hpanel (by
      intro i hi
      have hib : v (i+1)≤3/4 := hvle (i+1) (by omega)
      have hlow : 0<1-v (i+1)^2 := by nlinarith [hvnonneg (i+1)]
      have hupper : 1-v i^2≤1 := by nlinarith [sq_nonneg (v i)]
      apply endpoint_subinterval (hvnonneg i) (hstep i) (by linarith) (radialGreen 12) _ _ (hpanel i hi)
      · apply (radialGreen_antitone (by norm_num : 0<12)).mono
        intro S hS
        exact ⟨hlow.trans_le hS.1,by norm_num; linarith [hS.2]⟩
      · exact radialGreen_le_finite a n ha ha0 ⟨hlow,by nlinarith [sq_nonneg (v (i+1))]⟩)
  rw [hv0,hvl] at hh
  rw [show profileIntegrand=(fun S => radialWeight S*Real.exp ((7/10:ℝ)*radialGreen 12 S)) from rfl,
    endpoint_integral_change]
  exact hh

theorem radial_integral_finite_bound (a : ℕ → ℝ) (n : ℕ) (ha : Monotone a) (ha0 : a 0=1)
    (b : ℕ → ℝ) (m : ℕ) (hb : Monotone b) (hb0 : b 0=sourceS₀) (hbm : b m=7/16)
    (v : ℕ → ℝ) (l : ℕ) (hv : Monotone v) (hv0 : v 0=0) (hvl : v l=3/4) :
    (∫ S in 0..1,profileIntegrand S)≤originTerm a n+interiorTerm a n b m+endpointTerm a n v l := by
  have hi := interior_integrable sourceS₀_pos sourceS₀_lt.le (by norm_num : (7/16:ℝ)<1)
  have he := endpoint_radial_integrable (radialGreen 12) (radialGreen_measurable 12) (radialGreen_antitone (by norm_num))
  rw [← intervalIntegral.integral_add_adjacent_intervals ((origin_integrable a n ha ha0).trans hi) he,
    ← intervalIntegral.integral_add_adjacent_intervals (origin_integrable a n ha ha0) hi]
  exact add_le_add (add_le_add (origin_term_bound a n ha ha0) (interior_term_bound a n ha ha0 b m hb hb0 hbm))
    (endpoint_term_bound a n ha ha0 v l hv hv0 hvl)

#print axioms radial_integral_finite_bound
end BecknerOnofri.HighDim.RadialSeedReduction
