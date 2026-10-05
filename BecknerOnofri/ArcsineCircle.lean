import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! The actual sine-square distribution under uniform circle Haar measure,
including the exact finite bin masses used by the radial partition certificate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped Topology
namespace BecknerOnofri.HighDim.ArcsineCircle

def sineSquare (x : UnitAddCircle) : ℝ := Real.sin (Real.pi*‖x‖)^2

def radius (a : ℝ) : ℝ := Real.arcsin (Real.sqrt a)/Real.pi

theorem sineSquare_continuous : Continuous sineSquare := by
  unfold sineSquare
  fun_prop

theorem norm_mem (x : UnitAddCircle) : ‖x‖∈Icc (0:ℝ) (1/2) :=
  ⟨norm_nonneg x,by simpa using AddCircle.norm_le_half_period 1 (by norm_num : (1:ℝ)≠0) (x:=x)⟩

theorem angle_mem (x : UnitAddCircle) : Real.pi*‖x‖∈Icc (0:ℝ) (Real.pi/2) := by
  have hx := norm_mem x
  constructor
  · positivity
  · nlinarith [Real.pi_pos,hx.2]

theorem radius_mem {a : ℝ} (ha : a∈Icc (0:ℝ) 1) : radius a∈Icc (0:ℝ) (1/2) := by
  refine ⟨div_nonneg (Real.arcsin_nonneg.mpr (Real.sqrt_nonneg _)) Real.pi_pos.le,?_⟩
  apply (div_le_iff₀ Real.pi_pos).mpr
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using Real.arcsin_le_pi_div_two (Real.sqrt a)

theorem sineSquare_mem (x : UnitAddCircle) : sineSquare x∈Icc (0:ℝ) 1 := by
  refine ⟨sq_nonneg _,?_⟩
  unfold sineSquare
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi*‖x‖),sq_nonneg (Real.cos (Real.pi*‖x‖))]

theorem sineSquare_coe_of_mem {x : ℝ} (hx : x∈Icc (-(1/2:ℝ)) (1/2)) :
    sineSquare (x : UnitAddCircle)=Real.sin (Real.pi*x)^2 := by
  unfold sineSquare
  rw [(AddCircle.norm_coe_eq_abs_iff 1 (by norm_num : (1:ℝ)≠0)).mpr (by simpa using abs_le.mpr hx)]
  rcases le_total 0 x with hp|hn
  · rw [abs_of_nonneg hp]
  · rw [abs_of_nonpos hn,mul_neg,Real.sin_neg,neg_sq]

/-- This norm-based circle function is exactly the standard trigonometric one. -/
theorem sineSquare_fourier (x : UnitAddCircle) :
    sineSquare x=(1-(fourier 1 x).re)/2 := by
  let y := (AddCircle.equivIoc 1 (-(1/2:ℝ)) x : ℝ)
  have hy : y∈Icc (-(1/2:ℝ)) (1/2) := by
    have h := (AddCircle.equivIoc 1 (-(1/2:ℝ)) x).property
    constructor <;> dsimp [y] at * <;> linarith [h.1,h.2]
  have he : (y : UnitAddCircle)=x := AddCircle.coe_equivIoc
  rw [← he,sineSquare_coe_of_mem hy,fourier_coe_apply,Complex.exp_re]
  norm_num
  have hh := Real.cos_two_mul (Real.pi*y)
  have hs := Real.sin_sq_add_cos_sq (Real.pi*y)
  convert! (show Real.sin (Real.pi*y)^2=(1-Real.cos (2*(Real.pi*y)))/2 by nlinarith) using 1 <;> congr 2 <;> ring

/-- The identification holds for every real representative, not only the centered one. -/
theorem sineSquare_coe (x : ℝ) :
    sineSquare (x : UnitAddCircle)=Real.sin (Real.pi*x)^2 := by
  rw [sineSquare_fourier,fourier_coe_apply,Complex.exp_re]
  norm_num
  have hh := Real.cos_two_mul (Real.pi*x)
  have hs := Real.sin_sq_add_cos_sq (Real.pi*x)
  rw [show 2*Real.pi*x=2*(Real.pi*x) by ring]
  nlinarith

theorem sineSquare_lt_iff {a : ℝ} (ha : a∈Icc (0:ℝ) 1) (x : UnitAddCircle) :
    sineSquare x<a ↔ ‖x‖<radius a := by
  have hx := angle_mem x
  have hs : 0≤Real.sin (Real.pi*‖x‖) := Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [Real.pi_pos,hx.1,hx.2])
  have hroot : Real.sqrt a∈Icc (-1:ℝ) 1 :=
    ⟨by linarith [Real.sqrt_nonneg a],Real.sqrt_le_one.mpr ha.2⟩
  unfold sineSquare radius
  nth_rw 1 [← Real.sq_sqrt ha.1]
  rw [sq_lt_sq₀ hs (Real.sqrt_nonneg a)]
  rw [← Real.strictMonoOn_arcsin.lt_iff_lt (Real.sin_mem_Icc _) hroot,
    Real.arcsin_sin (by linarith [Real.pi_pos,hx.1,hx.2]) hx.2]
  exact (lt_div_iff₀' Real.pi_pos).symm

/-- Sine-square sublevel sets are actual metric balls on the circle. -/
theorem sublevel_eq_ball {a : ℝ} (ha : a∈Icc (0:ℝ) 1) :
    {x : UnitAddCircle | sineSquare x<a}=Metric.ball 0 (radius a) := by
  ext x
  simpa only [Set.mem_setOf_eq,Metric.mem_ball,dist_zero_right] using sineSquare_lt_iff ha x

theorem uniform_eq_volume : AddCircle.haarAddCircle (T:=1)=(volume : Measure UnitAddCircle) := by
  simpa using (AddCircle.volume_eq_smul_haarAddCircle (T:=1)).symm

/-- Exact cumulative distribution, including both endpoints. -/
theorem sublevel_measure {a : ℝ} (ha : a∈Icc (0:ℝ) 1) :
    (AddCircle.haarAddCircle (T:=1)).real {x : UnitAddCircle | sineSquare x<a}=
      (2/Real.pi)*Real.arcsin (Real.sqrt a) := by
  rw [uniform_eq_volume,sublevel_eq_ball ha]
  have hr := radius_mem ha
  have he : volume (Metric.ball (0:UnitAddCircle) (radius a))=
      volume (Metric.closedBall (0:UnitAddCircle) (radius a)) :=
    (measure_congr AddCircle.closedBall_ae_eq_ball).symm
  rw [measureReal_def,he,AddCircle.volume_closedBall,min_eq_right (by linarith [hr.2] : 2*radius a≤1),
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num) hr.1)]
  unfold radius
  ring

/-- Exact interval probability under the actual Haar probability measure. -/
theorem interval_measure {a b : ℝ} (ha : a∈Icc (0:ℝ) 1)
    (hb : b∈Icc (0:ℝ) 1) (hab : a≤b) :
    (AddCircle.haarAddCircle (T:=1)).real {x : UnitAddCircle | a≤sineSquare x ∧ sineSquare x<b}=
      (2/Real.pi)*(Real.arcsin (Real.sqrt b)-Real.arcsin (Real.sqrt a)) := by
  have he : {x : UnitAddCircle | a≤sineSquare x ∧ sineSquare x<b}=
      {x : UnitAddCircle | sineSquare x<b}\{x : UnitAddCircle | sineSquare x<a} := by
    ext x
    simp only [Set.mem_setOf_eq,Set.mem_sdiff,not_lt]
    exact and_comm
  rw [he]
  calc
    _ = (AddCircle.haarAddCircle (T:=1)).real {x : UnitAddCircle | sineSquare x<b}-
        (AddCircle.haarAddCircle (T:=1)).real {x : UnitAddCircle | sineSquare x<a} := by
      apply measureReal_sdiff
      · intro x hx
        exact lt_of_lt_of_le hx hab
      · exact sineSquare_continuous.measurable measurableSet_Iio
      · exact measure_ne_top _ _
    _ = _ := by rw [sublevel_measure hb,sublevel_measure ha]; ring

def bin (N j : ℕ) : Set UnitAddCircle :=
  {x | (j:ℝ)/N≤sineSquare x ∧ sineSquare x<((j:ℝ)+1)/N}

def binMass (N j : ℕ) : ℝ :=
  (2/Real.pi)*(Real.arcsin (Real.sqrt (((j:ℝ)+1)/N))-Real.arcsin (Real.sqrt ((j:ℝ)/N)))

theorem bin_measurable (N j : ℕ) : MeasurableSet (bin N j) :=
  (measurableSet_le measurable_const sineSquare_continuous.measurable).inter
    (measurableSet_lt sineSquare_continuous.measurable measurable_const)

theorem bin_measure {N j : ℕ} (hN : 0<N) (hj : j<N) :
    (AddCircle.haarAddCircle (T:=1)).real (bin N j)=binMass N j := by
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  apply interval_measure
  · exact ⟨by positivity,(div_le_one hNr).mpr (by exact_mod_cast hj.le)⟩
  · refine ⟨by positivity,(div_le_one hNr).mpr ?_⟩
    exact_mod_cast hj
  · exact div_le_div_of_nonneg_right (by linarith) hNr.le

theorem binMass_nonneg {N j : ℕ} (hN : 0<N) (hj : j<N) : 0≤binMass N j := by
  rw [← bin_measure hN hj]
  exact measureReal_nonneg

theorem bins_disjoint {N : ℕ} (hN : 0<N) {i j : ℕ} (hij : i≠j) :
    Disjoint (bin N i) (bin N j) := by
  rw [Set.disjoint_left]
  intro x hx hy
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hxi := (div_le_iff₀ hNr).mp hx.1
  have hxj := (lt_div_iff₀ hNr).mp hx.2
  have hyi := (div_le_iff₀ hNr).mp hy.1
  have hyj := (lt_div_iff₀ hNr).mp hy.2
  rcases lt_or_gt_of_ne hij with h | h
  · have hijr : (i:ℝ) + 1 ≤ (j:ℝ) := by exact_mod_cast h
    nlinarith
  · have hjir : (j:ℝ) + 1 ≤ (i:ℝ) := by exact_mod_cast h
    nlinarith

/-- All source bins, including the 4096-bin specialization, have the stated mass. -/
theorem source_bin_measure {j : ℕ} (hj : j<4096) :
    (AddCircle.haarAddCircle (T:=1)).real (bin 4096 j)=
      (2/Real.pi)*(Real.arcsin (Real.sqrt (((j:ℝ)+1)/4096))-
        Real.arcsin (Real.sqrt ((j:ℝ)/4096))) :=
  bin_measure (by norm_num) hj

theorem sineSquare_lt_one_ae :
    ∀ᵐ x ∂AddCircle.haarAddCircle (T:=1), sineSquare x<1 := by
  apply (mem_ae_iff_prob_eq_one (sineSquare_continuous.measurable measurableSet_Iio)).mpr
  change (AddCircle.haarAddCircle (T:=1)) {x : UnitAddCircle | sineSquare x<1}=1
  have h : (AddCircle.haarAddCircle (T:=1)).real {x : UnitAddCircle | sineSquare x<1}=1 := by
    rw [sublevel_measure (by constructor <;> norm_num)]
    simp only [Real.sqrt_one,Real.arcsin_one]
    field_simp
  have hh := congrArg ENNReal.ofReal h
  simpa only [measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _),ENNReal.ofReal_one] using hh

theorem exists_bin {N : ℕ} (hN : 0<N) (x : UnitAddCircle) (hx : sineSquare x<1) :
    ∃ j : Fin N, x∈bin N j.val := by
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  let j := ⌊sineSquare x*(N:ℝ)⌋₊
  have hj : j<N := (Nat.floor_lt' hN.ne').mpr (by nlinarith)
  refine ⟨⟨j,hj⟩,?_,?_⟩
  · exact (div_le_iff₀ hNr).mpr (Nat.floor_le (mul_nonneg (sineSquare_mem x).1 hNr.le))
  · exact (lt_div_iff₀ hNr).mpr (Nat.lt_floor_add_one _)

#print axioms sineSquare_fourier
#print axioms sublevel_measure
#print axioms source_bin_measure
end BecknerOnofri.HighDim.ArcsineCircle
