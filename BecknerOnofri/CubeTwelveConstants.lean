import BecknerOnofri.CubeTailBound
import Mathlib.Analysis.Real.Pi.Bounds

/-! Exact rational omitted-tail certificates for the 24- and 16-point grids.
All finite arithmetic and half-integer gamma reductions are checked by Lean. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.HighDim.CubeLatticeTail
open IterationOmittedTail

private def halfFactor (n : ℕ) : ℝ := ∏i∈Finset.range n, ((i:ℝ)+1/2)

private theorem gamma_nat_half (n : ℕ) :
    Real.Gamma ((n:ℝ)+1/2)=halfFactor n*Real.sqrt Real.pi := by
  induction n with
  | zero => simpa only [Nat.cast_zero,zero_add,halfFactor,Finset.range_zero,Finset.prod_empty,one_mul] using Real.Gamma_one_half_eq
  | succ n ih =>
    rw [Nat.cast_succ,show (n:ℝ)+1+1/2=((n:ℝ)+1/2)+1 by ring,
      Real.Gamma_add_one (by positivity : (n:ℝ)+1/2≠0),ih]
    simp only [halfFactor,Finset.prod_range_succ]
    ring

private theorem pi_nat_half (n : ℕ) :
    Real.pi^((n:ℝ)+1/2)=Real.pi^n*Real.sqrt Real.pi := by
  rw [Real.rpow_add Real.pi_pos,Real.rpow_natCast,← Real.sqrt_eq_rpow]

private def gammaRatio12 (j : ℕ) : ℝ :=
  Real.pi^((j:ℝ)/2)*Real.Gamma (12-(j:ℝ)/2)/Real.Gamma 12

private theorem gamma_half_6 : Real.Gamma (13/2 : ℝ) = (10395/64)*Real.sqrt Real.pi := by
  have h:=gamma_nat_half 6
  norm_num [halfFactor,Finset.prod_range_succ] at h
  exact h

private theorem gamma_half_7 : Real.Gamma (15/2 : ℝ) = (135135/128)*Real.sqrt Real.pi := by
  have h:=gamma_nat_half 7
  norm_num [halfFactor,Finset.prod_range_succ] at h
  exact h

private theorem gamma_half_8 : Real.Gamma (17/2 : ℝ) = (2027025/256)*Real.sqrt Real.pi := by
  have h:=gamma_nat_half 8
  norm_num [halfFactor,Finset.prod_range_succ] at h
  exact h

private theorem gamma_half_9 : Real.Gamma (19/2 : ℝ) = (34459425/512)*Real.sqrt Real.pi := by
  have h:=gamma_nat_half 9
  norm_num [halfFactor,Finset.prod_range_succ] at h
  exact h

private theorem gamma_half_10 : Real.Gamma (21/2 : ℝ) = (654729075/1024)*Real.sqrt Real.pi := by
  have h:=gamma_nat_half 10
  norm_num [halfFactor,Finset.prod_range_succ] at h
  exact h

private theorem gamma_half_11 : Real.Gamma (23/2 : ℝ) = (13749310575/2048)*Real.sqrt Real.pi := by
  have h:=gamma_nat_half 11
  norm_num [halfFactor,Finset.prod_range_succ] at h
  exact h

private theorem gamma_int_7 : Real.Gamma (7:ℝ)=(720:ℝ) := by
  norm_num

private theorem gamma_int_8 : Real.Gamma (8:ℝ)=(5040:ℝ) := by
  norm_num

private theorem gamma_int_9 : Real.Gamma (9:ℝ)=(40320:ℝ) := by
  norm_num

private theorem gamma_int_10 : Real.Gamma (10:ℝ)=(362880:ℝ) := by
  norm_num

private theorem gamma_int_11 : Real.Gamma (11:ℝ)=(3628800:ℝ) := by
  norm_num

private theorem gamma_int_12 : Real.Gamma (12:ℝ)=(39916800:ℝ) := by
  norm_num

private theorem gammaRatio12_0 : gammaRatio12 0=(1:ℝ)*Real.pi^0 := by
  norm_num only [gammaRatio12,Nat.cast_ofNat]
  rw [show (0:ℝ)=((0:ℕ):ℝ) by norm_num,Real.rpow_natCast,gamma_int_12]
  ring

private theorem gammaRatio12_1 : gammaRatio12 1=(88179/524288:ℝ)*Real.pi^1 := by
  have hp:=pi_nat_half 0
  norm_num at hp
  norm_num only [gammaRatio12,Nat.cast_ofNat]
  rw [hp,gamma_half_11,gamma_int_12]
  calc
    _ = (88179/524288:ℝ)*Real.pi^0*(Real.sqrt Real.pi)^2 := by ring
    _ = _ := by rw [Real.sq_sqrt Real.pi_pos.le]; ring

private theorem gammaRatio12_2 : gammaRatio12 2=(1/11:ℝ)*Real.pi^1 := by
  norm_num only [gammaRatio12,Nat.cast_ofNat]
  rw [show (1:ℝ)=((1:ℕ):ℝ) by norm_num,Real.rpow_natCast,gamma_int_11,gamma_int_12]
  ring

private theorem gammaRatio12_3 : gammaRatio12 3=(4199/262144:ℝ)*Real.pi^2 := by
  have hp:=pi_nat_half 1
  norm_num at hp
  norm_num only [gammaRatio12,Nat.cast_ofNat]
  rw [hp,gamma_half_10,gamma_int_12]
  calc
    _ = (4199/262144:ℝ)*Real.pi^1*(Real.sqrt Real.pi)^2 := by ring
    _ = _ := by rw [Real.sq_sqrt Real.pi_pos.le]; ring

private theorem gammaRatio12_4 : gammaRatio12 4=(1/110:ℝ)*Real.pi^2 := by
  norm_num only [gammaRatio12,Nat.cast_ofNat]
  rw [show (2:ℝ)=((2:ℕ):ℝ) by norm_num,Real.rpow_natCast,gamma_int_10,gamma_int_12]
  ring

private theorem gammaRatio12_5 : gammaRatio12 5=(221/131072:ℝ)*Real.pi^3 := by
  have hp:=pi_nat_half 2
  norm_num at hp
  norm_num only [gammaRatio12,Nat.cast_ofNat]
  rw [hp,gamma_half_9,gamma_int_12]
  calc
    _ = (221/131072:ℝ)*Real.pi^2*(Real.sqrt Real.pi)^2 := by ring
    _ = _ := by rw [Real.sq_sqrt Real.pi_pos.le]; ring

private theorem gammaRatio12_6 : gammaRatio12 6=(1/990:ℝ)*Real.pi^3 := by
  norm_num only [gammaRatio12,Nat.cast_ofNat]
  rw [show (3:ℝ)=((3:ℕ):ℝ) by norm_num,Real.rpow_natCast,gamma_int_9,gamma_int_12]
  ring

private theorem gammaRatio12_7 : gammaRatio12 7=(13/65536:ℝ)*Real.pi^4 := by
  have hp:=pi_nat_half 3
  norm_num at hp
  norm_num only [gammaRatio12,Nat.cast_ofNat]
  rw [hp,gamma_half_8,gamma_int_12]
  calc
    _ = (13/65536:ℝ)*Real.pi^3*(Real.sqrt Real.pi)^2 := by ring
    _ = _ := by rw [Real.sq_sqrt Real.pi_pos.le]; ring

private theorem gammaRatio12_8 : gammaRatio12 8=(1/7920:ℝ)*Real.pi^4 := by
  norm_num only [gammaRatio12,Nat.cast_ofNat]
  rw [show (4:ℝ)=((4:ℕ):ℝ) by norm_num,Real.rpow_natCast,gamma_int_8,gamma_int_12]
  ring

private theorem gammaRatio12_9 : gammaRatio12 9=(13/491520:ℝ)*Real.pi^5 := by
  have hp:=pi_nat_half 4
  norm_num at hp
  norm_num only [gammaRatio12,Nat.cast_ofNat]
  rw [hp,gamma_half_7,gamma_int_12]
  calc
    _ = (13/491520:ℝ)*Real.pi^4*(Real.sqrt Real.pi)^2 := by ring
    _ = _ := by rw [Real.sq_sqrt Real.pi_pos.le]; ring

private theorem gammaRatio12_10 : gammaRatio12 10=(1/55440:ℝ)*Real.pi^5 := by
  norm_num only [gammaRatio12,Nat.cast_ofNat]
  rw [show (5:ℝ)=((5:ℕ):ℝ) by norm_num,Real.rpow_natCast,gamma_int_7,gamma_int_12]
  ring

private theorem gammaRatio12_11 : gammaRatio12 11=(1/245760:ℝ)*Real.pi^6 := by
  have hp:=pi_nat_half 5
  norm_num at hp
  norm_num only [gammaRatio12,Nat.cast_ofNat]
  rw [hp,gamma_half_6,gamma_int_12]
  calc
    _ = (1/245760:ℝ)*Real.pi^5*(Real.sqrt Real.pi)^2 := by ring
    _ = _ := by rw [Real.sq_sqrt Real.pi_pos.le]; ring



private def ratioRational12 (j : ℕ) : ℝ :=
  match j with
  | 0 => (1:ℝ)*(355/113:ℝ)^0
  | 1 => (88179/524288:ℝ)*(355/113:ℝ)^1
  | 2 => (1/11:ℝ)*(355/113:ℝ)^1
  | 3 => (4199/262144:ℝ)*(355/113:ℝ)^2
  | 4 => (1/110:ℝ)*(355/113:ℝ)^2
  | 5 => (221/131072:ℝ)*(355/113:ℝ)^3
  | 6 => (1/990:ℝ)*(355/113:ℝ)^3
  | 7 => (13/65536:ℝ)*(355/113:ℝ)^4
  | 8 => (1/7920:ℝ)*(355/113:ℝ)^4
  | 9 => (13/491520:ℝ)*(355/113:ℝ)^5
  | 10 => (1/55440:ℝ)*(355/113:ℝ)^5
  | 11 => (1/245760:ℝ)*(355/113:ℝ)^6
  | _ => 0

private theorem gammaRatio12_le {j : ℕ} (hj : j<12) : gammaRatio12 j≤ratioRational12 j := by
  have hpi : Real.pi≤(355/113:ℝ) := by linarith [Real.pi_lt_d20]
  interval_cases j
  · rw [gammaRatio12_0]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ Real.pi_pos.le hpi 0) (by norm_num : (0:ℝ)≤1)
  · rw [gammaRatio12_1]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ Real.pi_pos.le hpi 1) (by norm_num : (0:ℝ)≤88179/524288)
  · rw [gammaRatio12_2]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ Real.pi_pos.le hpi 1) (by norm_num : (0:ℝ)≤1/11)
  · rw [gammaRatio12_3]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ Real.pi_pos.le hpi 2) (by norm_num : (0:ℝ)≤4199/262144)
  · rw [gammaRatio12_4]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ Real.pi_pos.le hpi 2) (by norm_num : (0:ℝ)≤1/110)
  · rw [gammaRatio12_5]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ Real.pi_pos.le hpi 3) (by norm_num : (0:ℝ)≤221/131072)
  · rw [gammaRatio12_6]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ Real.pi_pos.le hpi 3) (by norm_num : (0:ℝ)≤1/990)
  · rw [gammaRatio12_7]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ Real.pi_pos.le hpi 4) (by norm_num : (0:ℝ)≤13/65536)
  · rw [gammaRatio12_8]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ Real.pi_pos.le hpi 4) (by norm_num : (0:ℝ)≤1/7920)
  · rw [gammaRatio12_9]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ Real.pi_pos.le hpi 5) (by norm_num : (0:ℝ)≤13/491520)
  · rw [gammaRatio12_10]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ Real.pi_pos.le hpi 5) (by norm_num : (0:ℝ)≤1/55440)
  · rw [gammaRatio12_11]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ Real.pi_pos.le hpi 6) (by norm_num : (0:ℝ)≤1/245760)

private def tailFactor12 (R j : ℕ) : ℝ :=
  (((R+1:ℕ):ℝ)^((j:ℝ)-24)+((R+1:ℕ):ℝ)^((j:ℝ)-23)/(23-(j:ℝ)))

private def rationalTail12 (R : ℕ) : ℝ :=
  24*∑j∈Finset.range 12,((11:ℕ).choose j:ℝ)*ratioRational12 j*tailFactor12 R j

private theorem explicitBound_twelve_eq (R : ℕ) :
    explicitBound 12 R=24*∑j∈Finset.range 12,((11:ℕ).choose j:ℝ)*gammaRatio12 j*tailFactor12 R j := by
  unfold explicitBound gammaRatio12 tailFactor12
  norm_num only [Nat.cast_ofNat,Nat.reduceSub]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [show (j:ℝ)-24+1=(j:ℝ)-23 by ring,
    show (24:ℝ)-(j:ℝ)-1=23-(j:ℝ) by ring]
  ring

private theorem explicitBound_twelve_le_rational (R : ℕ) :
    explicitBound 12 R≤rationalTail12 R := by
  rw [explicitBound_twelve_eq]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤24)
  apply Finset.sum_le_sum
  intro j hj
  have hj' : j<12 := Finset.mem_range.mp hj
  have hjr : (j:ℝ)<12 := by exact_mod_cast hj'
  have ht : 0≤tailFactor12 R j := by
    unfold tailFactor12
    apply add_nonneg (Real.rpow_nonneg (by positivity) _)
    exact div_nonneg (Real.rpow_nonneg (by positivity) _) (by linarith)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (gammaRatio12_le hj') (Nat.cast_nonneg _)) ht

/-- Exact arithmetic certificate for the 24-point grid, with cube radius eleven. -/
theorem explicitBound_twelve_eleven : explicitBound 12 11≤(77/(10:ℝ)^9)^2 := by
  apply (explicitBound_twelve_le_rational 11).trans
  norm_num [rationalTail12,ratioRational12,tailFactor12,Finset.sum_range_succ,Real.rpow_neg_natCast,Nat.choose]

/-- Exact arithmetic certificate for the 16-point grid, with cube radius seven. -/
theorem explicitBound_twelve_seven : explicitBound 12 7≤(131/(10:ℝ)^8)^2 := by
  apply (explicitBound_twelve_le_rational 7).trans
  norm_num [rationalTail12,ratioRational12,tailFactor12,Finset.sum_range_succ,Real.rpow_neg_natCast,Nat.choose]

theorem tailConstant_twelve_eleven : tailConstant (cube 12 11)≤77/(10:ℝ)^9 := by
  have h := (tailConstant_cube_sq_le (d:=12) (by norm_num) 11).trans explicitBound_twelve_eleven
  have hn := tailConstant_nonneg (cube 12 11)
  nlinarith

theorem tailConstant_twelve_seven : tailConstant (cube 12 7)≤131/(10:ℝ)^8 := by
  have h := (tailConstant_cube_sq_le (d:=12) (by norm_num) 7).trans explicitBound_twelve_seven
  have hn := tailConstant_nonneg (cube 12 7)
  nlinarith

/-- Uniform complex potential enclosure on the 24-point grid. -/
theorem omitted_potential_twelve_eleven (f : Torus 12→ℝ)
    (hf : MeasureTheory.MemLp f 2 (torusMeasure 12)) (x : Torus 12) :
    ‖omittedPotential (cube 12 11) (fourierVector f hf) x‖ ≤
      (77/(10:ℝ)^9)*Real.sqrt (∫y,(f y)^2 ∂torusMeasure 12) :=
  (omittedPotential_raw_bound (cube 12 11) f hf x).trans
    (mul_le_mul_of_nonneg_right tailConstant_twelve_eleven (Real.sqrt_nonneg _))

/-- Uniform complex potential enclosure on the 16-point grid. -/
theorem omitted_potential_twelve_seven (f : Torus 12→ℝ)
    (hf : MeasureTheory.MemLp f 2 (torusMeasure 12)) (x : Torus 12) :
    ‖omittedPotential (cube 12 7) (fourierVector f hf) x‖ ≤
      (131/(10:ℝ)^8)*Real.sqrt (∫y,(f y)^2 ∂torusMeasure 12) :=
  (omittedPotential_raw_bound (cube 12 7) f hf x).trans
    (mul_le_mul_of_nonneg_right tailConstant_twelve_seven (Real.sqrt_nonneg _))

#print axioms tailConstant_twelve_eleven
#print axioms tailConstant_twelve_seven
end BecknerOnofri.HighDim.CubeLatticeTail
