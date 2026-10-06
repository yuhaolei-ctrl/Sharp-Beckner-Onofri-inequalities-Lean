module

public import BecknerOnofri.EntropyTailCore
public import Mathlib.Analysis.Calculus.SmoothSeries

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators
namespace BecknerOnofri.HighDim.EntropyTail

def frequencySquare (k : Frequency 12) : ℝ := ∑ i : Fin 12, (k i : ℝ)^2

def gaussianSlope (η : ℝ) : ℝ :=
  ∑' k : Frequency 12, scalarTailWeight k * frequencySquare k * Real.exp (-η*frequencySquare k)

theorem frequencySquare_nonneg (k : Frequency 12) : 0 ≤ frequencySquare k :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem square_exp_upper {a t R : ℝ} (ha : 0 < a) (hat : a ≤ t) (hR : 0 ≤ R) :
    R*Real.exp (-t*R) ≤ (2/a)*Real.exp (-(a/2)*R) := by
  have hmax := Real.mul_exp_neg_le_exp_neg_one (a*R/2)
  have he : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hbase : (a*R/2)*Real.exp (-(a*R/2)) ≤ 1 := hmax.trans he
  have hm := mul_le_mul_of_nonneg_right hbase (Real.exp_pos (-(a*R/2))).le
  have hid : Real.exp (-(a*R/2))*Real.exp (-(a*R/2)) = Real.exp (-a*R) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hbase' : R*Real.exp (-a*R) ≤ (2/a)*Real.exp (-(a/2)*R) := by
    have hh : a/2*(R*Real.exp (-a*R)) ≤ Real.exp (-(a*R/2)) := by
      calc
        _ = (a*R/2)*Real.exp (-(a*R/2))*Real.exp (-(a*R/2)) := by rw [mul_assoc, hid]; ring
        _ ≤ _ := by simpa using hm
    have heq : -(a*R/2) = -(a/2)*R := by ring
    rw [heq] at hh
    have hh' : R*Real.exp (-a*R) ≤ Real.exp (-(a/2)*R)/(a/2) :=
      (le_div_iff₀ (by positivity : (0 : ℝ) < a/2)).mpr (by nlinarith [hh])
    convert! hh' using 1 <;> field_simp <;> ring
  exact (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by nlinarith)) hR).trans hbase'

theorem gaussianSlope_summable {η : ℝ} (hη : 0 < η) :
    Summable (fun k : Frequency 12 => scalarTailWeight k * frequencySquare k *
      Real.exp (-η*frequencySquare k)) := by
  apply Summable.of_nonneg_of_le (fun k => mul_nonneg
    (mul_nonneg (scalarTailWeight_nonneg k) (frequencySquare_nonneg k)) (Real.exp_pos _).le)
    _ ((gaussianTail_summable (half_pos hη)).mul_left (2/η))
  intro k
  have h := mul_le_mul_of_nonneg_left
    (square_exp_upper hη le_rfl (frequencySquare_nonneg k)) (scalarTailWeight_nonneg k)
  convert! h using 1 <;> unfold frequencySquare <;> ring

theorem gaussianTail_hasDerivAt {η : ℝ} (hη : 0 < η) :
    HasDerivAt gaussianTail (-gaussianSlope η) η := by
  let F : Frequency 12 → ℝ → ℝ := fun k t =>
    scalarTailWeight k * Real.exp (-t*frequencySquare k)
  let F' : Frequency 12 → ℝ → ℝ := fun k t =>
    -(scalarTailWeight k * frequencySquare k * Real.exp (-t*frequencySquare k))
  have hd (k : Frequency 12) (t : ℝ) (_ : t ∈ Ioi (η/2)) :
      HasDerivAt (F k) (F' k t) t := by
    have h := (((hasDerivAt_id t).neg.mul_const (frequencySquare k)).exp).const_mul (scalarTailWeight k)
    convert! h using 1 <;> dsimp [F, F'] <;> ring
  have hb (k : Frequency 12) (t : ℝ) (ht : t ∈ Ioi (η/2)) :
      ‖F' k t‖ ≤ (2/(η/2))*(scalarTailWeight k * Real.exp (-(η/2/2)*frequencySquare k)) := by
    rw [show F' k t = -(scalarTailWeight k * frequencySquare k * Real.exp (-t*frequencySquare k)) from rfl,
      norm_neg, Real.norm_of_nonneg (mul_nonneg
        (mul_nonneg (scalarTailWeight_nonneg k) (frequencySquare_nonneg k)) (Real.exp_pos _).le)]
    have h := mul_le_mul_of_nonneg_left
      (square_exp_upper (half_pos hη) ht.le (frequencySquare_nonneg k)) (scalarTailWeight_nonneg k)
    convert! h using 1 <;> ring
  have hs : Summable (fun k : Frequency 12 =>
      (2/(η/2))*(scalarTailWeight k * Real.exp (-(η/2/2)*frequencySquare k))) :=
    (gaussianTail_summable (half_pos (half_pos hη))).mul_left _
  have hstart : Summable (fun k => F k η) := gaussianTail_summable hη
  have h := hasDerivAt_tsum_of_isPreconnected hs isOpen_Ioi isPreconnected_Ioi
    hd hb (by change η/2 < η; linarith) hstart (by change η/2 < η; linarith)
  convert! h using 1
  simp only [F', gaussianSlope, tsum_neg]

#print axioms gaussianTail_hasDerivAt
end BecknerOnofri.HighDim.EntropyTail
