module

public import BecknerOnofri.CirclePoissonGenerator

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace BecknerOnofri.HighDim.CirclePoisson

theorem fourier_energy_hasDerivAt (r : ℕ → ℝ)
    (hr : Summable (fun n : ℕ => (r (n+1))^2)) (s : ℝ) (hs : 0<s) :
    HasDerivAt (fun t => ∑' n : ℕ,Real.exp (-2*(n+1:ℝ)*t)*(r (n+1))^2/(n+1:ℝ))
      (-2*∑' n : ℕ,Real.exp (-2*(n+1:ℝ)*s)*(r (n+1))^2) s := by
  let F : ℕ → ℝ → ℝ := fun n t => Real.exp (-2*(n+1:ℝ)*t)*(r (n+1))^2/(n+1:ℝ)
  let F' : ℕ → ℝ → ℝ := fun n t => -2*Real.exp (-2*(n+1:ℝ)*t)*(r (n+1))^2
  have hE (n : ℕ) (t : ℝ) (ht : 0<t) : Real.exp (-2*(n+1:ℝ)*t)≤1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [Nat.cast_nonneg (α:=ℝ) n])
  have hd (n : ℕ) (t : ℝ) (_ : t ∈ Ioi (0:ℝ)) : HasDerivAt (F n) (F' n t) t := by
    have h := ((((hasDerivAt_id t).const_mul (-2*(n+1:ℝ))).exp).mul_const ((r (n+1))^2)).div_const (n+1:ℝ)
    have he : Real.exp (-2*(n+1:ℝ)*t)*(-2*(n+1:ℝ))*(r (n+1))^2/(n+1:ℝ)=F' n t := by
      dsimp only [F']
      have hn : (n+1:ℝ)≠0 := by positivity
      field_simp
    simpa only [id_eq,mul_one,he,F] using h
  have hb (n : ℕ) (t : ℝ) (ht : t ∈ Ioi (0:ℝ)) : ‖F' n t‖≤2*(r (n+1))^2 := by
    simp only [F',norm_mul,Real.norm_eq_abs,abs_neg,abs_of_nonneg (by norm_num : (0:ℝ)≤2),
      abs_of_pos (Real.exp_pos _),abs_of_nonneg (sq_nonneg (r (n+1)))]
    have h := mul_le_of_le_one_left (sq_nonneg (r (n+1))) (hE n t ht)
    nlinarith
  have hstart : Summable (fun n => F n s) := by
    apply Summable.of_nonneg_of_le (fun n => by dsimp [F]; positivity) _ hr
    intro n
    dsimp only [F]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<n+1)).mpr
    calc
      _ ≤ (r (n+1))^2 := mul_le_of_le_one_left (sq_nonneg (r (n+1))) (hE n s hs)
      _ ≤ (r (n+1))^2*(n+1:ℝ) := le_mul_of_one_le_right (sq_nonneg (r (n+1))) (by linarith [Nat.cast_nonneg (α:=ℝ) n])
  have h := hasDerivAt_tsum_of_isPreconnected (hr.mul_left 2) isOpen_Ioi isPreconnected_Ioi hd hb hs hstart hs
  have he : (∑' n,F' n s)= -2*∑' n : ℕ,Real.exp (-2*(n+1:ℝ)*s)*(r (n+1))^2 := by
    simp only [F',mul_assoc,tsum_mul_left]
  rw [he] at h
  exact h

#print axioms fourier_energy_hasDerivAt
end BecknerOnofri.HighDim.CirclePoisson
