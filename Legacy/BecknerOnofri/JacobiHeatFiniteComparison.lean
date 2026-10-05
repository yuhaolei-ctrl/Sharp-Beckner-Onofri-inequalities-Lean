import Legacy.BecknerOnofri.JacobiHeatFinite

/-! Comparison of two concrete finite Jacobi spectral evolutions with ordered actual initial data. -/
noncomputable section
open Set MeasureTheory Filter Polynomial Classical
open scoped ContDiff Topology BigOperators
namespace Legacy.BecknerOnofri.JacobiHeatPositivity
open JacobiEigenfunctions

def potentialBottom (m : ℕ) : ℝ := (m:ℝ)*((m:ℝ)-1)

theorem potentialBottom_nonnegative {m : ℕ} (hm : 0<m) : 0≤potentialBottom m := by
  have hh : (1:ℝ)≤m := by exact_mod_cast hm
  exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hh)

theorem potentialBottom_le {m : ℕ} (hm : 0<m) {x : ℝ} (hx : x∈Ioo 0 Real.pi) :
    potentialBottom m≤potential m x := by
  have hs : 0<Real.sin x^2 := sq_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2)
  change potentialBottom m≤potentialBottom m/Real.sin x^2
  apply (le_div_iff₀ hs).mpr
  have hsin : Real.sin x^2≤1 := by nlinarith [Real.sin_sq_add_cos_sq x,sq_nonneg (Real.cos x)]
  exact mul_le_of_le_one_right (potentialBottom_nonnegative hm) hsin

/-- Two finite evolutions can be compared without sharing a spectral basis.
Only their displayed actual initial functions are ordered. -/
theorem finiteHeat_le_decayed_dirichlet {m : ℕ} (hm : 0<m)
    (F G : Finset ℕ) (c d : ℕ→ℝ)
    (hn : ∀x∈Icc 0 Real.pi,0≤finiteHeat m F c 0 x)
    (horder : ∀x∈Icc 0 Real.pi,finiteHeat m F c 0 x≤finiteHeat 1 G d 0 x)
    {t x : ℝ} (ht : 0≤t) (hx : x∈Icc 0 Real.pi) :
    finiteHeat m F c t x≤Real.exp (-potentialBottom m*t)*finiteHeat 1 G d t x := by
  let ν := potentialBottom m
  let w := fun r y => Real.exp (-ν*r)*finiteHeat 1 G d r y-finiteHeat m F c r y
  let wt := fun r y => (-ν*Real.exp (-ν*r))*finiteHeat 1 G d r y+
    Real.exp (-ν*r)*finiteTime 1 G d r y-finiteTime m F c r y
  let wx := fun r y => Real.exp (-ν*r)*finiteSpace 1 G d r y-finiteSpace m F c r y
  let wxx := fun r y => Real.exp (-ν*r)*finiteSecond 1 G d r y-finiteSecond m F c r y
  have hw : ∀r∈Icc 0 t,∀y∈Icc 0 Real.pi,0≤w r y := by
    apply ParabolicComparison.nonnegative w wt wx wxx (fun _ => ν) t 0 Real.pi
    · exact (((Real.continuous_exp.comp (continuous_const.mul continuous_fst)).mul
        (finiteHeat_continuous 1 G d)).sub (finiteHeat_continuous m F c)).continuousOn
    · intro r hr y hy
      have he := (((hasDerivAt_id r).const_mul (-ν)).exp)
      convert! ((he.mul (finiteHeat_time 1 G d r y)).sub (finiteHeat_time m F c r y)).hasDerivWithinAt using 1 <;>
        simp only [w,wt,Pi.sub_apply,Pi.mul_apply,id_eq] <;> ring
    · intro r hr y hy
      exact ((finiteHeat_space 1 G d r y).const_mul _).sub (finiteHeat_space m F c r y)
    · intro r hr y hy
      exact ((finiteHeat_second 1 G d r y).const_mul _).sub (finiteHeat_second m F c r y)
    · intro y hy
      exact potentialBottom_nonnegative hm
    · intro r hr y hy
      have hA := finiteHeat_equation m F c r hy
      have hB := finiteHeat_equation 1 G d r hy
      have hzero : potential 1 y=0 := by simp [potential]
      rw [hzero,zero_mul,add_zero] at hB
      have hpos : 0≤finiteHeat m F c r y :=
        finiteHeat_nonnegative hm F c (by simpa only [finiteHeat_zero_time] using hn) hr.1.le ⟨hy.1.le,hy.2.le⟩
      have hgap : 0≤potential m y-ν := sub_nonneg.mpr (potentialBottom_le hm hy)
      have he : wt r y-wxx r y+ν*w r y =
          (potential m y-ν)*finiteHeat m F c r y := by
        dsimp [wt,wxx,w]
        linear_combination Real.exp (-ν*r)*hB - hA
      rw [he]
      exact mul_nonneg hgap hpos
    · intro y hy
      change 0≤Real.exp (-ν*0)*finiteHeat 1 G d 0 y-finiteHeat m F c 0 y
      simpa using sub_nonneg.mpr (horder y hy)
    · intro r hr
      dsimp [w]
      simp [finiteHeat_left hm,finiteHeat_left (by decide : 0<1)]
    · intro r hr
      dsimp [w]
      simp [finiteHeat_right hm,finiteHeat_right (by decide : 0<1)]
  exact sub_nonneg.mp (hw t ⟨ht,le_rfl⟩ x hx)

#print axioms finiteHeat_le_decayed_dirichlet
end Legacy.BecknerOnofri.JacobiHeatPositivity
