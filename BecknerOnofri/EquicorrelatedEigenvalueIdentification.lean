import BecknerOnofri.EquicorrelatedRecognition

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.EquicorrelatedSpectrum
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem operator_eq_of_radial_and_row_difference (a b R T : ℝ) (i j : ι) (hij : i≠j)
    (hr : operator a b (fun _ : ι => 1)=R • (fun _ => 1))
    (ht : ∀ v : ι → ℝ,operator a b v i-operator a b v j=T*(v i-v j)) :
    operator (ι := ι) a b=operator T ((R-T)/(Fintype.card ι : ℝ)) := by
  have hrow := ht (Pi.single i 1)
  simp only [operator_apply,Pi.single_apply,if_pos rfl,if_neg hij,if_neg (Ne.symm hij),ite_true] at hrow
  have ha : a=T := by linarith
  have hrad := congrFun hr i
  simp only [operator_apply,Pi.smul_apply,smul_eq_mul,mul_one,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul] at hrad
  have hn : (Fintype.card ι : ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hb : b=(R-T)/(Fintype.card ι : ℝ) := by
    apply (eq_div_iff hn).mpr
    linarith
  rw [ha,hb]

/-- On a one-dimensional support, the transverse space has dimension zero;
any prescribed transverse coefficient gives this matrix representation. -/
theorem eq_operator_of_radial_subsingleton [Subsingleton ι]
    (M : Module.End ℝ (ι → ℝ)) (R T : ℝ)
    (hr : M (fun _ : ι => 1)=R • (fun _ => 1)) :
    M=operator T ((R-T)/(Fintype.card ι : ℝ)) := by
  let p : ι := Classical.arbitrary ι
  have hn : (Fintype.card ι : ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  apply LinearMap.ext
  intro v
  funext i
  have hv : v=v p • (fun _ : ι => (1:ℝ)) := by
    funext k
    simp only [Pi.smul_apply,smul_eq_mul,mul_one,Subsingleton.elim k p]
  rw [hv,map_smul,hr]
  simp only [operator_apply,Pi.smul_apply,smul_eq_mul,mul_one,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul]
  field_simp
  <;> ring

theorem eigenvalue_multiplicities_of_radial_transverse (R T : ℝ) (hRT : R≠T) :
    Module.finrank ℝ ((operator (ι := ι) T ((R-T)/(Fintype.card ι : ℝ))).eigenspace R)=1 ∧
    Module.finrank ℝ ((operator (ι := ι) T ((R-T)/(Fintype.card ι : ℝ))).eigenspace T)=
      Fintype.card ι-1 := by
  have hn : (Fintype.card ι : ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hb : (R-T)/(Fintype.card ι : ℝ)≠0 := div_ne_zero (sub_ne_zero.mpr hRT) hn
  have he : T+(Fintype.card ι : ℝ)*((R-T)/(Fintype.card ι : ℝ))=R := by field_simp; ring
  have h := eigenvalue_multiplicities (ι := ι) T ((R-T)/(Fintype.card ι : ℝ)) hb
  rw [he] at h
  exact h

#print axioms eigenvalue_multiplicities_of_radial_transverse
end BecknerOnofri.EquicorrelatedSpectrum
