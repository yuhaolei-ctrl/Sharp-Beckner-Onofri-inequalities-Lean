module

public import BecknerOnofri.LocalElevenContinuousInverse
public import BecknerOnofri.QuarticSignsEleven
public import BecknerOnofri.AmplitudeLinearization
public import BecknerOnofri.LocalElevenCore.ReducedCubicParity
public import BecknerOnofri.QuarticBranches

@[expose] public section

/-! The exact limiting real-amplitude equation and its invertible full-mode
linearization. The cubic is identified with the actual Fourier reduction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.HighDim.LocalEleven.AmplitudeLinearization

open BecknerOnofri.HighDim.AmplitudeLinearization hiding Amplitudes inverseJacobian inverseJacobian_apply inverseJacobian_left inverseJacobian_right jacobian jacobianEquiv jacobian_apply limitingEquation limitingEquation_cubic limitingEquation_hasFDerivAt limitingEquation_one sumCLM sumCLM_apply sumProjection sumProjection_apply
open BecknerOnofri.HighDim.ReducedCubicExpansion hiding U_cube_difference U_square_difference coordinates_U coordinates_center coordinates_const coordinates_quadraticTerm_difference coordinates_shellSquare cubicModel cubicModel_analytic cubicModel_apply cubicModel_diagonal cubicModel_neg cubicTerm_assembly_analytic cubicTerm_difference quadraticCorrection_analytic quadraticCorrection_product_error realDiagonal realDiagonal_apply reduced_cubic_expansion reduced_cubic_expansion_fifth reduced_diagonal_cubic_expansion reduced_diagonal_cubic_expansion_fifth
open ContinuousFirstShell ReducedCubicExpansion

abbrev Amplitudes (d : ℕ) := Fin d → ℝ

def sumCLM (d : ℕ) : Amplitudes d →L[ℝ] ℝ := ∑ i, ContinuousLinearMap.proj i

@[simp] theorem sumCLM_apply {d : ℕ} (r : Amplitudes d) : sumCLM d r = ∑ i, r i := by
  simp [sumCLM]

def sumProjection (d : ℕ) : Amplitudes d →L[ℝ] Amplitudes d :=
  ContinuousLinearMap.pi (fun _ => sumCLM d)

@[simp] theorem sumProjection_apply {d : ℕ} (r : Amplitudes d) (i : Fin d) :
    sumProjection d r i = ∑ j, r j := by simp [sumProjection]

def limitingEquation (d : ℕ) (r : Amplitudes d) : Amplitudes d := fun i =>
  -kappa d*r i + (quarticB d-2*quarticA d)*(r i)^3 - quarticB d*r i*(∑ j, (r j)^2)

theorem limitingEquation_cubic {d : ℕ} (hd : 11 ≤ d) (r : Amplitudes d) (i : Fin d) :
    ((limitingEquation d r i : ℝ) : ℂ) =
      cubicModel hd (fun j => (r j:ℂ)) i - (kappa d:ℂ)*(r i:ℂ) := by
  rw [cubicModel_apply]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, limitingEquation]
  push_cast
  ring

theorem limitingEquation_one (d : ℕ) : limitingEquation d (fun _ => 1) = 0 := by
  funext i
  simp only [limitingEquation, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, Pi.zero_apply]
  unfold kappa
  ring

def jacobian (d : ℕ) : Amplitudes d →L[ℝ] Amplitudes d :=
  (2*(quarticB d-2*quarticA d)) • ContinuousLinearMap.id ℝ (Amplitudes d) -
    (2*quarticB d) • sumProjection d

@[simp] theorem jacobian_apply {d : ℕ} (r : Amplitudes d) (i : Fin d) :
    jacobian d r i = 2*(quarticB d-2*quarticA d)*r i - 2*quarticB d*(∑ j,r j) := by
  simp [jacobian]

theorem limitingEquation_hasFDerivAt (d : ℕ) :
    HasFDerivAt (limitingEquation d) (jacobian d) (fun _ => 1) := by
  have hS : HasFDerivAt (fun r : Amplitudes d => ∑ j, (r j)^2)
      (2 • sumCLM d) (fun _ => 1) := by
    have hs := HasFDerivAt.fun_sum (u := Finset.univ)
      (fun j _ => ((ContinuousLinearMap.proj j : Amplitudes d →L[ℝ] ℝ).hasFDerivAt
        (x := fun _ => 1)).pow 2)
    convert! hs using 1
    apply ContinuousLinearMap.ext
    intro r
    simp [sumCLM, Finset.mul_sum]
  have hj : jacobian d = ContinuousLinearMap.pi
      (fun i => (ContinuousLinearMap.proj i).comp (jacobian d)) := by
    ext r i
    rfl
  rw [hj]
  apply hasFDerivAt_pi.mpr
  intro i
  have hi := (ContinuousLinearMap.proj i : Amplitudes d →L[ℝ] ℝ).hasFDerivAt (x := fun _ => 1)
  have hh := ((hi.const_mul (-kappa d)).add
    ((hi.pow 3).const_mul (quarticB d-2*quarticA d))).sub ((hi.mul hS).const_mul (quarticB d))
  convert! hh using 1
  · funext r
    simp only [limitingEquation, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
      ContinuousLinearMap.proj_apply]
    ring
  · apply ContinuousLinearMap.ext
    intro r
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply,
      smul_eq_mul, sumCLM_apply, jacobian_apply, one_pow, mul_one,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    unfold kappa
    ring

def inverseJacobian (d : ℕ) : Amplitudes d →L[ℝ] Amplitudes d :=
  (1/(2*(quarticB d-2*quarticA d))) • ContinuousLinearMap.id ℝ (Amplitudes d) +
    (quarticB d/(2*(quarticB d-2*quarticA d)*kappa d)) • sumProjection d

@[simp] theorem inverseJacobian_apply {d : ℕ} (r : Amplitudes d) (i : Fin d) :
    inverseJacobian d r i = r i/(2*(quarticB d-2*quarticA d)) +
      quarticB d/(2*(quarticB d-2*quarticA d)*kappa d)*(∑ j,r j) := by
  simp only [inverseJacobian, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, Pi.add_apply, Pi.smul_apply, sumProjection_apply, smul_eq_mul]
  ring

theorem inverseJacobian_left {d : ℕ} (hd : 11 ≤ d) (r : Amplitudes d) :
    inverseJacobian d (jacobian d r) = r := by
  have ha : quarticB d-2*quarticA d ≠ 0 := by
    have := BecknerOnofri.HighDim.LocalQuartic.quarticA_negative hd
    have := BecknerOnofri.HighDim.LocalQuartic.quarticB_positive hd
    linarith
  have hk := (BecknerOnofri.HighDim.LocalQuartic.kappa_positive hd).ne'
  have he : kappa d = quarticB d-2*quarticA d-(d:ℝ)*quarticB d := by unfold kappa; ring
  funext i
  simp only [inverseJacobian_apply, jacobian_apply, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  rw [he]
  ring

theorem inverseJacobian_right {d : ℕ} (hd : 11 ≤ d) (r : Amplitudes d) :
    jacobian d (inverseJacobian d r) = r := by
  have hi : Function.Injective (jacobian d) := Function.LeftInverse.injective (inverseJacobian_left hd)
  have hs : Function.Surjective (jacobian d) :=
    (LinearMap.injective_iff_surjective (f := (jacobian d).toLinearMap)).mp hi
  obtain ⟨s,rfl⟩ := hs r
  rw [inverseJacobian_left hd]

def jacobianEquiv {d : ℕ} (hd : 11 ≤ d) : Amplitudes d ≃L[ℝ] Amplitudes d where
  toFun := jacobian d
  invFun := inverseJacobian d
  left_inv := inverseJacobian_left hd
  right_inv := inverseJacobian_right hd
  map_add' := map_add _
  map_smul' := map_smul _
  continuous_toFun := (jacobian d).continuous
  continuous_invFun := (inverseJacobian d).continuous

#print axioms limitingEquation_hasFDerivAt
#print axioms jacobianEquiv
end BecknerOnofri.HighDim.LocalEleven.AmplitudeLinearization
