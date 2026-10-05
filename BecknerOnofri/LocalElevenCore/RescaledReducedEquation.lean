module

public import BecknerOnofri.LocalElevenContinuousInverse
public import BecknerOnofri.QuarticSignsEleven
public import BecknerOnofri.RescaledReducedEquation
public import BecknerOnofri.AnalyticParameterOrderDivision
public import BecknerOnofri.LocalElevenCore.AmplitudeLinearization
public import BecknerOnofri.LocalElevenCore.ReducedParameterExpansion
public import BecknerOnofri.LocalElevenCore.ReflectionSymmetry

@[expose] public section

/-! Analytic resolution of the cubic scaling singularity in the actual full
real-amplitude reduced equation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Filter Asymptotics
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.LocalEleven.RescaledReducedEquation

open BecknerOnofri.HighDim.RescaledReducedEquation hiding cubicModel_real_smul extension extension_analytic extension_axis extension_base extension_factor extension_factor_complex realCoordinates realCoordinates_apply reduced_rescaled_real reduced_zero_iff_extension rescaleInput rescaleInput_analytic rescaleInput_axis rescaleInput_tendsto rescaled_model scalarResidual scalarResidual_analytic scalarResidual_slice_expansion scalarResidual_slice_order
open BecknerOnofri.HighDim.AmplitudeLinearization hiding Amplitudes inverseJacobian inverseJacobian_apply inverseJacobian_left inverseJacobian_right jacobian jacobianEquiv jacobian_apply limitingEquation limitingEquation_cubic limitingEquation_hasFDerivAt limitingEquation_one sumCLM sumCLM_apply sumProjection sumProjection_apply
open BecknerOnofri.HighDim.ReducedCubicExpansion hiding U_cube_difference U_square_difference coordinates_U coordinates_center coordinates_const coordinates_quadraticTerm_difference coordinates_shellSquare cubicModel cubicModel_analytic cubicModel_apply cubicModel_diagonal cubicModel_neg cubicTerm_assembly_analytic cubicTerm_difference nonlinear_graph_derivative_axis potential_axis quadraticCorrection_analytic quadraticCorrection_product_error realDiagonal realDiagonal_apply reduced_cubic_expansion reduced_cubic_expansion_fifth reduced_derivative_axis reduced_diagonal_cubic_expansion reduced_diagonal_cubic_expansion_fifth reduced_diagonal_derivative_axis reduced_eq_linear_remainder
open BecknerOnofri.HighDim.ReducedEquation hiding complementMap_assembly complementMap_reconstruction coordinates_complement coordinates_green coordinates_one coordinates_reconstruction full full_complement full_coordinates full_mean full_zero_iff graph_full_iff_reduced local_full_iff_reduced meanZero_zero_iff mean_green potential potential_analytic reduced reduced_analytic
open ContinuousFirstShell ReducedCubicExpansion ReducedEquation AmplitudeLinearization

open AnalyticParameterDivision

def realCoordinates (d : ℕ) : Amplitudes d →L[ℝ] Coordinates d :=
  ContinuousLinearMap.pi (fun i => Complex.ofRealCLM.comp (ContinuousLinearMap.proj i))

@[simp] theorem realCoordinates_apply {d : ℕ} (r : Amplitudes d) (i : Fin d) :
    realCoordinates d r i = (r i:ℂ) := rfl

def rescaleInput (d : ℕ) (x : Amplitudes d × ℝ) : ℝ × Coordinates d :=
  (1+kappa d*x.2^2,x.2 • realCoordinates d x.1)

theorem rescaleInput_analytic (d : ℕ) (r : Amplitudes d) :
    AnalyticAt ℝ (rescaleInput d) (r,0) := by
  have hv : AnalyticAt ℝ (fun x : Amplitudes d × ℝ => realCoordinates d x.1) (r,0) :=
    ((realCoordinates d).analyticAt r).comp
      (f := (Prod.fst : Amplitudes d × ℝ → Amplitudes d)) (x := (r,(0:ℝ))) analyticAt_fst
  exact (analyticAt_const.add (analyticAt_const.mul (analyticAt_snd.pow 2))).prod
    (analyticAt_snd.smul hv)

@[simp] theorem rescaleInput_axis (d : ℕ) (r : Amplitudes d) : rescaleInput d (r,0) = (1,0) := by
  simp [rescaleInput]

def scalarResidual {d : ℕ} (hd : 11 ≤ d) (i : Fin d) (x : Amplitudes d × ℝ) : ℝ :=
  (reduced hd (rescaleInput d x) i).re

theorem scalarResidual_analytic {d : ℕ} (hd : 11 ≤ d) (i : Fin d) (r : Amplitudes d) :
    AnalyticAt ℝ (scalarResidual hd i) (r,0) := by
  have ho : AnalyticAt ℝ (reduced hd) (rescaleInput d (r,0)) := by
    simpa only [rescaleInput_axis] using reduced_analytic hd
  let ev : Coordinates d →L[ℝ] ℝ := Complex.reCLM.comp (ContinuousLinearMap.proj i)
  exact (ev.analyticAt _).comp (f := fun x => reduced hd (rescaleInput d x))
    (ho.comp (rescaleInput_analytic d r))

theorem cubicModel_real_smul {d : ℕ} (hd : 11 ≤ d) (t : ℝ) (z : Coordinates d) :
    cubicModel hd (t • z) = t^3 • cubicModel hd z := by
  ext i
  simp only [cubicModel_apply,Pi.smul_apply,Complex.real_smul,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,mul_pow,sq_abs,← Finset.mul_sum]
  push_cast
  ring

theorem rescaled_model {d : ℕ} (hd : 11 ≤ d) (r : Amplitudes d) (t : ℝ) (i : Fin d) :
    (((1-(1+kappa d*t^2)) • (t • realCoordinates d r)) i).re +
      (cubicModel hd (t • realCoordinates d r) i).re = t^3*limitingEquation d r i := by
  have hh := congrArg Complex.re (limitingEquation_cubic hd r i)
  simp only [Complex.ofReal_re,Complex.sub_re,Complex.mul_re,Complex.ofReal_im,mul_zero,sub_zero] at hh
  change limitingEquation d r i = (cubicModel hd (realCoordinates d r) i).re-kappa d*r i at hh
  rw [cubicModel_real_smul,hh]
  simp only [Pi.smul_apply,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,realCoordinates_apply,mul_zero,sub_zero,Complex.sub_re] 
  ring

theorem scalarResidual_slice_expansion {d : ℕ} (hd : 11 ≤ d) (i : Fin d) (r : Amplitudes d) :
    (fun t : ℝ => scalarResidual hd i (r,t)-t^3*limitingEquation d r i)
      =O[𝓝 0] (fun t : ℝ => ‖t‖^5) := by
  have ht : Tendsto (fun t : ℝ => rescaleInput d (r,t)) (𝓝 0) (𝓝 (1,(0:Coordinates d))) := by
    have hi : Tendsto (fun t : ℝ => (r,t)) (𝓝 0) (𝓝 (r,(0:ℝ))) :=
      (continuous_const.prodMk continuous_id).continuousAt
    convert (rescaleInput_analytic d r).continuousAt.tendsto.comp hi using 1 <;>
      first | rfl | simp only [rescaleInput_axis]
  have hb := (UniformComplementBounds.reduced_parameter_cubic_expansion hd).comp_tendsto ht
  let ev : Coordinates d →L[ℝ] ℝ := Complex.reCLM.comp (ContinuousLinearMap.proj i)
  have hh := (ev.isBigO_comp _ _).trans hb
  have he : (fun t : ℝ => ‖(rescaleInput d (r,t)).2‖^5 +
        |(rescaleInput d (r,t)).1-1| *‖(rescaleInput d (r,t)).2‖^3) =
      (fun t : ℝ => (‖realCoordinates d r‖^5 + |kappa d| *‖realCoordinates d r‖^3)*‖t‖^5) := by
    funext t
    simp only [rescaleInput,norm_smul,Real.norm_eq_abs,add_sub_cancel_left,
      abs_mul,abs_pow,abs_abs,mul_pow]
    ring
  have hm : (fun t : ℝ => ‖(rescaleInput d (r,t)).2‖^5 +
        |(rescaleInput d (r,t)).1-1| *‖(rescaleInput d (r,t)).2‖^3)
        =O[𝓝 0] (fun t : ℝ => ‖t‖^5) := by
    rw [he]
    exact (isBigO_refl _ _).const_mul_left _
  apply (hh.trans hm).congr_left
  intro t
  change (reduced hd (rescaleInput d (r,t)) i -
    ((1-(rescaleInput d (r,t)).1) • (rescaleInput d (r,t)).2) i -
    cubicModel hd (rescaleInput d (r,t)).2 i).re = _
  simp only [Complex.sub_re,rescaleInput]
  have hx := rescaled_model hd r t i
  change _ = (reduced hd (1+kappa d*t^2,t • realCoordinates d r) i).re-t^3*limitingEquation d r i
  linarith

theorem scalarResidual_slice_order {d : ℕ} (hd : 11 ≤ d) (i : Fin d) (r : Amplitudes d) :
    (fun t : ℝ => scalarResidual hd i (r,t)) =O[𝓝 0] (fun t : ℝ => ‖t‖^3) := by
  have hr := (scalarResidual_slice_expansion hd i r).trans
    (norm_pow_bigO_of_le (E := ℝ) (by norm_num : 3 ≤ 5))
  have hm : (fun t : ℝ => t^3*limitingEquation d r i) =O[𝓝 0] (fun t : ℝ => ‖t‖^3) :=
    by
      have hh := ((isBigO_refl (fun t : ℝ => t) (𝓝 0)).norm_right.pow 3).const_mul_left (limitingEquation d r i)
      convert hh using 1 <;> first | rfl | (funext t; ring)
  apply (hr.add hm).congr_left
  intro t
  ring

private theorem scalarExtension_exists {d : ℕ} (hd : 11 ≤ d) (i : Fin d) :
    ∃ g : Amplitudes d × ℝ → ℝ, AnalyticAt ℝ g ((fun _ => 1),0) ∧
      ∀ᶠ x in 𝓝 ((fun _ => 1),(0:ℝ)), scalarResidual hd i x = x.2^3*g x :=
  exists_analytic_power_factor 3 (scalarResidual_analytic hd i (fun _ => 1))
    (Eventually.of_forall (scalarResidual_slice_order hd i))

/-- Actual jointly analytic extension of R(1+κt²,t r)/t³ through t=0. -/
def extension {d : ℕ} (hd : 11 ≤ d) (x : Amplitudes d × ℝ) : Amplitudes d :=
  fun i => (scalarExtension_exists hd i).choose x

theorem extension_analytic {d : ℕ} (hd : 11 ≤ d) :
    AnalyticAt ℝ (extension hd) ((fun _ => 1),0) := by
  exact AnalyticAt.pi (fun i => (scalarExtension_exists hd i).choose_spec.1)

theorem extension_factor {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ x in 𝓝 ((fun _ : Fin d => (1:ℝ)),(0:ℝ)),
      ∀ i, scalarResidual hd i x = x.2^3*extension hd x i := by
  exact Filter.eventually_all.mpr (fun i => (scalarExtension_exists hd i).choose_spec.2)

/-- The boundary value of the genuine analytic extension is the actual
limiting polynomial, throughout an amplitude neighbourhood of the all-active point. -/
theorem extension_axis {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ r in 𝓝 (fun _ : Fin d => (1:ℝ)), extension hd (r,0)=limitingEquation d r := by
  have ht : Tendsto (fun r : Amplitudes d => (r,(0:ℝ)))
      (𝓝 (fun _ => 1)) (𝓝 ((fun _ => 1),(0:ℝ))) :=
    (continuous_id.prodMk continuous_const).continuousAt
  filter_upwards [ht.eventually (extension_analytic hd).eventually_analyticAt,
    ht.eventually (extension_factor hd).eventually_nhds] with r hr he
  funext i
  have hslice : AnalyticAt ℝ (fun t : ℝ => extension hd (r,t) i) 0 := by
    have hv := hr.comp (f := fun t : ℝ => (r,t)) (analyticAt_const.prod analyticAt_id)
    exact (analyticAt_pi_iff.mp hv) i
  have hts : Tendsto (fun t : ℝ => (r,t)) (𝓝 0) (𝓝 (r,(0:ℝ))) :=
    (continuous_const.prodMk continuous_id).continuousAt
  apply power_factor_value (N := 3) hslice.continuousAt
    ((hts.eventually he).mono (fun t h => h i))
  exact (scalarResidual_slice_expansion hd i r).trans
    (norm_pow_bigO_of_le (E := ℝ) (by norm_num : 3+1 ≤ 5))

@[simp] theorem extension_base {d : ℕ} (hd : 11 ≤ d) :
    extension hd ((fun _ => 1),0)=0 := by
  rw [(extension_axis hd).self_of_nhds,limitingEquation_one]

theorem rescaleInput_tendsto (d : ℕ) :
    Tendsto (rescaleInput d) (𝓝 ((fun _ : Fin d => (1:ℝ)),(0:ℝ)))
      (𝓝 (1,(0:Coordinates d))) := by
  simpa only [rescaleInput_axis] using
    (rescaleInput_analytic d (fun _ => 1)).continuousAt.tendsto

theorem reduced_rescaled_real {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ x in 𝓝 ((fun _ : Fin d => (1:ℝ)),(0:ℝ)),
      ∀ i, (reduced hd (rescaleInput d x) i).im=0 := by
  filter_upwards [(rescaleInput_tendsto d).eventually (ContinuousSymmetry.reduced_reflection hd)]
    with x hx
  have hc : ContinuousSymmetry.conjugateCoordinates (rescaleInput d x).2 =
      (rescaleInput d x).2 := by
    ext i
    simp [rescaleInput,ContinuousSymmetry.conjugateCoordinates_apply,Complex.real_smul]
  rw [hc] at hx
  intro i
  have hh := congrArg Complex.im (congrFun hx i)
  simp only [ContinuousSymmetry.conjugateCoordinates_apply,Complex.conj_im] at hh
  linarith

theorem extension_factor_complex {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ x in 𝓝 ((fun _ : Fin d => (1:ℝ)),(0:ℝ)),
      reduced hd (rescaleInput d x) = realCoordinates d (x.2^3 • extension hd x) := by
  filter_upwards [extension_factor hd,reduced_rescaled_real hd] with x he hr
  ext i
  apply Complex.ext
  · exact he i
  · simpa only [realCoordinates_apply,Complex.ofReal_im] using hr i

theorem reduced_zero_iff_extension {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ x in 𝓝 ((fun _ : Fin d => (1:ℝ)),(0:ℝ)), x.2≠0 →
      (reduced hd (rescaleInput d x)=0 ↔ extension hd x=0) := by
  filter_upwards [extension_factor_complex hd] with x hx ht
  rw [hx]
  constructor
  · intro h
    funext i
    have hi := congrArg (fun z : Coordinates d => (z i).re) h
    simp only [realCoordinates_apply,Pi.smul_apply,smul_eq_mul,Complex.ofReal_re,
      Pi.zero_apply,Complex.zero_re] at hi
    exact (mul_eq_zero.mp hi).resolve_left (pow_ne_zero _ ht)
  · intro h
    rw [h,smul_zero,map_zero]

#print axioms extension_factor_complex
#print axioms reduced_zero_iff_extension
#print axioms extension_analytic
#print axioms extension_axis
#print axioms scalarResidual_slice_expansion
end BecknerOnofri.HighDim.LocalEleven.RescaledReducedEquation
