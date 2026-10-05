module

public import BecknerOnofri.PolarizationL1Properties
public import Legacy.BecknerOnofri.GibbsL2Continuity

@[expose] public section

/-! L2 continuity of genuine coordinate polarization, needed to keep the
closure of a prescribed density's orbit inside the actual optimizer set. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter Legacy.TorusEndpoint
open scoped Topology
namespace BecknerOnofri.PolarizationL2
open Legacy.BecknerOnofri CoordinatePolarization GibbsL2Continuity

lemma sorted_squared_distance_le (a b c d : ℝ) :
    (max a b-max c d)^2+(min a b-min c d)^2≤(a-c)^2+(b-d)^2 := by
  rcases le_total a b with hab | hba <;> rcases le_total c d with hcd | hdc
  · simp only [max_eq_right hab,max_eq_right hcd,min_eq_left hab,min_eq_left hcd]
    ring_nf
    exact le_rfl
  · simp only [max_eq_right hab,max_eq_left hdc,min_eq_left hab,min_eq_right hdc]
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hdc)]
  · simp only [max_eq_left hba,max_eq_right hcd,min_eq_right hba,min_eq_left hcd]
    nlinarith [mul_nonneg (sub_nonneg.mpr hba) (sub_nonneg.mpr hcd)]
  · simp only [max_eq_left hba,max_eq_left hdc,min_eq_right hba,min_eq_right hdc]
    exact le_rfl

lemma pair_squared_distance_le_on_half {d : ℕ} (i : Fin d) (a : ℝ) (f g : Torus d → ℝ)
    {x : Torus d} (hx : x∈halfTorus i a) :
    (polarize i a f x-polarize i a g x)^2+
      (polarize i a f (reflection i a x)-polarize i a g (reflection i a x))^2≤
      (f x-g x)^2+(f (reflection i a x)-g (reflection i a x))^2 := by
  rw [polarize_reflected_of_mem i a f hx,polarize_reflected_of_mem i a g hx]
  simp only [polarize,if_pos hx]
  exact sorted_squared_distance_le _ _ _ _

lemma pair_squared_distance_le {d : ℕ} (i : Fin d) (a : ℝ) (f g : Torus d → ℝ) (x : Torus d) :
    (polarize i a f x-polarize i a g x)^2+
      (polarize i a f (reflection i a x)-polarize i a g (reflection i a x))^2≤
      (f x-g x)^2+(f (reflection i a x)-g (reflection i a x))^2 := by
  rcases reflection_half_or_fixed i a x with hf | hr
  · simp only [hf,polarize_of_fixed i a f hf,polarize_of_fixed i a g hf,le_refl]
  · by_cases hx : x∈halfTorus i a
    · exact pair_squared_distance_le_on_half i a f g hx
    · have h := pair_squared_distance_le_on_half i a f g (hr.mpr hx)
      rw [reflection_involutive i a x] at h
      linarith

theorem integral_squared_contraction {d : ℕ} (i : Fin d) (a : ℝ) {f g : Torus d → ℝ}
    (hf : MemLp f 2 (torusMeasure d)) (hg : MemLp g 2 (torusMeasure d)) :
    (∫ x,(polarize i a f x-polarize i a g x)^2 ∂torusMeasure d)≤
      ∫ x,(f x-g x)^2 ∂torusMeasure d := by
  have hraw := hf.sub hg
  have hpol := (polarize_memLp_two i a hf).sub (polarize_memLp_two i a hg)
  have hi := (memLp_two_iff_integrable_sq hraw.aestronglyMeasurable).mp hraw
  have hp := (memLp_two_iff_integrable_sq hpol.aestronglyMeasurable).mp hpol
  have h := integral_mono (hp.add (reflection_integrable i a hp))
    (hi.add (reflection_integrable i a hi)) (pair_squared_distance_le i a f g)
  simp only [Pi.add_apply] at h
  rw [integral_add hp (reflection_integrable i a hp),
    integral_add hi (reflection_integrable i a hi)] at h
  have hep := reflection_integral i a (fun x => (polarize i a f x-polarize i a g x)^2)
  have hei := reflection_integral i a (fun x => (f x-g x)^2)
  simp only [Pi.sub_apply] at h
  rw [hep,hei] at h
  linarith

def polarizeLp {d : ℕ} (i : Fin d) (a : ℝ) (f : DensityL2 d) : DensityL2 d :=
  (polarize_memLp_two i a (Lp.memLp f)).toLp (polarize i a f)

theorem polarizeLp_ae {d : ℕ} (i : Fin d) (a : ℝ) (f : DensityL2 d) :
    polarizeLp i a f =ᵐ[torusMeasure d] polarize i a f := MemLp.coeFn_toLp _

theorem polarizeLp_lipschitz {d : ℕ} (i : Fin d) (a : ℝ) : LipschitzWith 1 (polarizeLp i a) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  have h := integral_squared_contraction i a (Lp.memLp f) (Lp.memLp g)
  change (∫ x, (polarize i a (f : Torus d → ℝ)-polarize i a (g : Torus d → ℝ)) x ^ 2 ∂torusMeasure d) ≤
    ∫ x, ((f : Torus d → ℝ)-(g : Torus d → ℝ)) x ^ 2 ∂torusMeasure d at h
  rw [ExponentialPartitionContinuity.integral_sq_toLp
      ((polarize_memLp_two i a (Lp.memLp f)).sub (polarize_memLp_two i a (Lp.memLp g))),
    ExponentialPartitionContinuity.integral_sq_toLp ((Lp.memLp f).sub (Lp.memLp g)),
    MemLp.toLp_sub (polarize_memLp_two i a (Lp.memLp f)) (polarize_memLp_two i a (Lp.memLp g)),
    MemLp.toLp_sub (Lp.memLp f) (Lp.memLp g)] at h
  have hf : (Lp.memLp f).toLp f=f := Lp.ext (MemLp.coeFn_toLp _)
  have hg : (Lp.memLp g).toLp g=g := Lp.ext (MemLp.coeFn_toLp _)
  rw [hf,hg] at h
  change ‖polarizeLp i a f-polarizeLp i a g‖^2≤‖f-g‖^2 at h
  simp only [dist_eq_norm,NNReal.coe_one,one_mul]
  nlinarith [norm_nonneg (polarizeLp i a f-polarizeLp i a g),norm_nonneg (f-g)]

#print axioms polarizeLp_lipschitz
end BecknerOnofri.PolarizationL2
