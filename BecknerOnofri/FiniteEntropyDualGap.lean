module

public import BecknerOnofri.FiniteEntropyGreenSobolev
public import BecknerOnofri.GenericAttainment
public import Legacy.BecknerOnofri.SubcriticalPrimalDual

@[expose] public section

/-! The literal relative-entropy gap on the full finite-entropy density domain.
The potential is the actual Green convolution, represented in the Fourier L2 space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
namespace BecknerOnofri.FiniteEntropyGreen
open Legacy.TorusEndpoint Legacy.BecknerOnofri TorusSobolev
open SubcriticalAttainment SubcriticalEuler SubcriticalPrimalDual

lemma relative_entropy_gibbs {d : ℕ} {b Ab : ℝ} (hR : RoughExponentialBound d b Ab)
    (r : ProbabilityDensity d) (hr : r.FiniteEntropy) (u : TorusL2 d) (hu : Admissible u)
    (hp : Integrable (fun x => r.value x*(u x).re) (torusMeasure d)) :
    Integrable (fun x => r.value x*Real.log (r.value x/gibbsValue u x)) (torusMeasure d) ∧
    (∫ x,r.value x*Real.log (r.value x/gibbsValue u x) ∂torusMeasure d) =
      densityEntropy r.value-(∫ x,r.value x*(u x).re ∂torusMeasure d)+Real.log (partition u) := by
  have he (x : Torus d) : r.value x*Real.log (r.value x/gibbsValue u x) =
      r.value x*Real.log (r.value x)-r.value x*(u x).re+r.value x*Real.log (partition u) := by
    by_cases hx : r.value x = 0
    · simp [hx]
    · rw [Real.log_div hx (gibbsValue_pos hR hu x).ne',log_gibbsValue hR hu]
      ring
  have hsub : Integrable (fun x => r.value x*Real.log (r.value x)-r.value x*(u x).re)
      (torusMeasure d) := hr.sub hp
  have hi := hsub.add (r.integrable.mul_const (Real.log (partition u)))
  have hefun : (fun x => r.value x*Real.log (r.value x/gibbsValue u x)) =
      fun x => r.value x*Real.log (r.value x)-r.value x*(u x).re+r.value x*Real.log (partition u) :=
    funext he
  refine ⟨by simpa only [hefun,Pi.add_apply,Pi.sub_apply] using! hi,?_⟩
  rw [hefun,integral_add hsub (r.integrable.mul_const _),integral_sub hr hp,
    integral_mul_const,r.mass,one_mul]
  rfl

def dualPotential {d : ℕ} (hd : 0 < d) (A : ℝ) (r : ProbabilityDensity d)
    (hr : r.FiniteEntropy) : TorusL2 d :=
  ((1/(2*A) : ℝ) : ℂ) • potentialLp hd r hr

lemma dualPotential_admissible {d : ℕ} (hd : 0 < d) (A : ℝ) (r : ProbabilityDensity d)
    (hr : r.FiniteEntropy) : Admissible (dualPotential hd A r hr) :=
  admissible_smul_real (potentialLp_admissible hd r hr) _

lemma dualPotential_ae {d : ℕ} (hd : 0 < d) (A : ℝ) (r : ProbabilityDensity d)
    (hr : r.FiniteEntropy) : (fun x => (dualPotential hd A r hr x).re) =ᵐ[torusMeasure d]
      fun x => (1/(2*A))*GreenRoughEnergy.potential r x := by
  filter_upwards [Lp.coeFn_smul ((1/(2*A):ℝ):ℂ) (potentialLp hd r hr),
    potentialLp_ae hd r hr] with x hx hg
  change (dualPotential hd A r hr x).re = _
  rw [dualPotential,hx]
  simp only [Pi.smul_apply,smul_eq_mul,hg,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    mul_zero,sub_zero]

lemma dualPotential_pair_integrable {d : ℕ} (hd : 0 < d) (A : ℝ) (r : ProbabilityDensity d)
    (hr : r.FiniteEntropy) :
    Integrable (fun x => r.value x*(dualPotential hd A r hr x).re) (torusMeasure d) := by
  apply ((pairing_integrable hd r hr).const_mul (1/(2*A))).congr
  filter_upwards [dualPotential_ae hd A r hr] with x hx
  rw [hx]
  ring

lemma dualPotential_pairing {d : ℕ} (hd : 0 < d) (A : ℝ) (r : ProbabilityDensity d)
    (hr : r.FiniteEntropy) : (∫ x,r.value x*(dualPotential hd A r hr x).re ∂torusMeasure d) =
      (1/(2*A))*fourierEnergy r := by
  calc
    _ = ∫ x,(1/(2*A))*(r.value x*GreenRoughEnergy.potential r x) ∂torusMeasure d := by
      apply integral_congr_ae
      filter_upwards [dualPotential_ae hd A r hr] with x hx
      rw [hx]
      ring
    _ = _ := by rw [integral_const_mul,pairing_eq_fourier hd r hr]

/-- The full density-side gap identity, with the integral relative entropy remainder. -/
theorem dual_gap_identity {d : ℕ} (hd : 0 < d) {A : ℝ} (hA : 0 < A)
    (r : ProbabilityDensity d) (hr : r.FiniteEntropy) :
    densityFunctional A r = functional A (dualPotential hd A r hr) -
      ∫ x,r.value x*Real.log (r.value x/gibbsValue (dualPotential hd A r hr) x) ∂torusMeasure d := by
  have hC : 0 < endpointConstant d := div_pos (Nat.cast_pos.mpr hd) (endpointSigma_pos hd)
  have hR := GenericAttainment.rough_bound hd (by positivity : 0 < endpointConstant d/2)
    (by linarith : endpointConstant d/2 < endpointConstant d)
  have hrel := (relative_entropy_gibbs hR r hr _ (dualPotential_admissible hd A r hr)
    (dualPotential_pair_integrable hd A r hr)).2
  rw [dualPotential_pairing hd A r hr] at hrel
  rw [hrel,functional,densityFunctional,dualPotential,criticalEnergy_smul_real,potentialLp_energy hd r hr]
  field_simp
  <;> ring

#print axioms relative_entropy_gibbs
#print axioms dual_gap_identity
end BecknerOnofri.FiniteEntropyGreen
