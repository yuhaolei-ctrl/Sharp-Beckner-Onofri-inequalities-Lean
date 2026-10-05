import Legacy.BecknerOnofri.GreenHeatIntegrability
import Legacy.BecknerOnofri.GreenHeatFourier
import Legacy.BecknerOnofri.GreenRoughEnergy

/-! The actual Fourier Green kernel has every subcritical exponential moment.
The heat-Mellin representative is identified by L2 Fourier uniqueness first.
-/
namespace Legacy.BecknerOnofri.GreenExponentialIntegrability
open MeasureTheory Legacy.TorusEndpoint GreenKernelReal GreenHeatPointwise

theorem heatGreen_eq_realGreen_ae {d : ℕ} (hd : 0 < d) :
    (@heatGreen d) =ᵐ[torusMeasure d] realGreen d := by
  have hg := heatGreen_memLp hd
  let G := hg.ofReal.toLp (fun x => (heatGreen x : ℂ))
  have he : G = GreenMultiplierSummability.greenL2 d := by
    apply greenL2_unique
    intro k
    exact (GreenPairing.fourierCoeff_real_toLp hg k).trans (heatGreen_fourier hd k)
  have hae : G =ᵐ[torusMeasure d] (fun x => (heatGreen x : ℂ)) := hg.ofReal.coeFn_toLp
  rw [he] at hae
  filter_upwards [hae] with x hx
  exact (congrArg Complex.re hx).symm

/-- The coefficient range is sharp at the logarithmic singularity; this
theorem asserts integrability only strictly below it. -/
theorem realGreen_exp_integrable {d : ℕ} (hd : 0 < d)
    {a : ℝ} (ha : 0 ≤ a) (had : a < d) :
    Integrable (fun x => Real.exp (a * realGreen d x)) (torusMeasure d) := by
  apply (heatGreen_exp_integrable hd ha had).congr
  filter_upwards [heatGreen_eq_realGreen_ae hd] with x hx
  rw [hx]

theorem kernel_exp_integrable {d : ℕ} (hd : 0 < d)
    {b : ℝ} (hb : 0 ≤ b) (hbd : b < endpointConstant d) :
    Integrable (fun x => Real.exp (b * GreenRoughEnergy.kernel d x)) (torusMeasure d) := by
  have hs := endpointSigma_pos hd
  have had : b * endpointSigma d < d := (lt_div_iff₀ hs).mp hbd
  simpa only [GreenRoughEnergy.kernel, mul_assoc] using
    realGreen_exp_integrable hd (mul_nonneg hb hs.le) had

theorem kernel_partition_pos {d : ℕ} (hd : 0 < d)
    {b : ℝ} (hb : 0 ≤ b) (hbd : b < endpointConstant d) :
    0 < GreenRoughEnergy.partition d b :=
  integral_exp_pos (kernel_exp_integrable hd hb hbd)

theorem rough_energy {d : ℕ} (hd : 0 < d)
    (r : ProbabilityDensity d) (hr : MemLp r.value 2 (torusMeasure d))
    {b : ℝ} (hb : 0 ≤ b) (hbd : b < endpointConstant d) :
    b * fourierEnergy r ≤ densityEntropy r.value + Real.log (GreenRoughEnergy.partition d b) :=
  GreenRoughEnergy.rough_energy hd r hr b (kernel_exp_integrable hd hb hbd)

#print axioms heatGreen_eq_realGreen_ae
#print axioms kernel_exp_integrable
#print axioms rough_energy
end Legacy.BecknerOnofri.GreenExponentialIntegrability
