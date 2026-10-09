module

public import BecknerOnofri.V2.Section3.Lemma31
public import BecknerOnofri.V2.Section3.LegacyBridge
public import Legacy.D10.CircleEntropy

@[expose] public section

/-! # The circle `d = 1` of Theorem 1.1: the entropy and potential bounds (G04)

`d = 1` is *not* obtained from the rigidity argument of Lemma 3.1 (which is false there: the
Lebedev--Milin equality family is nonconstant).  Instead:

* the entropy bound `Ent ρ ≥ c_1 ‖ρ‖²_{Ḣ^{-1/2}}` on the full finite-entropy domain is Lemma 3.2 with
  `d = 1` (`Legacy.D10.CircleEntropy.entropy_bound`), translated to the manuscript normalization;
* `P_1(2) = 0`, `C_1(A_c(1)) = 0` and the potential inequality follow by the same duality as in
  Lemma 3.1 (`..._of_full`);
* the equality classification (Poisson kernels, resp. the logarithms `-2 log |1 - \bar a e^{2πix}| + c`)
  is the repository's circle theorem `CircleEquality.{density,onofri}_equality_iff_paper_family`,
  translated to the manuscript normalization (it is *nonconstant*, and nothing from `d ≥ 2` is used).
 -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology ComplexConjugate

namespace BecknerOnofri.V2.Section3
open BecknerOnofri.HighDim BecknerOnofri.V2.Vocab

/-- Lemma 3.2 for the circle, in the manuscript normalization: `Ent ρ ≥ c_1 ‖ρ‖²` for every
finite-entropy density on `𝕋`. -/
theorem circle_entropy_bound (ρ : ProbabilityDensity 1) (hρ : ρ.FiniteEntropy) :
    EntropyBound 1 ρ := by
  obtain ⟨hsum, hbound⟩ := Legacy.D10.CircleEntropy.entropy_bound (Bridge.density ρ) hρ
  have hterm : Legacy.TorusEndpoint.densitySpectralTerm (Bridge.density ρ) =
      fun k : Legacy.TorusEndpoint.NonzeroFrequency 1 =>
        Legacy.D10.CircleEntropy.weight k.val *
          ‖Legacy.TorusEndpoint.densityFourier (Bridge.density ρ).value k.val‖ ^ 2 :=
    funext (Legacy.BecknerOnofri.circle_energyTerm (Bridge.density ρ))
  have hsum' : Summable (Legacy.TorusEndpoint.densitySpectralTerm (Bridge.density ρ)) := by
    rw [hterm]; exact hsum
  have h1 := energy_real_eq_legacy (d := 1) (by norm_num) ρ (Bridge.density ρ)
    (Filter.EventuallyEq.rfl) hsum'
  have h2 := entropy_real_eq_legacy ρ hρ (Bridge.density ρ) (Filter.EventuallyEq.rfl)
  unfold EntropyBound
  rw [h1, h2]
  have hc : Legacy.BecknerOnofri.endpointConstant 1 = 1 / 2 := Legacy.BecknerOnofri.endpointConstant_one
  rw [hc]
  unfold Legacy.BecknerOnofri.fourierEnergy
  rw [hterm]
  change 1 / 2 * _ ≤ Legacy.TorusEndpoint.densityEntropy (Bridge.density ρ).value
  linarith

/-- `P_1(2) = 0`. -/
theorem circle_pressure_two : pressure 1 (2 * ((1 : ℕ) : ℝ)) = 0 :=
  pressure_two_d_eq_zero_of_full (by norm_num) (fun ρ hρ => circle_entropy_bound ρ hρ)

/-- Lebedev--Milin: the potential inequality on the circle with the coefficient `A_c(1)`. -/
theorem circle_potential_bound (u : Torus 1 → ℝ) (hu : InCriticalSobolev u) :
    Integrable (fun x => Real.exp (centered u x)) (torusMeasure 1) ∧
      logPartition u ≤ ((collapseCoefficient 1 * potentialEnergy u : ℝ) : EReal) :=
  potential_bound_of_full (by norm_num) (fun ρ hρ => circle_entropy_bound ρ hρ) u hu

end BecknerOnofri.V2.Section3
