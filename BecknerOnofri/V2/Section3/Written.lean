module

public import BecknerOnofri.V2.Section3.MixtureCountable

@[expose] public section

/-! # The two hypotheses of Lemma 3.1 on the manuscript's class, by the written route (G04)

`mixtureInequality_written` and `mixtureStrictness_written` prove, for `2 ≤ d ≤ 10`,

* `MixtureInequality d`: `Ent ρ ≥ d c_d ‖ρ‖²` for **every** finite-entropy countable cosine-power
  mixture (no majorant, no smoothness, no positivity);
* `MixtureStrictness d`: strict for every nonuniform one;

by the argument of Subsections 3.3 to 3.5 of the manuscript: the conditional hypergeometric draws
(`MixtureFinite.lean`), the harmonic identity, Proposition 3.4 with the mixed-index average, the
chain-rule / Lemma 3.2 bound `eq:circle-marginal-fourier-control` (`Marginal.lean`), the passage to
countable mixtures by monotone convergence (`MixtureCountable.lean`), and positivity of the latent
positive-index probability for nonuniform mixtures.  No declaration of the legacy module
`Legacy.BecknerOnofri.LowDimensionMixtureEndpoint` is used. -/

noncomputable section
open Finset Filter MeasureTheory
open scoped BigOperators ENNReal

namespace BecknerOnofri.V2.Section3
open BecknerOnofri.HighDim BecknerOnofri.V2.Vocab
open Legacy.D10 (latentBox latentWeight latentWeight_nonneg)
open Legacy.BecknerOnofri

variable {d : ℕ}

theorem posMass_nonneg {α : Type*} (s : Finset α) (w : α → ℝ) (N : α → Fin d → ℕ)
    (hw : ∀ a ∈ s, 0 ≤ w a) : 0 ≤ posMass s w N := by
  have h := latAvg_mono s w N hw (F := fun _ => (0 : ℝ))
    (G := fun L => ∑ i, (if 1 ≤ L i then (1 : ℝ) else 0))
    (fun L => sum_nonneg fun i _ => by split_ifs <;> norm_num)
  rwa [latAvg_const, zero_mul] at h

theorem latentWeight_self_pos' (N : Fin d → ℕ) : 0 < latentWeight N N N := by
  unfold Legacy.D10.latentWeight
  apply prod_pos
  intro i _
  unfold Legacy.D10.hypergeometricWeightReal Legacy.D10.hypergeometricWeight
  have hc : 0 < (N i + N i).choose (N i) := Nat.choose_pos (by omega)
  norm_cast
  simp only [Nat.choose_self, Nat.cast_one, mul_one]
  exact div_pos (by norm_num) (Nat.cast_pos.mpr hc)

theorem mem_latentBox_self' (N : Fin d → ℕ) : N ∈ latentBox N := by
  simp [Legacy.D10.latentBox]

/-- A single positive-weight component with a nonzero index gives the latent positive-index mass a
positive lower bound (independence of the two entire draws `N, M`). -/
theorem posMass_lower {α : Type*} (s : Finset α) (w : α → ℝ) (N : α → Fin d → ℕ)
    (hw : ∀ a ∈ s, 0 ≤ w a) {a : α} (ha : a ∈ s) (hNa : N a ≠ 0) :
    w a * w a * latentWeight (N a) (N a) (N a) ≤ posMass s w N := by
  unfold posMass latAvg
  have hT (a' b : α) (ha' : a' ∈ s) (hb : b ∈ s) (L : Fin d → ℕ) :
      0 ≤ w a' * w b * latentWeight (N a') (N b) L *
        ∑ i, (if 1 ≤ L i then (1 : ℝ) else 0) :=
    mul_nonneg (mul_nonneg (mul_nonneg (hw a' ha') (hw b hb)) (latentWeight_nonneg _ _ _))
      (sum_nonneg fun i _ => by split_ifs <;> norm_num)
  have hF : (1 : ℝ) ≤ ∑ i, (if 1 ≤ N a i then (1 : ℝ) else 0) := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hNa
    have hi1 : 1 ≤ N a i := Nat.one_le_iff_ne_zero.mpr hi
    have := Finset.single_le_sum (f := fun i => (if 1 ≤ N a i then (1 : ℝ) else 0))
      (fun i _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
    simpa [hi1] using this
  have hnn : 0 ≤ w a * w a * latentWeight (N a) (N a) (N a) :=
    mul_nonneg (mul_nonneg (hw a ha) (hw a ha)) (latentWeight_nonneg _ _ _)
  calc w a * w a * latentWeight (N a) (N a) (N a)
      ≤ w a * w a * latentWeight (N a) (N a) (N a) * ∑ i, (if 1 ≤ N a i then (1 : ℝ) else 0) :=
        le_mul_of_one_le_right hnn hF
    _ ≤ ∑ L ∈ latentBox (N a), w a * w a * latentWeight (N a) (N a) L *
          ∑ i, (if 1 ≤ L i then (1 : ℝ) else 0) :=
        Finset.single_le_sum (f := fun L => w a * w a * latentWeight (N a) (N a) L *
          ∑ i, (if 1 ≤ L i then (1 : ℝ) else 0)) (fun L _ => hT a a ha ha L)
          (mem_latentBox_self' (N a))
    _ ≤ ∑ b ∈ s, ∑ L ∈ latentBox (N a), w a * w b * latentWeight (N a) (N b) L *
          ∑ i, (if 1 ≤ L i then (1 : ℝ) else 0) :=
        Finset.single_le_sum (f := fun b => ∑ L ∈ latentBox (N a),
          w a * w b * latentWeight (N a) (N b) L * ∑ i, (if 1 ≤ L i then (1 : ℝ) else 0))
          (fun b hb => sum_nonneg fun L _ => hT a b ha hb L) ha
    _ ≤ _ :=
        Finset.single_le_sum (f := fun a' => ∑ b ∈ s, ∑ L ∈ latentBox (N a'),
          w a' * w b * latentWeight (N a') (N b) L * ∑ i, (if 1 ≤ L i then (1 : ℝ) else 0))
          (fun a' ha' => sum_nonneg fun b hb => sum_nonneg fun L _ => hT a' b ha' hb L) ha

/-- The real-number form of the normalisation: `d c_d ‖ρ‖² = (d/β_s(d)) · (spectral energy)`. -/
theorem energy_toReal_eq (hd : 0 < d) (ρ : ProbabilityDensity d) :
    (d : ℝ) * kernelConstant d * (negSobolevEnergy ρ.value).toReal =
      Legacy.BecknerOnofri.endpointConstant d * (spectralEnergy ρ).toReal := by
  have hkey := kernelConstant_mul_negSobolevEnergy_toReal hd ρ
  rw [mul_assoc, hkey]
  have hc : Legacy.BecknerOnofri.endpointConstant d = (d : ℝ) / spectralThreshold d := rfl
  rw [hc]
  ring

/-- A mixture all of whose positive-weight components are the constant `h_0 ⊗ ... ⊗ h_0 = 1` is
uniform. -/
theorem rho_uniform_of_no_component (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n)
    (hm : HasSum w 1) (hn : ∀ n, 0 < w n → N n = 0) (x : Torus d) :
    CosineMixtureApproximation.rho w N x = 1 := by
  unfold CosineMixtureApproximation.rho
  have heq : (fun n => w n * CosineMixture.tensor (N n) x) = w := by
    funext n
    by_cases h : w n = 0
    · simp [h]
    · rw [hn n (lt_of_le_of_ne (hw n) (Ne.symm h))]
      simp only [Pi.zero_def, CosineMixtureApproximation.tensor_zero_index, mul_one]
  rw [heq, hm.tsum_eq]

/-- **The mixture inequality (first hypothesis of Lemma 3.1), written route, `2 ≤ d ≤ 10`.** -/
theorem mixtureInequality_written (hd2 : 2 ≤ d) (hd10 : d ≤ 10) : MixtureInequality d := by
  intro ρ hρ hmix
  obtain ⟨w, N, hw, hm, he⟩ := hmix
  have he' : ρ.value =ᵐ[torusMeasure d] CosineMixtureApproximation.rho w N := he
  have hd0 : 0 < d := by omega
  obtain ⟨-, h⟩ := mixture_energy_gap hd2 hd10 ρ hρ w N hw hm he' 0
    (Eventually.of_forall fun m => posMass_nonneg _ w N fun a _ => hw a)
  unfold EntropyBound
  rw [energy_toReal_eq hd0 ρ, ← entropy_eq_toReal_torusEntropy ρ hρ]
  linarith

/-- **The mixture strictness (second hypothesis of Lemma 3.1), written route, `2 ≤ d ≤ 10`.** -/
theorem mixtureStrictness_written (hd2 : 2 ≤ d) (hd10 : d ≤ 10) : MixtureStrictness d := by
  intro ρ hρ hmix hnon
  obtain ⟨w, N, hw, hm, he⟩ := hmix
  have he' : ρ.value =ᵐ[torusMeasure d] CosineMixtureApproximation.rho w N := he
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hcomp : ∃ a, 0 < w a ∧ N a ≠ 0 := by
    by_contra hno
    push Not at hno
    apply hnon
    filter_upwards [he'] with x hx
    rw [hx]
    exact rho_uniform_of_no_component w N hw hm hno x
  obtain ⟨a, ha, hNa⟩ := hcomp
  have hγpos : 0 < w a * w a * latentWeight (N a) (N a) (N a) :=
    mul_pos (mul_pos ha ha) (latentWeight_self_pos' _)
  have hγ : ∀ᶠ m in atTop, w a * w a * latentWeight (N a) (N a) (N a) ≤ posMass (range m) w N := by
    filter_upwards [eventually_ge_atTop (a + 1)] with m hm'
    exact posMass_lower (range m) w N (fun a _ => hw a) (mem_range.mpr (by omega)) hNa
  obtain ⟨-, h⟩ := mixture_energy_gap hd2 hd10 ρ hρ w N hw hm he' _ hγ
  have hg : 0 < 3 / (1100 * (d : ℝ)) := by positivity
  unfold EntropyStrict
  rw [energy_toReal_eq hd0 ρ, ← entropy_eq_toReal_torusEntropy ρ hρ]
  nlinarith [mul_pos hg hγpos]

#print axioms mixtureInequality_written
#print axioms mixtureStrictness_written

end BecknerOnofri.V2.Section3
