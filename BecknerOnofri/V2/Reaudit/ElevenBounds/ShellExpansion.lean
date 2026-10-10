module

public import BecknerOnofri.V2.Eleven.Estimates
public import BecknerOnofri.ElevenCompetitorEnergy

@[expose] public section

/-! # S029: the full infinite shell expansion `eq:section4-shell-expansion`

`(2π)^{11} ‖ρ_*‖²_{Ḣ^{-11/2}} = ∑_{m ≥ 1} r_{11}(m) m^{-11/2} Φ(2π√m/5)²`, with
`r_d(q) = #{k ∈ ℤ^d : |k|² = q}` (`eq:section4-shell-multiplicity`).

This is the equality of the *full* lattice sum with the sum over shells: by Tonelli (here in the form
`ENNReal.tsum_fiberwise` for the fibres of `k ↦ |k|²`; every fibre is finite, with `r_d(q)` elements) the
lattice sum `∑_{k ≠ 0} |k|^{-11} |ρ̂_*(k)|²`, whose summand depends on `k` only through `|k|²` by
`eq:section4-rho-star-fourier`, is regrouped into shells.  The finite lower certificate
(`Shell.certified_finite_energy`: the one hundred shells, `10^{20}` root scale, `10^{12}` rounding) is then
attached to the infinite identity in `energy_bound_via_shells` ("omitting all terms with `m > 100`"). -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal

namespace BecknerOnofri.V2.Reaudit.ElevenBounds

open BecknerOnofri.HighDim

/-- `|k|² = ∑ k_i²` of an integer frequency vector, as a natural number. -/
def sqNorm (d : ℕ) (k : Frequency d) : ℕ := ∑ i, (k i).natAbs ^ 2

/-- **`eq:section4-shell-multiplicity`**: `r_d(q) = #{k ∈ ℤ^d : |k|² = q}`. -/
def shellMultiplicity (d q : ℕ) : ℕ := Set.ncard {k : Frequency d | ∑ i, (k i) ^ 2 = (q : ℤ)}

theorem sqNorm_cast_int (d : ℕ) (k : Frequency d) : ((sqNorm d k : ℕ) : ℤ) = ∑ i, (k i) ^ 2 := by
  simp only [sqNorm, Nat.cast_sum, Nat.cast_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Int.natAbs_sq (k i) ▸ by simp [sq]

theorem sqNorm_cast_real (d : ℕ) (k : Frequency d) :
    ((sqNorm d k : ℕ) : ℝ) = ∑ i, ((k i : ℤ) : ℝ) ^ 2 := by
  have h := congrArg (fun z : ℤ => (z : ℝ)) (sqNorm_cast_int d k)
  simpa using h

theorem frequencyLength_eq_sqrt (d : ℕ) (k : Frequency d) :
    frequencyLength k = Real.sqrt (sqNorm d k : ℕ) := by
  rw [frequencyLength, sqNorm_cast_real]

theorem shell_set_eq (d q : ℕ) :
    {k : Frequency d | ∑ i, (k i) ^ 2 = (q : ℤ)} = sqNorm d ⁻¹' {q} := by
  ext k
  simp only [mem_ofPred_eq, mem_preimage, mem_singleton_iff]
  rw [← sqNorm_cast_int]
  exact_mod_cast Iff.rfl

theorem shell_finite (d q : ℕ) : (sqNorm d ⁻¹' {q}).Finite := by
  refine (Finset.finite_toSet (Fintype.piFinset fun _ : Fin d => Finset.Icc (-(q : ℤ)) q)).subset ?_
  intro k hk
  simp only [mem_preimage, mem_singleton_iff] at hk
  simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have h1 : (k i).natAbs ^ 2 ≤ q := by
    rw [← hk]
    exact Finset.single_le_sum (f := fun i => (k i).natAbs ^ 2) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  have h2 : (k i).natAbs ≤ q := (Nat.le_self_pow (by norm_num) _).trans h1
  omega

theorem shellMultiplicity_eq_ncard (d q : ℕ) :
    shellMultiplicity d q = (sqNorm d ⁻¹' {q}).ncard := by
  unfold shellMultiplicity
  rw [shell_set_eq]

/-- **Tonelli for the shell decomposition**: a nonnegative function of `|k|²` summed over all of `ℤ^d`
is the sum over shells `q` of `r_d(q)` times the value on the shell. -/
theorem tsum_frequency_eq_tsum_shell (d : ℕ) (f : ℕ → ℝ≥0∞) :
    ∑' k : Frequency d, f (sqNorm d k) = ∑' q : ℕ, (shellMultiplicity d q : ℝ≥0∞) * f q := by
  rw [← ENNReal.tsum_fiberwise (fun k : Frequency d => f (sqNorm d k)) (sqNorm d)]
  refine tsum_congr fun q => ?_
  have h1 : ∀ k : ↥(sqNorm d ⁻¹' {q}), f (sqNorm d k.1) = f q := fun k => by
    have := k.2
    simp only [mem_preimage, mem_singleton_iff] at this
    rw [this]
  simp_rw [h1]
  rw [ENNReal.tsum_const, shellMultiplicity_eq_ncard]
  congr 1
  have hfin := shell_finite d q
  have : ENat.card ↑(sqNorm d ⁻¹' {q}) = ((sqNorm d ⁻¹' {q}).ncard : ℕ∞) :=
    (Set.Finite.cast_ncard_eq hfin).symm
  rw [this]
  simp

/-! ## The expansion for `ρ_*` -/

open HighDim.Eleven (Shell.weight Shell.weight_nonneg Shell.weight_zero)

/-- **`eq:section4-shell-expansion`, in `ℝ≥0∞`.** For the density `ρ_*`,
`∑_{k≠0} |k|^{-11}|ρ̂_*(k)|² = ∑_{q≥0} r_{11}(q) · (√q^{11})⁻¹ Φ(2π√q/5)²` (the `q = 0` term is zero).
No finiteness is assumed. -/
theorem spectralEnergy_eq_tsum_shell (ρ : ProbabilityDensity 11)
    (hρ : ρ.value = HighDim.Eleven.periodizedProfile) :
    spectralEnergy ρ = ∑' q : ℕ, ENNReal.ofReal ((shellMultiplicity 11 q : ℝ) * Shell.weight q) := by
  let g : Frequency 11 → ℝ≥0∞ := fun k =>
    ENNReal.ofReal ((frequencyLength k ^ 11)⁻¹ * ‖fourierCoeff ρ.value k‖ ^ 2)
  have hz : g 0 = 0 := by simp [g, frequencyLength]
  have hs : Function.support g ⊆ {k : Frequency 11 | k ≠ 0} := by
    intro k hk hk0
    exact hk (hk0 ▸ hz)
  have ht : (∑' k : Frequency 11, g k) = spectralEnergy ρ :=
    (tsum_subtype_eq_of_support_subset hs).symm
  have he (k : Frequency 11) : g k = ENNReal.ofReal (Shell.weight (sqNorm 11 k)) := by
    dsimp only [g, Shell.weight]
    rw [hρ, HighDim.Eleven.periodizedProfile_fourier, frequencyLength_eq_sqrt]
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [← ht]
  simp_rw [he]
  rw [tsum_frequency_eq_tsum_shell 11 (fun q => ENNReal.ofReal (Shell.weight q))]
  refine tsum_congr fun q => ?_
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

theorem rpow_neg_half_eleven (x : ℝ) (hx : 0 ≤ x) :
    x ^ (-(11 / 2 : ℝ)) = ((Real.sqrt x) ^ 11)⁻¹ := by
  rw [Real.rpow_neg hx, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

/-- The shell expansion with the weights `Shell.weight m = (√m^{11})⁻¹ Φ(2π√m/5)²` of the repository's
finite certificate: `(2π)^{11}‖ρ_*‖²_{Ḣ^{-11/2}} = ∑_{m≥1} r_{11}(m) weight(m)`. -/
theorem hasSum_shell_weight (ρ : ProbabilityDensity 11)
    (hρ : ρ.value = HighDim.Eleven.periodizedProfile) :
    HasSum (fun m : ℕ => (shellMultiplicity 11 (m + 1) : ℝ) * Shell.weight (m + 1))
      ((2 * Real.pi) ^ 11 * (Vocab.negSobolevEnergy ρ.value).toReal) := by
  have hfin : spectralEnergy ρ ≠ ⊤ :=
    finiteEntropy_spectralEnergy_ne_top (by norm_num) ρ (Eleven.finiteEntropy_of_value_eq ρ hρ)
  have hE := spectralEnergy_eq_tsum_shell ρ hρ
  have hsum : ∑' q : ℕ, ENNReal.ofReal ((shellMultiplicity 11 q : ℝ) * Shell.weight q) ≠ ⊤ := by
    rw [← hE]; exact hfin
  have h1 := ENNReal.hasSum_toReal hsum
  rw [← ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top), ← hE] at h1
  have h2 : HasSum (fun q : ℕ => (shellMultiplicity 11 q : ℝ) * Shell.weight q)
      (spectralEnergy ρ).toReal := by
    convert h1 using 2 with q
    rw [ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg _) (Shell.weight_nonneg q))]
  have h3 := (hasSum_nat_add_iff' 1).mpr h2
  have hE' : (spectralEnergy ρ).toReal = (2 * Real.pi) ^ 11 * (Vocab.negSobolevEnergy ρ.value).toReal := by
    rw [Vocab.spectralEnergy_eq_mul_negSobolevEnergy, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity)]
  rw [hE'] at h3
  simpa only [Finset.sum_range_one, Shell.weight_zero, mul_zero, sub_zero] using h3

/-- **`eq:section4-shell-expansion`.** For the density `ρ_*`,
`(2π)^{11} ‖ρ_*‖²_{Ḣ^{-11/2}} = ∑_{m≥1} r_{11}(m) m^{-11/2} Φ((2π/5)√m)²`
(the series of nonnegative terms converges, with this sum). -/
theorem hasSum_shell_expansion (ρ : ProbabilityDensity 11)
    (hρ : ρ.value = HighDim.Eleven.periodizedProfile) :
    HasSum (fun m : ℕ => (shellMultiplicity 11 (m + 1) : ℝ) * (((m + 1 : ℕ) : ℝ) ^ (-(11 / 2 : ℝ)) *
        HighDim.Eleven.fourierProfile (2 * Real.pi / 5 * Real.sqrt ((m + 1 : ℕ) : ℝ)) ^ 2))
      ((2 * Real.pi) ^ 11 * (Vocab.negSobolevEnergy ρ.value).toReal) := by
  convert hasSum_shell_weight ρ hρ using 2 with m
  simp only [Shell.weight]
  rw [rpow_neg_half_eleven _ (Nat.cast_nonneg _)]
  have : 2 * Real.pi / 5 * Real.sqrt ((m + 1 : ℕ) : ℝ) = 2 * Real.pi * Real.sqrt ((m + 1 : ℕ) : ℝ) / 5 := by
    ring
  rw [this]

/-! ## Attaching the finite certificate -/

/-- Every shell contains the `HighDim.Eleven.Shell.thetaPolynomial^11`-many box vectors: the coefficient of `X^m` in
`(∑_{j=-10}^{10} X^{j²})^{11}` is at most `r_{11}(m)` (equality for `m ≤ 100`, not needed). -/
theorem coeff_le_shellMultiplicity (m : ℕ) :
    (((HighDim.Eleven.Shell.thetaPolynomial ^ 11).coeff m : ℕ) : ℝ) ≤ (shellMultiplicity 11 m : ℝ) := by
  rw [HighDim.Eleven.Shell.coefficient_count, shellMultiplicity_eq_ncard]
  have hc : (Finset.univ.filter (fun x : Fin 11 → Fin 21 => HighDim.Eleven.Shell.radius 11 x = m)).card =
      (HighDim.Eleven.Shell.vector 11 '' {x : Fin 11 → Fin 21 | HighDim.Eleven.Shell.radius 11 x = m}).ncard := by
    rw [Set.ncard_image_of_injective _ (HighDim.Eleven.Shell.vector_injective 11), ← Set.ncard_coe_finset]
    congr 1
    ext x
    simp
  rw [hc]
  refine Nat.cast_le.mpr (Set.ncard_le_ncard ?_ (shell_finite 11 m))
  rintro _ ⟨x, hx, rfl⟩
  simp only [mem_preimage, mem_singleton_iff]
  exact hx

/-- **The finite lower certificate attached to the infinite identity** (omitting all terms with
`m > 100`, which are nonnegative): `14475384292906/10^{12} < (2π)^{11}/2 · ‖ρ_*‖²_{Ḣ^{-11/2}}`. -/
theorem energy_bound_via_shells (ρ : ProbabilityDensity 11)
    (hρ : ρ.value = HighDim.Eleven.periodizedProfile) :
    (14475384292906 : ℝ) / 10 ^ 12 <
      (2 * Real.pi) ^ 11 / 2 * (Vocab.negSobolevEnergy ρ.value).toReal := by
  have h := hasSum_shell_weight ρ hρ
  have hle := sum_le_hasSum (Finset.range 100)
    (fun m _ => mul_nonneg (Nat.cast_nonneg _) (Shell.weight_nonneg (m + 1))) h
  have hs : ∑ m ∈ Finset.range 101, (((HighDim.Eleven.Shell.thetaPolynomial ^ 11).coeff m : ℕ) : ℝ) *
        Shell.weight m ≤
      ∑ m ∈ Finset.range 100, (shellMultiplicity 11 (m + 1) : ℝ) * Shell.weight (m + 1) := by
    rw [show (101 : ℕ) = 100 + 1 from rfl, Finset.sum_range_succ', Shell.weight_zero, mul_zero, add_zero]
    exact Finset.sum_le_sum fun m _ =>
      mul_le_mul_of_nonneg_right (coeff_le_shellMultiplicity (m + 1)) (Shell.weight_nonneg _)
  have hc := HighDim.Eleven.Shell.certified_finite_energy
  linarith

end BecknerOnofri.V2.Reaudit.ElevenBounds
