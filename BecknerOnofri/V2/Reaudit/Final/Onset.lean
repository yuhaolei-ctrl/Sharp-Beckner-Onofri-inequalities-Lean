module

public import BecknerOnofri.V2.Reaudit.MorseBott.FullBranch
public import BecknerOnofri.V2.Reaudit.Final.OnsetBranches
public import BecknerOnofri.V2.Reaudit.MorseBott.PressureDifferentiation
public import BecknerOnofri.V2.Reaudit.MorseBott.CosineCorrection
public import BecknerOnofri.V2.Reaudit.SpinChannel.WrittenEndpoint
public import BecknerOnofri.OnsetTransfer
public import BecknerOnofri.V2.Reaudit.MorseBott.OrderParameterV2

@[expose] public section

/-! # Theorem 1.3 and Propositions 5.23--5.24, Corollary 5.25 on the printed route

The three high-dimensional onset statements of `Challenge.lean` are derived here from the
route-aligned pieces of the second pass, not from the earlier conditional onset chain:

* the endpoint inputs of Proposition 5.24 are the conclusions of Corollary 5.8 proved along the
  written dimension transfer (`SpinChannel.onsetEndpointInputs_written`); the global minimizers are
  classified by the Sobolev-smallness / second-variation route of `V2/Onset`
  (`V2.Onset.physical_density_classification_v2`);
* the branch is the full-support branch of the profile family `(5.full-branch-profile)`,
  `SupportedFamily.branch univ (1 - β_s/β)`, whose Morse--Bott structure is the embedded critical
  manifold `MorseBott.EmbeddedCriticalOrbit` (Proposition 5.23);
* the global minimizers are the translation orbit of that branch
  (`MorseBott.minimizers_are_profile_branch_orbit`);
* the pressure has the form `(d/(2κ_d)) δ² + δ³ R(δ)` with `R` real analytic at `0`
  (`MorseBott.pressure_common_branch_form`); the pressure onset of Theorem 1.3 and the defect onset
  (`OnsetTransfer.coefficient_onset_of_pressure`) are consequences, and the one-sided derivatives of
  Corollary 5.25 follow by differentiating the analytic remainder
  (`MorseBott.pressure_differentiation_from_remainder`).
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter Set
open scoped Topology

namespace BecknerOnofri.V2.Reaudit.Final.Onset

open BecknerOnofri.HighDim BecknerOnofri.HighDim.LocalEleven

/-- `β ↦ 1 - β_s/β` maps `(β_s, ∞)` near `β_s` into `(0, ∞)` near `0`. -/
theorem onsetDelta_tendsto {d : ℕ} (hd : 0 < d) :
    Tendsto (onsetDelta d) (𝓝[>] (spectralThreshold d)) (𝓝[>] 0) := by
  have hσ : 0 < spectralThreshold d := spectralThreshold_pos hd
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have hc : ContinuousAt (onsetDelta d) (spectralThreshold d) := by
      unfold onsetDelta
      exact continuousAt_const.sub (continuousAt_const.div continuousAt_id hσ.ne')
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (spectralThreshold d)))
    simpa [onsetDelta, hσ.ne'] using this
  · filter_upwards [self_mem_nhdsWithin] with β hβ
    have hβ' : spectralThreshold d < β := hβ
    have h0 : 0 < β := hσ.trans hβ'
    simp only [Set.mem_Ioi, onsetDelta]
    rw [sub_pos, div_lt_one h0]
    exact hβ'

/-- The coupling recovered from the onset variable: `β = β_s / (1 - δ)`. -/
theorem coupling_of_onsetDelta {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : spectralThreshold d < β) :
    (1 / (1 - onsetDelta d β)) * spectralThreshold d = β := by
  have hσ : 0 < spectralThreshold d := spectralThreshold_pos hd
  have h0 : 0 < β := hσ.trans hβ
  unfold onsetDelta
  rw [sub_sub_cancel]
  field_simp

/-- **Pressure onset (Theorem 1.3, `eq:intro-pressure-onset`)** on the printed route. -/
theorem high_dim_pressure_onset_route (d : ℕ) (hd : 12 ≤ d) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧
      ∀ β : ℝ, spectralThreshold d < β → β < spectralThreshold d + ε →
        ∃ p : ℝ, pressure d β = (p : EReal) ∧
          |p - (d : ℝ) / (2 * kappa d) * (1 - spectralThreshold d / β) ^ 2| ≤
            C * (β - spectralThreshold d) ^ 3 := by
  obtain ⟨R, hR, hform⟩ :=
    MorseBott.pressure_common_branch_form hd (SpinChannel.onsetEndpointInputs_written hd)
  have hσ : 0 < spectralThreshold d := spectralThreshold_pos (by omega)
  -- `R` is bounded on a neighbourhood of `0`
  obtain ⟨r, hr, hRb⟩ : ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, |t| < r → |R t| ≤ |R 0| + 1 := by
    have hc : ContinuousAt R 0 := hR.continuousAt
    have := Metric.continuousAt_iff.mp hc 1 one_pos
    obtain ⟨r, hr, h⟩ := this
    refine ⟨r, hr, fun t ht => ?_⟩
    have := h (by simpa [Real.dist_eq] using ht)
    rw [Real.dist_eq] at this
    have := abs_sub_abs_le_abs_sub (R t) (R 0)
    linarith [abs_lt.mp (show |R t - R 0| < 1 from by assumption)]
  obtain ⟨e, he, hBall⟩ := Metric.mem_nhdsWithin_iff.mp hform
  refine ⟨min e (r * spectralThreshold d), (|R 0| + 1) / spectralThreshold d ^ 3, lt_min he
    (mul_pos hr hσ), by positivity, ?_⟩
  intro β hβ hupper
  have hβ0 : 0 < β := hσ.trans hβ
  have hmem : β ∈ Metric.ball (spectralThreshold d) e ∩ Set.Ioi (spectralThreshold d) := by
    refine ⟨?_, hβ⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hβ)]
    have := min_le_left e (r * spectralThreshold d)
    linarith
  have hp := hBall hmem
  refine ⟨_, hp, ?_⟩
  unfold onsetDelta at *
  have hδ0 : 0 ≤ 1 - spectralThreshold d / β := by
    rw [sub_nonneg, div_le_one hβ0]; exact hβ.le
  have hδeq : 1 - spectralThreshold d / β = (β - spectralThreshold d) / β := by field_simp
  have hδle : 1 - spectralThreshold d / β ≤ (β - spectralThreshold d) / spectralThreshold d := by
    rw [hδeq]
    exact div_le_div_of_nonneg_left (by linarith) hσ hβ.le
  have hδr : |1 - spectralThreshold d / β| < r := by
    rw [abs_of_nonneg hδ0]
    refine lt_of_le_of_lt hδle ?_
    rw [div_lt_iff₀ hσ]
    have := min_le_right e (r * spectralThreshold d)
    linarith
  have hRδ := hRb _ hδr
  have h3 := pow_le_pow_left₀ hδ0 hδle 3
  have hsimp : (d : ℝ) / (2 * kappa d) * (1 - spectralThreshold d / β) ^ 2 +
      (1 - spectralThreshold d / β) ^ 3 * R (1 - spectralThreshold d / β) -
      (d : ℝ) / (2 * kappa d) * (1 - spectralThreshold d / β) ^ 2 =
      (1 - spectralThreshold d / β) ^ 3 * R (1 - spectralThreshold d / β) := by ring
  rw [hsimp, abs_mul, abs_of_nonneg (pow_nonneg hδ0 3)]
  calc (1 - spectralThreshold d / β) ^ 3 * |R (1 - spectralThreshold d / β)|
      ≤ (((β - spectralThreshold d) / spectralThreshold d) ^ 3) * (|R 0| + 1) :=
        mul_le_mul h3 hRδ (abs_nonneg _) (by positivity)
    _ = (|R 0| + 1) / spectralThreshold d ^ 3 * (β - spectralThreshold d) ^ 3 := by
        rw [div_pow]; ring

/-- **Defect onset (Theorem 1.3, `eq:intro-C-onset`; Corollary 5.25)** on the printed route. -/
theorem high_dim_defect_onset_route (d : ℕ) (hd : 12 ≤ d) :
    ∃ ε C : ℝ, 0 < ε ∧ ε < spectralCoefficient d ∧ 0 ≤ C ∧
      ∀ A : ℝ, spectralCoefficient d - ε < A → A < spectralCoefficient d →
        ∃ c : ℝ, coefficientDefect d A = (c : EReal) ∧
          |c - (d : ℝ) / (2 * kappa d) * (1 - A / spectralCoefficient d) ^ 2| ≤
            C * (1 - A / spectralCoefficient d) ^ 3 :=
  coefficient_onset_of_pressure (by omega) (high_dim_pressure_onset_route d hd)

/-- **Branch assertions of Theorem 1.3 (Propositions 5.23 and 5.24)** on the printed route: the
family is `U_β = SupportedFamily.branch univ (1 - β_s/β)`, its Morse--Bott structure comes from the
full-support branch analysis, the global minimizers are its translation orbit, and the Sobolev
remainder estimate is the one for the physical branch, transported along the identification of the
two parametrizations of the branch. -/
theorem high_dim_onset_branch_route (d : ℕ) (hd : 12 ≤ d) : FullBranchOnset d := by
  have hd11 : 11 ≤ d := by omega
  have hd0 : 0 < d := by omega
  have E := SpinChannel.onsetEndpointInputs_written hd
  have hphys : ∀ᶠ β in 𝓝[>] (spectralThreshold d),
      SupportedFamily.branch hd11 Finset.univ (onsetDelta d β) =
        DiagonalScalarBranch.physicalPotential hd11 β :=
    (MorseBott.physicalCore_eq_branch hd).mono fun β h => h.symm
  have hMB : ∀ᶠ β in 𝓝[>] (spectralThreshold d),
      FullModeMorseBott β
        (SupportedFamily.branch hd11 Finset.univ (onsetDelta d β) : Torus d → ℝ) := by
    -- Proposition 5.23: the full-mode Morse--Bott property comes from the embedded-critical-orbit theorem
    -- (any Sobolev index `s > d/2` serves; `s = d` is used)
    have hMB0 : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        FullModeMorseBott ((1 / (1 - δ)) * spectralThreshold d)
          (SupportedFamily.branch hd11 Finset.univ δ) := by
      have hdpos : (0 : ℝ) < d := by exact_mod_cast hd0
      exact ((prop_section5_local_branches d hd11).2.2.2.2.2.2.1 (d : ℝ) (by linarith)).mono
        fun δ ⟨_, hmb, _⟩ => hmb
    filter_upwards [(onsetDelta_tendsto hd0).eventually hMB0,
      self_mem_nhdsWithin] with β hβ hβ'
    rwa [coupling_of_onsetDelta hd0 (show spectralThreshold d < β from hβ')] at hβ
  have hAll : ∀ᶠ β in 𝓝[>] (spectralThreshold d),
      (SupportedFamily.branch hd11 Finset.univ (onsetDelta d β) : Torus d → ℝ) =
          (DiagonalScalarBranch.physicalPotential hd11 β : Torus d → ℝ) ∧
      FullModeMorseBott β
        (SupportedFamily.branch hd11 Finset.univ (onsetDelta d β) : Torus d → ℝ) ∧
      (∃ ρ : ProbabilityDensity d, IsGlobalMinimizer β ρ) ∧
      (∀ ρ : ProbabilityDensity d, IsGlobalMinimizer β ρ ↔
        ∃ a : Torus d, ρ.value =ᵐ[torusMeasure d] normalizedGibbs (translate
          (SupportedFamily.branch hd11 Finset.univ (onsetDelta d β) : Torus d → ℝ) a)) := by
    filter_upwards [hphys, hMB, MorseBott.minimizers_are_profile_branch_orbit hd E]
      with β hid hmb hmin
    exact ⟨by rw [hid], hmb, hmin⟩
  obtain ⟨r, hr, hBall⟩ := Metric.mem_nhdsWithin_iff.mp hAll
  refine ⟨r, hr,
    (fun β => (SupportedFamily.branch hd11 Finset.univ (onsetDelta d β) : Torus d → ℝ)), ?_, ?_⟩
  · intro β hβ hupper
    have hmem : β ∈ Metric.ball (spectralThreshold d) r ∩ Set.Ioi (spectralThreshold d) := by
      refine ⟨?_, hβ⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hβ)]
      linarith
    obtain ⟨-, h2, h3, h4⟩ := hBall hmem
    exact ⟨h2, h3, h4⟩
  · intro s _
    obtain ⟨η, C, hη, hηr, hC, hbd⟩ :=
      DiagonalScalarBranch.physical_profile_sobolev_interval hd11 s hr
    refine ⟨η, C, hη, hηr, hC, fun β hβ hupper x₀ => ?_⟩
    have hmem : β ∈ Metric.ball (spectralThreshold d) r ∩ Set.Ioi (spectralThreshold d) := by
      refine ⟨?_, hβ⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hβ)]
      linarith
    obtain ⟨heq, -⟩ := hBall hmem
    beta_reduce
    rw [heq]
    exact hbd β hβ hupper x₀

/-- **Propositions 5.23--5.24 and Corollary 5.25, jointly, on the printed route.**  For `d ≥ 12`:

1. (Proposition 5.23) for every `s > d/2` and all sufficiently small `δ > 0`, the full-support branch
   `u_δ` of `(5.full-branch-profile)` lies in `H^s`, satisfies `FullModeMorseBott` at the coupling
   `β = β_s/(1 - δ)`, and its translation orbit is an embedded critical manifold with Hessian kernel
   equal to the tangent space (`EmbeddedCriticalOrbit`);
2. (displayed cosine correction `eq:section5-full-branch-w2`) for `δ ≥ 0` the quadratic slaving term
   at the leading amplitude is the printed cosine polynomial;
3. (Proposition 5.24) for `β ↓ β_s`, the global minimizers exist and are exactly the Gibbs densities of
   the translates of `u_{1 - β_s/β}`;
4. (Corollary 5.25) the pressure equals `(d/(2κ_d)) δ² + δ³ R(δ)` with `R` real analytic at `0`, and
   the one-sided derivatives satisfy `P' = (d/(κ_d β_s)) δ + O(δ²)`, `P'' = d/(κ_d β_s²) + O(δ)`, with
   limits `0` and `d/(κ_d β_s²)`;
5. (Proposition 5.24, order parameter) one constant bounds `|M(ρ) - √(2d/κ_d) δ^{1/2}| ≤ C δ` over all
   global minimizers, with `M` the first-shell order parameter; and the branch of the order-parameter
   theorem (the derivative family, `physicalPotential`) is, near `β_s`, the branch
   `SupportedFamily.branch univ (1 - β_s/β)` of the adopted reduction. -/
theorem onset_manuscript (d : ℕ) (hd : 12 ≤ d) :
    (∀ s : ℝ, (d : ℝ) / 2 < s → ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ∃ hu : InSobolev s (SupportedFamily.branch (by omega : 11 ≤ d) Finset.univ δ),
        FullModeMorseBott ((1 / (1 - δ)) * spectralThreshold d)
          (SupportedFamily.branch (by omega : 11 ≤ d) Finset.univ δ) ∧
        MorseBott.EmbeddedCriticalOrbit ((1 / (1 - δ)) * spectralThreshold d) s
          (SupportedFamily.branch (by omega : 11 ≤ d) Finset.univ δ) hu) ∧
    (∀ δ : ℝ, 0 ≤ δ → ∀ x₀ x : Torus d,
      ((QuadraticSlaving.quadraticCorrection (by omega : 11 ≤ d)
          (MorseBott.leadingCoordinatesT (δ / kappa d) x₀) : ContinuousFirstShell.complement d) :
          ContinuousGibbs.Space d) (x + x₀) =
        δ / kappa d * ((∑ j, (Complex.re (fourier 2 (x j)))) / ((2 : ℝ) ^ d - 1) +
          4 * (∑ i, ∑ j ∈ Finset.Ioi i, (fourier 1 (x i)).re * (fourier 1 (x j)).re) /
            ((2 : ℝ) ^ ((d : ℝ) / 2) - 1))) ∧
    (∀ᶠ β in 𝓝[>] (spectralThreshold d),
      (∃ ρ : ProbabilityDensity d, IsGlobalMinimizer β ρ) ∧
      (∀ ρ : ProbabilityDensity d, IsGlobalMinimizer β ρ ↔
        ∃ a : Torus d, ρ.value =ᵐ[torusMeasure d] normalizedGibbs (translate
          (SupportedFamily.branch (by omega : 11 ≤ d) Finset.univ (onsetDelta d β) :
            ContinuousGibbs.Space d) a))) ∧
    (∃ R : ℝ → ℝ, AnalyticAt ℝ R 0 ∧
      (∀ᶠ β in 𝓝[>] (spectralThreshold d), (pressure d β).toReal =
        (d : ℝ) / (2 * kappa d) * onsetDelta d β ^ 2 + onsetDelta d β ^ 3 * R (onsetDelta d β)) ∧
      (fun β => deriv (fun γ => (pressure d γ).toReal) β -
          (d : ℝ) / (kappa d * spectralThreshold d) * onsetDelta d β)
        =O[𝓝[>] (spectralThreshold d)] (fun β => onsetDelta d β ^ 2) ∧
      (fun β => deriv (deriv (fun γ => (pressure d γ).toReal)) β -
          (d : ℝ) / (kappa d * spectralThreshold d ^ 2))
        =O[𝓝[>] (spectralThreshold d)] (onsetDelta d) ∧
      Tendsto (deriv (fun γ => (pressure d γ).toReal)) (𝓝[>] (spectralThreshold d)) (𝓝 0) ∧
      Tendsto (deriv (deriv (fun γ => (pressure d γ).toReal))) (𝓝[>] (spectralThreshold d))
        (𝓝 ((d : ℝ) / (kappa d * spectralThreshold d ^ 2)))) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ᶠ β in 𝓝[>] (spectralThreshold d),
      ∀ ρ : ProbabilityDensity d, IsGlobalMinimizer β ρ →
        |firstShellOrderParameter ρ.value -
          Real.sqrt (2 * (d : ℝ) / kappa d) * Real.sqrt (onsetDelta d β)| ≤ C * onsetDelta d β) ∧
    (∀ᶠ β in 𝓝[>] (spectralThreshold d),
      (HighDim.DiagonalScalarBranch.physicalPotential hd β : ContinuousGibbs.Space d) =
        SupportedFamily.branch (by omega : 11 ≤ d) Finset.univ (onsetDelta d β)) := by
  have E := SpinChannel.onsetEndpointInputs_written hd
  refine ⟨fun s hs => ?_, fun δ hδ x₀ x => MorseBott.cosine_correction_kappa (by omega) hδ x₀ x,
    MorseBott.minimizers_are_profile_branch_orbit hd E,
    MorseBott.pressure_differentiation_from_remainder hd E,
    MorseBott.all_minimizers_bound_v2 hd E,
    (MorseBott.common_branch_interface_beta hd).elim fun R h => h.2.mono fun β h => h.1⟩
  exact (prop_section5_local_branches d (by omega)).2.2.2.2.2.2.1 s hs

/-! ## Statement identity with the earlier conditional chain -/

theorem high_dim_onset_branch_route_statement_eq :
    (type_of% @high_dim_onset_branch_route) = (type_of% @SpinChannel.high_dim_onset_branch_written) := rfl

theorem high_dim_pressure_onset_route_statement_eq :
    (type_of% @high_dim_pressure_onset_route) =
      (type_of% @SpinChannel.high_dim_pressure_onset_written) := rfl

theorem high_dim_defect_onset_route_statement_eq :
    (type_of% @high_dim_defect_onset_route) = (type_of% @SpinChannel.high_dim_defect_onset_written) := rfl

#print axioms onset_manuscript

#print axioms high_dim_pressure_onset_route
#print axioms high_dim_defect_onset_route
#print axioms high_dim_onset_branch_route

end BecknerOnofri.V2.Reaudit.Final.Onset
