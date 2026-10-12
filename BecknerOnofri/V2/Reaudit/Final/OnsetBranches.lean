module

public import BecknerOnofri.V2.Reaudit.MorseBott.FullBranch
public import BecknerOnofri.LocalElevenCore.SupportedRawClassification
public import BecknerOnofri.LocalElevenCore.SupportedFamilyStability
public import BecknerOnofri.LocalElevenCore.SupportedFamilyEnergyOrdering
public import BecknerOnofri.LocalElevenCore.SupportedFamilyProfile
public import BecknerOnofri.QuarticSignsEleven
public import BecknerOnofri.LocalElevenCore.GraphAllSobolevBounds

@[expose] public section

/-! # Proposition `prop:section5-local-branches` as one statement (Reaudit, Final)

All assertions of the proposition for `d ≥ 11`, as one conjunction, assembled from the declarations
that prove them:

1. the analytic amplitudes `r_{d,n}(δ) = -δ/(2a_d + b_d(n-1)) + O(δ²)`
   (`SupportedFamily.amplitude_spec`);
2. the small nonzero critical points of `Φ_{d,τ}` in `H^s` (`s > d/2`) are translates of the branches
   `u = v_{δ,I,x₀} + w(τ, v_{δ,I,x₀})` (`SupportedFamily.raw_sobolev_classification`), and conversely
   the branch and its translates are critical points (`branch_profile`, `full_translation`);
3. the value on the `n`-branch, `-δ²/(4 q_{d,n}) + O(δ³)` (`SupportedFamily.branch_profile`, through
   `supported_energy_expansion`);
4. every `q_{d,n}` is negative (`LocalQuartic.coefficient_negative`);
5. the branches with `|I| < d` are saddles (`SupportedFamily.proper_branch_saddle`, through
   `small_stationary_saddle` and the `inactive_*` lemmas);
6. the full branch is a Morse--Bott local maximizer modulo translations
   (`SupportedFamily.full_branch_morse_bott`, `MorseBott.full_branch_embedded_orbit`);
7. the full branch has the largest value among the nonuniform branches
   (`SupportedFamily.branch_energy_ordering`, `branch_energy_ordering_ereal`);
8. the complement graph `w(τ, v)` is quadratically small in every Sobolev norm
   (`GraphAllSobolevBounds.correction_sobolev_quadratic`, the Wiener-algebra bound behind the profile
   estimate in every `H^r`). -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter MeasureTheory Asymptotics
open scoped Topology

namespace BecknerOnofri.V2.Reaudit.Final
open BecknerOnofri.HighDim BecknerOnofri.HighDim.LocalEleven ContinuousGibbs

/-- **Proposition `prop:section5-local-branches`** (`d ≥ 11`), every assertion of the printed
statement (see the module docstring). -/
theorem prop_section5_local_branches (d : ℕ) (hd : 11 ≤ d) :
    -- (1) the analytic amplitudes `r_{d,n}`
    (∀ n : ℕ, 0 < n → n ≤ d →
      AnalyticAt ℝ (SupportedFamily.amplitude hd n) 0 ∧
      (fun δ : ℝ => SupportedFamily.amplitude hd n δ -
          (-δ / (2 * quarticA d + quarticB d * ((n : ℝ) - 1)))) =O[𝓝 (0 : ℝ)]
        (fun δ => ‖δ‖ ^ 2)) ∧
    -- (2) the small nonzero critical points are exactly the translates of the branches
    (∀ s : ℝ, (d : ℝ) / 2 < s →
      ∃ ε : ℝ, 0 < ε ∧ ∀ (μ : ℝ) (u : Torus d → ℝ),
        InSobolev s u → MeanZero u → |μ - 1| < ε → sobolevNorm s u < ε →
        (∀ k : NonzeroFrequency d, ((frequencyLength k.val ^ d : ℝ) : ℂ) * fourierCoeff u k.val =
          (μ : ℂ) * fourierCoeff (normalizedGibbs u) k.val) →
        ¬u =ᵐ[torusMeasure d] (fun _ => 0) →
        0 < 1 - 1 / μ ∧ ∃ I : Finset (Fin d), I.Nonempty ∧ ∃ a : Torus d,
          u =ᵐ[torusMeasure d]
            (ContinuousSymmetry.translation a (SupportedFamily.branch hd I (1 - 1 / μ)) :
              Torus d → ℝ)) ∧
    (∀ I : Finset (Fin d), I.Nonempty → ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      0 < SupportedFamily.amplitude hd I.card δ ∧
      ∀ a : Torus d, LocalEleven.ReducedEquation.full d (1 / (1 - δ))
        (ContinuousSymmetry.translation a (SupportedFamily.branch hd I δ)) = 0) ∧
    -- (3) the value of the functional on the `n`-branch
    (∀ I : Finset (Fin d), I.Nonempty →
      (fun δ : ℝ => (dualFunctional ((1 / (1 - δ)) * spectralThreshold d)
          (SupportedFamily.branch hd I δ)).toReal -
        (-1 / (4 * branchQuarticCoefficient d I.card)) * δ ^ 2)
        =O[𝓝[>] (0 : ℝ)] (fun δ => ‖δ‖ ^ 3)) ∧
    -- (4) every `q_{d,n}` is negative
    (∀ n : ℕ, 0 < n → n ≤ d → branchQuarticCoefficient d n < 0) ∧
    -- (5) the branches with `n < d` are saddles
    (∀ I : Finset (Fin d), I.Nonempty → I.card < d → ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ∃ v q : Space d, InCriticalSobolev v ∧ MeanZero v ∧ InCriticalSobolev q ∧ MeanZero q ∧
        0 < secondVariation ((1 / (1 - δ)) * spectralThreshold d) (SupportedFamily.branch hd I δ) v ∧
        secondVariation ((1 / (1 - δ)) * spectralThreshold d) (SupportedFamily.branch hd I δ) q < 0) ∧
    -- (6) the full branch is a Morse--Bott local maximizer modulo translations
    (∀ s : ℝ, (d : ℝ) / 2 < s → ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ∃ hu : InSobolev s (SupportedFamily.branch hd Finset.univ δ),
        FullModeMorseBott ((1 / (1 - δ)) * spectralThreshold d)
          (SupportedFamily.branch hd Finset.univ δ) ∧
        MorseBott.EmbeddedCriticalOrbit ((1 / (1 - δ)) * spectralThreshold d) s
          (SupportedFamily.branch hd Finset.univ δ) hu) ∧
    -- (7) the full branch has the largest value among the branches
    (∀ I J : Finset (Fin d), I.Nonempty → I.card < J.card → ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (dualFunctional ((1 / (1 - δ)) * spectralThreshold d) (SupportedFamily.branch hd I δ)).toReal <
        (dualFunctional ((1 / (1 - δ)) * spectralThreshold d)
          (SupportedFamily.branch hd J δ)).toReal) ∧
    (∀ I J : Finset (Fin d), I.Nonempty → I.card < J.card → ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      dualFunctional ((1 / (1 - δ)) * spectralThreshold d) (SupportedFamily.branch hd I δ) <
        dualFunctional ((1 / (1 - δ)) * spectralThreshold d) (SupportedFamily.branch hd J δ)) ∧
    -- (8) the complement graph is quadratically small in every Sobolev norm
    (∀ s : ℝ, (fun x : ℝ × ContinuousFirstShell.Coordinates d =>
        sobolevNorm s (LocalEleven.GreenLocalBranch.correction hd x : Space d))
      =O[𝓝 (1, (0 : ContinuousFirstShell.Coordinates d))] (fun x => ‖x.2‖ ^ 2)) := by
  refine ⟨fun n hn hnd => ?_, fun s hs => SupportedFamily.raw_sobolev_classification hd s hs,
    fun I hI => ?_, fun I hI => (SupportedFamily.branch_profile hd I hI).2,
    fun n hn hnd => LocalQuartic.coefficient_negative hd hn hnd,
    fun I hI hc => SupportedFamily.proper_branch_saddle hd I hI hc,
    fun s hs => MorseBott.full_branch_embedded_orbit hd hs,
    fun I J hI hIJ => SupportedFamily.branch_energy_ordering hd I J hI hIJ,
    fun I J hI hIJ => SupportedFamily.branch_energy_ordering_ereal hd I J hI hIJ,
    fun s => LocalEleven.GraphAllSobolevBounds.correction_sobolev_quadratic hd s⟩
  · obtain ⟨hr, -, -, he, -⟩ := SupportedFamily.amplitude_spec hd hn hnd
    refine ⟨hr, he.congr_left fun δ => ?_⟩
    simp only [LocalReductionStatement.supportCoefficient, neg_div, div_neg]
  · filter_upwards [(SupportedFamily.branch_profile hd I hI).1.2] with δ hδ
    obtain ⟨hp, -, -, -, hm, hE, -⟩ := hδ
    refine ⟨hp, fun a => ?_⟩
    have hf : LocalEleven.ReducedEquation.full d (1 / (1 - δ)) (SupportedFamily.branch hd I δ) = 0 :=
      (LocalEleven.ReducedEquation.full_zero_iff_stationary (by omega) _ _).mpr ⟨hm, hE⟩
    rw [LocalEleven.ContinuousSymmetry.full_translation (by omega), hf, map_zero]

#print axioms prop_section5_local_branches

end BecknerOnofri.V2.Reaudit.Final
