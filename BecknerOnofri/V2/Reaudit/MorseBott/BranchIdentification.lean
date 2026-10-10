module

public import BecknerOnofri.LocalElevenCore.SupportedFullIdentification
public import BecknerOnofri.LocalElevenCore.SupportedDeltaExhaustiveness
public import BecknerOnofri.FirstShellOrbits
public import BecknerOnofri.DiagonalAmplitude
public import BecknerOnofri.DiagonalStationaryBranch
public import BecknerOnofri.OptimizerTranslation
public import BecknerOnofri.Translation

@[expose] public section

/-! # One branch: the pressure/derivative family equals the profile family

The development carries two parallel constructions of the full-support branch:

* the **derivative family** `HighDim.DiagonalScalarBranch` (`12 ≤ d`): `branchPotential hd t`,
  `amplitude hd μ`, used for the energy `supercriticalEnergy`, the pressure derivatives and the
  order parameter;
* the **profile family** `HighDim.LocalEleven.SupportedFamily` (`11 ≤ d`): `branch hd I δ`, used
  for the Morse--Bott assertions, the profile `(5.full-branch-profile)` and the pressure value.

Both are produced by (separately chosen) implicit function constructions.  We prove that they are
the same potential: for `μ ↓ 1`,
`DiagonalScalarBranch.branchPotential hd (DiagonalScalarBranch.amplitude hd μ) =
  SupportedFamily.branch hd univ (1 - 1/μ)`.
The proof does *not* compare the constructions: the derivative-family potential is a small mean-zero
nonzero solution of the Euler equation whose first-shell coordinates are the positive real number
`amplitude`, so the existing local classification `small_solution_branch` forces it to be a
translate of a supported branch; positivity of all first-shell coordinates forces full support and
trivial translation. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace BecknerOnofri.V2.Reaudit.MorseBott
open BecknerOnofri.HighDim

/-- **The derivative-family branch is the profile-family branch.** -/
theorem derivativeBranch_eq_profileBranch {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ μ in 𝓝[>] (1 : ℝ),
      (DiagonalScalarBranch.branchPotential hd (DiagonalScalarBranch.amplitude hd μ) :
        ContinuousGibbs.Space d) =
        LocalEleven.SupportedFamily.branch (by omega : 11 ≤ d) Finset.univ (1 - 1 / μ) := by
  have hd11 : 11 ≤ d := by omega
  have hd0 : 0 < d := by omega
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := ⟨⟨0, hd0⟩, Finset.mem_univ _⟩
  -- the family `v μ`
  have hcont : ContinuousAt (DiagonalScalarBranch.branchPotential hd) 0 :=
    (DiagonalScalarBranch.branchPotential_analytic hd).continuousAt
  have hv0 : Tendsto (fun μ : ℝ =>
      DiagonalScalarBranch.branchPotential hd (DiagonalScalarBranch.amplitude hd μ))
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    have h := hcont.tendsto.comp (DiagonalScalarBranch.amplitude_tendsto hd)
    rw [DiagonalScalarBranch.branchPotential_base] at h
    exact h
  have hpair : Tendsto (fun μ : ℝ => ((μ, DiagonalScalarBranch.branchPotential hd
      (DiagonalScalarBranch.amplitude hd μ)) : ℝ × ContinuousGibbs.Space d))
      (𝓝[>] (1 : ℝ)) (𝓝 (1, 0)) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).prodMk_nhds hv0
  have hprof : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ I : Finset (Fin d), I.Nonempty →
      (∀ j : Fin d, fourierCoeff (LocalEleven.SupportedFamily.branch hd11 I δ) (axisFrequency j) =
        if j ∈ I then
          ((Real.sqrt (LocalEleven.SupportedFamily.amplitude hd11 I.card δ) : ℝ) : ℂ) else 0) ∧
      (∀ j : Fin d, fourierCoeff (LocalEleven.SupportedFamily.branch hd11 I δ) (axisFrequency j) ≠ 0
        ↔ j ∈ I) ∧
      0 < LocalEleven.SupportedFamily.amplitude hd11 I.card δ := by
    apply eventually_all.mpr
    intro I
    by_cases hI : I.Nonempty
    · filter_upwards [(LocalEleven.SupportedFamily.branch_profile hd11 I hI).1.2] with δ h _
      exact ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2, h.1⟩
    · exact Eventually.of_forall (fun δ h => (hI h).elim)
  have hδ : Tendsto (fun μ : ℝ => 1 - 1 / μ) (𝓝[>] (1 : ℝ)) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : ContinuousAt (fun μ : ℝ => 1 - 1 / μ) 1 :=
        continuousAt_const.sub (continuousAt_const.div continuousAt_id one_ne_zero)
      simpa using this.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with μ hμ
      have : 1 < μ := hμ
      simp only [Set.mem_Ioi]
      have : 1 / μ < 1 := by rw [div_lt_one (by linarith)]; exact this
      linarith
  filter_upwards [hpair.eventually (LocalEleven.SupportedFamily.small_solution_branch hd11),
    hδ.eventually hprof, DiagonalScalarBranch.eventually_parameter_interval hd,
    self_mem_nhdsWithin] with μ hsmall hpr hint hμ1
  have hμ : 1 < μ := hμ1
  set t := DiagonalScalarBranch.amplitude hd μ with ht
  have htpos : 0 < t := DiagonalScalarBranch.amplitude_pos hd hμ hint.2
  obtain ⟨hne0, hmean, -, -, hfull⟩ := DiagonalScalarBranch.amplitude_stationary hd hμ hint.2
  obtain ⟨-, I, hIne, a, hva⟩ := hsmall (by simpa [MeanZero] using hmean) hfull hne0
  set v := DiagonalScalarBranch.branchPotential hd t with hv
  -- first-shell coordinates of `v` are `t`
  have hcoord : ∀ j : Fin d, fourierCoeff (v : Torus d → ℝ) (axisFrequency j) = (t : ℂ) := by
    intro j
    have := congrFun (DiagonalScalarBranch.branchPotential_coordinates hd t) j
    rw [ContinuousFirstShell.coordinates_apply, ContinuousFirstShell.coefficient_eq_fourierCoeff] at this
    simpa using this
  -- coefficients of the translate of the supported branch
  have hcoef : ∀ j : Fin d, fourierCoeff (v : Torus d → ℝ) (axisFrequency j) =
      UnitAddTorus.mFourier (-axisFrequency j) a *
        fourierCoeff (LocalEleven.SupportedFamily.branch hd11 I (1 - 1 / μ) : Torus d → ℝ)
          (axisFrequency j) := by
    intro j
    rw [← ContinuousFirstShell.coefficient_eq_fourierCoeff, hva,
      ContinuousSymmetry.coefficient_translation, ContinuousFirstShell.coefficient_eq_fourierCoeff]
  obtain ⟨hco, hnz, hamp⟩ := hpr I hIne
  -- the support is full
  have hI : I = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]
    intro j
    apply (hnz j).mp
    intro h0
    have := hcoef j
    rw [h0, mul_zero, hcoord j] at this
    exact htpos.ne' (by exact_mod_cast this)
  subst hI
  obtain ⟨hco', hnz', hamp'⟩ := hpr Finset.univ hne
  set s' := Real.sqrt (LocalEleven.SupportedFamily.amplitude hd11 (Finset.univ : Finset (Fin d)).card
    (1 - 1 / μ)) with hs'
  have hs'pos : 0 < s' := Real.sqrt_pos.mpr hamp'
  have hphase : ∀ j : Fin d, UnitAddTorus.mFourier (-axisFrequency j) a = 1 := by
    intro j
    have h1 := hcoef j
    rw [hcoord j, hco' j] at h1
    simp only [Finset.mem_univ, ↓reduceIte] at h1
    have hn := congrArg norm h1
    rw [norm_mul, mFourier_norm_apply, one_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos htpos, abs_of_pos hs'pos] at hn
    have hts : t = s' := hn
    rw [hts] at h1
    have hne' : ((s' : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs'pos.ne'
    exact (mul_right_cancel₀ hne' (h1.symm.trans (one_mul _).symm))
  have ha0 : a = 0 := by
    funext j
    exact (ContinuousSymmetry.axis_phase_eq_one_iff a j).mp (hphase j)
  rw [ha0, ContinuousSymmetry.translation_zero] at hva
  exact hva

end BecknerOnofri.V2.Reaudit.MorseBott

#print axioms BecknerOnofri.V2.Reaudit.MorseBott.derivativeBranch_eq_profileBranch
