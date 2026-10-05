module

public import BecknerOnofri.EndpointRigidity.MaximizerLevel

@[expose] public section

/-! Compactness of endpoint equality densities at a fixed entropy level.
The energy ball is fixed by the prescribed entropy, so this proof uses no
subcritical coercivity at the endpoint. -/
noncomputable section
open Set MeasureTheory
namespace BecknerOnofri.EndpointRigidity.Compactness
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open TorusSobolev SubcriticalAttainment SubcriticalEuler
open SubcriticalPrimalDual SubcriticalDensityCompactness GibbsL2Continuity
open MaximizerLevel

def potentialLevel (d : ℕ) (A E : ℝ) : Set (EnergyBall d (E/A)) :=
  maximizingPotentials d A (E/A) ∩ {u | Real.log (partition u.1) = E}

def densityLevel (d : ℕ) (C E : ℝ) : Set (DensityL2 d) :=
  {rL | ∃ r : ProbabilityDensity d, ∃ hr : MemLp r.value 2 (torusMeasure d),
    rL = hr.toLp r.value ∧ densityEntropy r.value = E ∧
      densityEntropy r.value = C * fourierEnergy r}

variable {d : ℕ} {C : ℝ} (hd : 0 < d) (hEndpoint : CoefficientEndpoint d C) {b Ab A E : ℝ}
  (hb : 0 < b) (hR : RoughExponentialBound d b Ab) (hA : 0 < A)
  (hCoeff : 1/(4*A) = C)

include hb hR hA
theorem potentialLevel_isClosed : IsClosed (potentialLevel d A E) := by
  apply (maximizingPotentials_isClosed hb hA.le hR).inter
  have hc : Continuous (fun u : EnergyBall d (E/A) => Real.log (partition u.1)) :=
    continuousOn_iff_continuous_restrict.mp (log_partition_continuousOn_ball hb hR)
  exact isClosed_eq hc continuous_const

include hd hEndpoint hCoeff
omit hb in
theorem densityLevel_eq_image : densityLevel d C E =
    (gibbsLp hR) '' potentialLevel d A E := by
  ext rL
  constructor
  · rintro ⟨r, hr, rfl, hEnt, he⟩
    let v := dualPotential A r hr
    have hv : Admissible v := dualPotential_admissible hd A r hr
    have hm := equality_density_maximizer hEndpoint hCoeff r he
    have hvmax := (density_maximizer_dual hd hR hA r hr hm).2
    have hE : criticalEnergy v = E/A := by
      rw [dualPotential_energy_of_equality hA hCoeff r hr hd he, hEnt]
    let vB : EnergyBall d (E/A) := ⟨v, ⟨⟨hv.2, hE.le⟩, hv.1⟩⟩
    refine ⟨vB, ⟨hvmax, ?_⟩, ?_⟩
    · exact (dualPotential_log_of_equality hd hEndpoint hR hA hCoeff r hr he).trans hEnt
    · apply Lp.ext
      filter_upwards [gibbsLp_ae hR vB, hr.coeFn_toLp,
        density_maximizer_gibbs hd hR hA r hr hm] with x hx hy he
      exact hx.trans (he.symm.trans hy.symm)
  · rintro ⟨u, hu, rfl⟩
    let r := gibbsDensity hR (ball_admissible u)
    have hr : MemLp r.value 2 (torusMeasure d) := gibbsValue_memLp_two hR (ball_admissible u)
    have hm := hu.1
    have hEnt : densityEntropy r.value = E :=
      (maximizer_entropy_eq_log hd hEndpoint hR hA hCoeff (ball_admissible u) hm).trans hu.2
    refine ⟨r, hr, ?_, hEnt, ?_⟩
    · apply Lp.ext
      filter_upwards [gibbsLp_ae hR u, hr.coeFn_toLp] with x hx hy
      exact hx.trans hy.symm
    · have hz := maximizer_functional_zero hd hEndpoint hR hA hCoeff (ball_admissible u) hm
      rw [maximizer_functional_eq_density hd hR hA (ball_admissible u) hm, hCoeff] at hz
      exact (sub_eq_zero.mp hz).symm

theorem densityLevel_isCompact (hE : 0 ≤ E) : IsCompact (densityLevel d C E) := by
  letI : CompactSpace (EnergyBall d (E/A)) :=
    isCompact_iff_compactSpace.mp (realSobolevBall_isCompact hd (div_nonneg hE hA.le))
  rw [densityLevel_eq_image hd hEndpoint hR hA hCoeff]
  exact (potentialLevel_isClosed hb hR hA).isCompact.image (gibbsLp_continuous hb hR)

#print axioms densityLevel_eq_image
#print axioms densityLevel_isCompact
end BecknerOnofri.EndpointRigidity.Compactness
