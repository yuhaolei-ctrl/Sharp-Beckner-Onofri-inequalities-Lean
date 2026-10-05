module

public import BecknerOnofri.LocalElevenCore.SupportedFamilyProfile
public import BecknerOnofri.QuadraticEnergyComparison
public import BecknerOnofri.LocalElevenCore.ContinuousEnergyAlongLine

@[expose] public section

noncomputable section
open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.SupportedFamily

/-- The very family used in the exhaustive classification has strictly increasing
physical branch energies as the number of active coordinates increases. -/
theorem branch_energy_ordering {d : ℕ} (hd : 11≤d)
    (I J : Finset (Fin d)) (hI : I.Nonempty) (hIJ : I.card<J.card) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ),
      (dualFunctional ((1/(1-δ))*spectralThreshold d) (branch hd I δ)).toReal <
        (dualFunctional ((1/(1-δ))*spectralThreshold d) (branch hd J δ)).toReal := by
  have hi : 0<I.card := Finset.card_pos.mpr hI
  have hJ : J.Nonempty := Finset.card_pos.mp (hi.trans hIJ)
  have hjD : J.card≤d := by simpa using Finset.card_le_univ J
  exact quadratic_energy_compare (LocalQuartic.branch_pressure_strictMono hd hi hIJ hjD)
    (branch_profile hd I hI).2 (branch_profile hd J hJ).2

/-- Strict ordering of the actual extended-real functional, on the same family. -/
theorem branch_energy_ordering_ereal {d : ℕ} (hd : 11≤d)
    (I J : Finset (Fin d)) (hI : I.Nonempty) (hIJ : I.card<J.card) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ),
      dualFunctional ((1/(1-δ))*spectralThreshold d) (branch hd I δ) <
        dualFunctional ((1/(1-δ))*spectralThreshold d) (branch hd J δ) := by
  have hJ : J.Nonempty := Finset.card_pos.mp ((Finset.card_pos.mpr hI).trans hIJ)
  filter_upwards [branch_energy_ordering hd I J hI hIJ,
    (branch_profile hd I hI).1.2,(branch_profile hd J hJ).1.2] with δ hE hi hj
  have heI := ContinuousEnergy.value_eq_dual (by omega : 0<d) (1/(1-δ))
    (branch hd I δ) hi.2.2.2.2.1
  have heJ := ContinuousEnergy.value_eq_dual (by omega : 0<d) (1/(1-δ))
    (branch hd J δ) hj.2.2.2.2.1
  rw [heI,heJ,EReal.toReal_coe,EReal.toReal_coe] at hE
  rw [heI,heJ]
  exact EReal.coe_lt_coe_iff.mpr hE

#print axioms branch_energy_ordering_ereal

#print axioms branch_energy_ordering
end BecknerOnofri.HighDim.LocalEleven.SupportedFamily
