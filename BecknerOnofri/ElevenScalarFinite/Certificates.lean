module

public import Legacy.D10.FiniteShellList
public import Legacy.BecknerOnofri.FiniteScalarCore
public import BecknerOnofri.ElevenScalarFinite.Core

@[expose] public section

/-!
# Finite scalar certificates in dimension eleven

The Section 4 checks `β_Λ E_n^+ + 1/2000 < 11 H_n` for `1 ≤ n ≤ 21`, where `E_n^+` is the
upper bound `energyUpper 11 n` for the scalar energy. Each check rewrites the truncated shell
polynomial with its list form (`shellArray_eq_shellList`) and is decided by the kernel.
-/

namespace BecknerOnofri.HighDim.Eleven.ScalarFinite

open Legacy.D10.FiniteScalar Legacy.BecknerOnofri.FiniteScalar

theorem check01 : betaLambda * Legacy.BecknerOnofri.FiniteScalar.energyUpper 11 1 + 1/2000 <
    11 * Legacy.D10.FiniteScalar.harmonic 1 := by
  unfold Legacy.BecknerOnofri.FiniteScalar.energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check02 : betaLambda * Legacy.BecknerOnofri.FiniteScalar.energyUpper 11 2 + 1/2000 <
    11 * Legacy.D10.FiniteScalar.harmonic 2 := by
  unfold Legacy.BecknerOnofri.FiniteScalar.energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check03 : betaLambda * Legacy.BecknerOnofri.FiniteScalar.energyUpper 11 3 + 1/2000 <
    11 * Legacy.D10.FiniteScalar.harmonic 3 := by
  unfold Legacy.BecknerOnofri.FiniteScalar.energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check04 : betaLambda * Legacy.BecknerOnofri.FiniteScalar.energyUpper 11 4 + 1/2000 <
    11 * Legacy.D10.FiniteScalar.harmonic 4 := by
  unfold Legacy.BecknerOnofri.FiniteScalar.energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check05 : betaLambda * Legacy.BecknerOnofri.FiniteScalar.energyUpper 11 5 + 1/2000 <
    11 * Legacy.D10.FiniteScalar.harmonic 5 := by
  unfold Legacy.BecknerOnofri.FiniteScalar.energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check06 : betaLambda * Legacy.BecknerOnofri.FiniteScalar.energyUpper 11 6 + 1/2000 <
    11 * Legacy.D10.FiniteScalar.harmonic 6 := by
  unfold Legacy.BecknerOnofri.FiniteScalar.energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check07 : betaLambda * Legacy.BecknerOnofri.FiniteScalar.energyUpper 11 7 + 1/2000 <
    11 * Legacy.D10.FiniteScalar.harmonic 7 := by
  unfold Legacy.BecknerOnofri.FiniteScalar.energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check08 : betaLambda * Legacy.BecknerOnofri.FiniteScalar.energyUpper 11 8 + 1/2000 <
    11 * Legacy.D10.FiniteScalar.harmonic 8 := by
  unfold Legacy.BecknerOnofri.FiniteScalar.energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check09 : betaLambda * Legacy.BecknerOnofri.FiniteScalar.energyUpper 11 9 + 1/2000 <
    11 * Legacy.D10.FiniteScalar.harmonic 9 := by
  unfold Legacy.BecknerOnofri.FiniteScalar.energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check10 : betaLambda * Legacy.BecknerOnofri.FiniteScalar.energyUpper 11 10 + 1/2000 <
    11 * Legacy.D10.FiniteScalar.harmonic 10 := by
  unfold Legacy.BecknerOnofri.FiniteScalar.energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check11 : betaLambda * Legacy.BecknerOnofri.FiniteScalar.energyUpper 11 11 + 1/2000 <
    11 * Legacy.D10.FiniteScalar.harmonic 11 := by
  unfold Legacy.BecknerOnofri.FiniteScalar.energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check12 : betaLambda * Legacy.BecknerOnofri.FiniteScalar.energyUpper 11 12 + 1/2000 <
    11 * Legacy.D10.FiniteScalar.harmonic 12 := by
  unfold Legacy.BecknerOnofri.FiniteScalar.energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check13 : betaLambda * Legacy.BecknerOnofri.FiniteScalar.energyUpper 11 13 + 1/2000 <
    11 * Legacy.D10.FiniteScalar.harmonic 13 := by
  unfold Legacy.BecknerOnofri.FiniteScalar.energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check14 : betaLambda * Legacy.BecknerOnofri.FiniteScalar.energyUpper 11 14 + 1/2000 <
    11 * Legacy.D10.FiniteScalar.harmonic 14 := by
  unfold Legacy.BecknerOnofri.FiniteScalar.energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check15 : betaLambda * Legacy.BecknerOnofri.FiniteScalar.energyUpper 11 15 + 1/2000 <
    11 * Legacy.D10.FiniteScalar.harmonic 15 := by
  unfold Legacy.BecknerOnofri.FiniteScalar.energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check16 : betaLambda * Legacy.BecknerOnofri.FiniteScalar.energyUpper 11 16 + 1/2000 <
    11 * Legacy.D10.FiniteScalar.harmonic 16 := by
  unfold Legacy.BecknerOnofri.FiniteScalar.energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check17 : betaLambda * Legacy.BecknerOnofri.FiniteScalar.energyUpper 11 17 + 1/2000 <
    11 * Legacy.D10.FiniteScalar.harmonic 17 := by
  unfold Legacy.BecknerOnofri.FiniteScalar.energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check18 : betaLambda * Legacy.BecknerOnofri.FiniteScalar.energyUpper 11 18 + 1/2000 <
    11 * Legacy.D10.FiniteScalar.harmonic 18 := by
  unfold Legacy.BecknerOnofri.FiniteScalar.energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check19 : betaLambda * Legacy.BecknerOnofri.FiniteScalar.energyUpper 11 19 + 1/2000 <
    11 * Legacy.D10.FiniteScalar.harmonic 19 := by
  unfold Legacy.BecknerOnofri.FiniteScalar.energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check20 : betaLambda * Legacy.BecknerOnofri.FiniteScalar.energyUpper 11 20 + 1/2000 <
    11 * Legacy.D10.FiniteScalar.harmonic 20 := by
  unfold Legacy.BecknerOnofri.FiniteScalar.energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem check21 : betaLambda * Legacy.BecknerOnofri.FiniteScalar.energyUpper 11 21 + 1/2000 <
    11 * Legacy.D10.FiniteScalar.harmonic 21 := by
  unfold Legacy.BecknerOnofri.FiniteScalar.energyUpper
  rw [shellArray_eq_shellList]
  decide +kernel

theorem checks : ∀ i : Fin 21,
    betaLambda * Legacy.BecknerOnofri.FiniteScalar.energyUpper 11 (i.val + 1) + 1/2000 <
      11 * Legacy.D10.FiniteScalar.harmonic (i.val + 1) := by
  intro i
  fin_cases i
  · exact check01
  · exact check02
  · exact check03
  · exact check04
  · exact check05
  · exact check06
  · exact check07
  · exact check08
  · exact check09
  · exact check10
  · exact check11
  · exact check12
  · exact check13
  · exact check14
  · exact check15
  · exact check16
  · exact check17
  · exact check18
  · exact check19
  · exact check20
  · exact check21

theorem weight_checks : ∀ i : Fin 65,
    Legacy.BecknerOnofri.FiniteScalar.scale^2 ≤
      reciprocalUnits 11 (i.val+1)^2 * (i.val+1)^11 := by
  decide +kernel

theorem weight_check {q : ℕ} (h : 1 ≤ q) (h' : q ≤ 65) :
    Legacy.BecknerOnofri.FiniteScalar.scale^2 ≤ reciprocalUnits 11 q^2 * q^11 := by
  have hh := weight_checks ⟨q-1, by omega⟩
  simpa [Nat.sub_add_cancel h] using hh

end BecknerOnofri.HighDim.Eleven.ScalarFinite
