module

public import Legacy.BecknerOnofri.FiniteChecks.Dim03
public import Legacy.BecknerOnofri.FiniteChecks.Dim04
public import Legacy.BecknerOnofri.FiniteChecks.Dim05
public import Legacy.BecknerOnofri.FiniteChecks.Dim06
public import Legacy.BecknerOnofri.FiniteChecks.Dim07
public import Legacy.BecknerOnofri.FiniteChecks.Dim08
public import Legacy.BecknerOnofri.FiniteChecks.Dim09
public import Legacy.BecknerOnofri.FiniteChecks.Dim10

@[expose] public section

/-! The finite scalar certificates `FiniteCheck d n` for `3 ≤ d ≤ 10` and `1 ≤ n ≤ 21`. -/

namespace Legacy.BecknerOnofri.FiniteScalar

theorem finite_checks : ∀ j : Fin 21, ∀ i : Fin 8, FiniteCheck (i.val + 3) (j.val + 1) := by
  intro j i
  fin_cases i
  · exact Dim03.checks j
  · exact Dim04.checks j
  · exact Dim05.checks j
  · exact Dim06.checks j
  · exact Dim07.checks j
  · exact Dim08.checks j
  · exact Dim09.checks j
  · exact Dim10.checks j

theorem finite_check {d n : Nat} (hd : 3 ≤ d) (hd10 : d ≤ 10) (hn : 1 ≤ n) (hn21 : n ≤ 21) :
    FiniteCheck d n := by
  have h := finite_checks ⟨n - 1, by omega⟩ ⟨d - 3, by omega⟩
  simpa only [Nat.sub_add_cancel hd, Nat.sub_add_cancel hn] using h

end Legacy.BecknerOnofri.FiniteScalar
