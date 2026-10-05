import Legacy.BecknerOnofri.FiniteScalarCore
namespace Legacy.BecknerOnofri.FiniteScalar
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option profiler true

theorem weight_checks : ∀ i : Fin 8, ∀ j : Fin 65,
    scale^2 ≤ reciprocalUnits (i.val+3) (j.val+1)^2 * (j.val+1)^(i.val+3) := by
  decide +kernel

theorem weight_check {d q : Nat} (hd : 3 ≤ d) (hd10 : d ≤ 10)
    (hq : 1 ≤ q) (hq65 : q ≤ 65) :
    scale^2 ≤ reciprocalUnits d q^2 * q^d := by
  have h := weight_checks ⟨d-3, by omega⟩ ⟨q-1, by omega⟩
  simpa [Nat.sub_add_cancel hd, Nat.sub_add_cancel hq] using h

theorem weight_upper {d q : Nat} (hd : 3 ≤ d) (hd10 : d ≤ 10)
    (hq : 1 ≤ q) (hq65 : q ≤ 65) :
    1 / Real.sqrt ((q : ℝ)^d) ≤ (reciprocalUnits d q : ℝ) / scale :=
  reciprocal_sqrt_le (by decide) hq (weight_check hd hd10 hq hq65)

#print axioms weight_checks
#print axioms weight_upper
end Legacy.BecknerOnofri.FiniteScalar
