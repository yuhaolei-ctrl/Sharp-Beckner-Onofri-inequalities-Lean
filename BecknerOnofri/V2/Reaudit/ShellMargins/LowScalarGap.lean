module

public import BecknerOnofri.V2.Reaudit.ShellMargins.RetainedShell
public import BecknerOnofri.V2.Reaudit.ShellMargins.TwoDim
public import Legacy.BecknerOnofri.GaussianScalarTail

@[expose] public section

/-! # Rows S020 and S022: the scalar inequality for `2 ≤ d ≤ 10`, assembled from the retained-shell
certificate

`eq:scalar-result` of the manuscript: for `2 ≤ d ≤ 10` and `n ≥ 1`,
`d H_n - (2d/β_s(d)) G_{d,n} > 3/1100`, where `G_{d,n}` is the lattice energy.  The three ranges of
`(d, n)` are proved as in the replacement text of Subsection `subsec:finite-scalar-inequalities`:

* the 171 pairs `Pair171` (`d = 2`, `n ≤ 3`; `3 ≤ d ≤ 10`, `n ≤ 21`) by the retained-shell
  certificate `scalar_gap_171_direct` (margin `4/25 > 3/1100`);
* `d = 2`, `n ≥ 4` by `dimension_two_large_printed` (margin `63407/1500000`);
* `3 ≤ d ≤ 10`, `n ≥ 22` by the Gaussian tail estimate (`gaussianTailBound`) with the theta-integral bound.

This theorem has the statement of `HighDim.LowScalar.scalar_gap`, and replaces it in the final chain. -/

noncomputable section

namespace BecknerOnofri.V2.Reaudit.ShellMargins

open Legacy.BecknerOnofri

theorem low_scalar_gap (d n : ℕ) (hd2 : 2 ≤ d) (hd10 : d ≤ 10) (hn : 1 ≤ n) :
    (3 / 1100 : ℝ) < (d : ℝ) * (_root_.harmonic n : ℝ) -
      (2 * (d : ℝ) / HighDim.spectralThreshold d) * HighDim.LowScalar.energy d n := by
  by_cases hp : Pair171 d n
  · exact lt_trans (by norm_num) (scalar_gap_171_direct hp)
  · by_cases hd : d = 2
    · subst hd
      have hn4 : 4 ≤ n := by
        by_contra h
        exact hp (Or.inl ⟨rfl, hn, by omega⟩)
      have h := dimension_two_large_printed hn4
      have e : (2 * ((2 : ℕ) : ℝ) / HighDim.spectralThreshold 2) =
          (4 : ℝ) / HighDim.spectralThreshold 2 := by
        push_cast; ring
      rw [e]
      push_cast
      have h' : (3 / 1100 : ℝ) < 63407 / 1500000 := by norm_num
      linarith
    · have hd3 : 3 ≤ d := by omega
      have hn22 : 22 ≤ n := by
        by_contra h
        exact hp (Or.inr ⟨hd3, hd10, hn, by omega⟩)
      have h := large_scalar_gap_of_gaussian hd3 hd10 hn22
        (GaussianScalarTail.gaussianTailBound hd3 hd10)
      have he : 2 * (d : ℝ) / HighDim.spectralThreshold d = 2 * endpointConstant d := by
        unfold endpointConstant HighDim.spectralThreshold Legacy.TorusEndpoint.endpointSigma
        ring
      rw [he, HighDim.LowScalar.energy_eq_legacy, ← HighDim.LowScalar.harmonic_eq]
      simpa only [scalarGap, LatticePolynomial.polynomialEnergy_eq_binomialEnergy] using h

end BecknerOnofri.V2.Reaudit.ShellMargins

end
