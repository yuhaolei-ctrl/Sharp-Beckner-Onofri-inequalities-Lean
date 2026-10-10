module

public import BecknerOnofri.V2.Section3.Lemma32
public import BecknerOnofri.LowScalarFull
public import Legacy.D10.GaussianMajorantReal
public import BecknerOnofri.V2.Reaudit.ScalarBridges.GaussianBinomial

@[expose] public section

/-! # Lemma 3.5 (`lem:gaussian-binomial`) for `j ∈ ℤ` (G04)

`a_n(j) = C(2n, n+j) / C(2n, n)` is `EntropyTail.scalarCoefficient n j.natAbs` (zero outside the support
`|j| ≤ n`).  The repository proves the Gaussian bound for `j : ℕ`
(`Legacy.D10.binomialCoeffReal_gaussian`); the integer statement follows by symmetry. -/

noncomputable section

namespace BecknerOnofri.V2.Section3
open BecknerOnofri.HighDim

/-- **Lemma 3.5 (`lem:gaussian-binomial`).**  For `n ≥ 1` and `j ∈ ℤ`,
`a_n(j) ≤ exp(-log(1 + 1/n) j²)`. -/
theorem lemma_3_5 (n : ℕ) (hn : 0 < n) (j : ℤ) :
    EntropyTail.scalarCoefficient n j.natAbs ≤
      Real.exp (-Real.log (1 + 1 / (n : ℝ)) * (j : ℝ) ^ 2) :=
  BecknerOnofri.V2.Reaudit.ScalarBridges.lemma_3_5_artanh n hn j

#print axioms lemma_3_5

end BecknerOnofri.V2.Section3
