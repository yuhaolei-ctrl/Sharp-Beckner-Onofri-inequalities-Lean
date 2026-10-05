module

public import BecknerOnofri.EntropyHeatCertificate.Row00
public import BecknerOnofri.EntropyHeatCertificate.Row01
public import BecknerOnofri.EntropyHeatCertificate.Row02
public import BecknerOnofri.EntropyHeatCertificate.Row03
public import BecknerOnofri.EntropyHeatCertificate.Row04
public import BecknerOnofri.EntropyHeatCertificate.Row05
public import BecknerOnofri.EntropyHeatCertificate.Row06
public import BecknerOnofri.EntropyHeatCertificate.Row07
public import BecknerOnofri.EntropyHeatCertificate.Row08
public import BecknerOnofri.EntropyHeatCertificate.Row09
public import BecknerOnofri.EntropyHeatCertificate.Row10
public import BecknerOnofri.EntropyHeatCertificate.Row11
public import BecknerOnofri.EntropyHeatCertificate.Row12
public import BecknerOnofri.EntropyTailTwo

@[expose] public section

noncomputable section
namespace BecknerOnofri.HighDim.EntropyTail
/-- The complete scalar tail bound. This file is only ready to build once
all exponential, panel, and thirteen row certificates have been accepted. -/
theorem scalarTail_le_budget (n : ℕ) : scalarTail n ≤ scalarBudget n := by
  by_cases hs : n ≤ 2
  · exact scalarTail_le_budget_of_le_two hs
  by_cases hl : 100 ≤ n
  · apply (scalarTail_lt_budget_large_of_base _ hl).le
    convert! HeatCertificate.Row12.heat_upper using 1 <;> norm_num
  by_cases h0 : n ≤ 3
  · exact (HeatCertificate.Row00.scalar_interval (by omega) h0).le
  by_cases h1 : n ≤ 4
  · exact (HeatCertificate.Row01.scalar_interval (by omega) h1).le
  by_cases h2 : n ≤ 6
  · exact (HeatCertificate.Row02.scalar_interval (by omega) h2).le
  by_cases h3 : n ≤ 8
  · exact (HeatCertificate.Row03.scalar_interval (by omega) h3).le
  by_cases h4 : n ≤ 11
  · exact (HeatCertificate.Row04.scalar_interval (by omega) h4).le
  by_cases h5 : n ≤ 15
  · exact (HeatCertificate.Row05.scalar_interval (by omega) h5).le
  by_cases h6 : n ≤ 21
  · exact (HeatCertificate.Row06.scalar_interval (by omega) h6).le
  by_cases h7 : n ≤ 29
  · exact (HeatCertificate.Row07.scalar_interval (by omega) h7).le
  by_cases h8 : n ≤ 39
  · exact (HeatCertificate.Row08.scalar_interval (by omega) h8).le
  by_cases h9 : n ≤ 53
  · exact (HeatCertificate.Row09.scalar_interval (by omega) h9).le
  by_cases h10 : n ≤ 72
  · exact (HeatCertificate.Row10.scalar_interval (by omega) h10).le
  by_cases h11 : n ≤ 98
  · exact (HeatCertificate.Row11.scalar_interval (by omega) h11).le
  exact (HeatCertificate.Row12.scalar_interval (by omega) (by omega)).le

#print axioms scalarTail_le_budget
end BecknerOnofri.HighDim.EntropyTail
