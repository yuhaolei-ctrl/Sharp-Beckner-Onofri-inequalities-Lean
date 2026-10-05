module

public import BecknerOnofri.EntropyTailRowAssembly
public import BecknerOnofri.EntropyHeatCertificate.Segments000
public import BecknerOnofri.EntropyHeatCertificate.Segments001
public import BecknerOnofri.EntropyHeatCertificate.Segments002
public import BecknerOnofri.EntropyHeatCertificate.Segments003
public import BecknerOnofri.EntropyHeatCertificate.Segments004
public import BecknerOnofri.EntropyHeatCertificate.Segments005
public import BecknerOnofri.EntropyHeatCertificate.Segments006
public import BecknerOnofri.EntropyHeatCertificate.Segments007
public import BecknerOnofri.EntropyHeatCertificate.Segments008
public import BecknerOnofri.EntropyHeatCertificate.Segments009
public import BecknerOnofri.EntropyHeatCertificate.Segments010
public import BecknerOnofri.EntropyHeatCertificate.Segments011
public import BecknerOnofri.EntropyHeatCertificate.Segments012
public import BecknerOnofri.EntropyHeatCertificate.Segments013
public import BecknerOnofri.EntropyHeatCertificate.Segments014
public import BecknerOnofri.EntropyHeatCertificate.Segments015
public import BecknerOnofri.EntropyHeatCertificate.Segments016
public import BecknerOnofri.EntropyHeatCertificate.Segments017
public import BecknerOnofri.EntropyHeatCertificate.Segments018
public import BecknerOnofri.EntropyHeatCertificate.Segments019
public import BecknerOnofri.EntropyHeatCertificate.Segments020
public import BecknerOnofri.EntropyHeatCertificate.Segments021
public import BecknerOnofri.EntropyHeatCertificate.Segments022
public import BecknerOnofri.EntropyHeatCertificate.Segments023
public import BecknerOnofri.EntropyHeatCertificate.Segments024
public import BecknerOnofri.EntropyHeatCertificate.Segments025
public import BecknerOnofri.EntropyHeatCertificate.Segments026
public import BecknerOnofri.EntropyHeatCertificate.Segments027
public import BecknerOnofri.EntropyHeatCertificate.Segments028
public import BecknerOnofri.EntropyHeatCertificate.Segments029
public import BecknerOnofri.EntropyHeatCertificate.Segments030

@[expose] public section
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Row10
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def segments : List (WeightedSegment (13793103448275862068965517241/10^30)) := [
  Segments000.Row10.segment,
  Segments001.Row10.segment,
  Segments002.Row10.segment,
  Segments003.Row10.segment,
  Segments004.Row10.segment,
  Segments005.Row10.segment,
  Segments006.Row10.segment,
  Segments007.Row10.segment,
  Segments008.Row10.segment,
  Segments009.Row10.segment,
  Segments010.Row10.segment,
  Segments011.Row10.segment,
  Segments012.Row10.segment,
  Segments013.Row10.segment,
  Segments014.Row10.segment,
  Segments015.Row10.segment,
  Segments016.Row10.segment,
  Segments017.Row10.segment,
  Segments018.Row10.segment,
  Segments019.Row10.segment,
  Segments020.Row10.segment,
  Segments021.Row10.segment,
  Segments022.Row10.segment,
  Segments023.Row10.segment,
  Segments024.Row10.segment,
  Segments025.Row10.segment,
  Segments026.Row10.segment,
  Segments027.Row10.segment,
  Segments028.Row10.segment,
  Segments029.Row10.segment,
  Segments030.Row10.segment
]
theorem chain_checked : segmentChainCheck (9950248756218905472636815920/10^30) 20 segments=true := by decide +kernel
theorem weight_checked : segmentTotal segments=10110021014781950775845753789530098720144294461487888498913592460010962483521792805311195241958197214670618412618340321433919097995385214755872647110219689813670488149840681937346696052515426035005945879521121680362/(720*10^210) := by decide +kernel
theorem heat_upper : heatIntegral (2/145) < 14041696/10^6 := by
  have h := segments_heatIntegral_bound segments chain_checked (by norm_num)
    (η := 2/145) (by norm_num) (by norm_num) (by norm_num)
  rw [weight_checked] at h
  apply h.trans_le
  norm_num
theorem budget_checked : (14041696/10^6 : ℚ) < rationalScalarBudget 54 := by decide +kernel
theorem scalar_interval {n : ℕ} (ha : 54≤n) (hb : n≤72) :
    scalarTail n < scalarBudget n := by
  apply scalarTail_lt_budget_of_rational_row (by omega) ha hb _ budget_checked
  convert! heat_upper using 1 <;> norm_num
#print axioms heat_upper
#print axioms scalar_interval
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Row10
