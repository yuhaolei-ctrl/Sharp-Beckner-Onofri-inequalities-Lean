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
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Row09
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def segments : List (WeightedSegment (18691588785046728971962616822/10^30)) := [
  Segments000.Row09.segment,
  Segments001.Row09.segment,
  Segments002.Row09.segment,
  Segments003.Row09.segment,
  Segments004.Row09.segment,
  Segments005.Row09.segment,
  Segments006.Row09.segment,
  Segments007.Row09.segment,
  Segments008.Row09.segment,
  Segments009.Row09.segment,
  Segments010.Row09.segment,
  Segments011.Row09.segment,
  Segments012.Row09.segment,
  Segments013.Row09.segment,
  Segments014.Row09.segment,
  Segments015.Row09.segment,
  Segments016.Row09.segment,
  Segments017.Row09.segment,
  Segments018.Row09.segment,
  Segments019.Row09.segment,
  Segments020.Row09.segment,
  Segments021.Row09.segment,
  Segments022.Row09.segment,
  Segments023.Row09.segment,
  Segments024.Row09.segment,
  Segments025.Row09.segment,
  Segments026.Row09.segment,
  Segments027.Row09.segment,
  Segments028.Row09.segment,
  Segments029.Row09.segment,
  Segments030.Row09.segment
]
theorem chain_checked : segmentChainCheck (9950248756218905472636815920/10^30) 20 segments=true := by decide +kernel
theorem weight_checked : segmentTotal segments=8567361443403920787858366332342711739492058263222201666906908021642690170507037203631581732276883733007585101051257022734603887922707571948311430772691925768735354282689510748890503357685429156177071822014256330255/(720*10^210) := by decide +kernel
theorem heat_upper : heatIntegral (2/107) < 11899114/10^6 := by
  have h := segments_heatIntegral_bound segments chain_checked (by norm_num)
    (η := 2/107) (by norm_num) (by norm_num) (by norm_num)
  rw [weight_checked] at h
  apply h.trans_le
  norm_num
theorem budget_checked : (11899114/10^6 : ℚ) < rationalScalarBudget 40 := by decide +kernel
theorem scalar_interval {n : ℕ} (ha : 40≤n) (hb : n≤53) :
    scalarTail n < scalarBudget n := by
  apply scalarTail_lt_budget_of_rational_row (by omega) ha hb _ budget_checked
  convert! heat_upper using 1 <;> norm_num
#print axioms heat_upper
#print axioms scalar_interval
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Row09
