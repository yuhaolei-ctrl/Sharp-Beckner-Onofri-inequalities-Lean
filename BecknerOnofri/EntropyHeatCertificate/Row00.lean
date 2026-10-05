import BecknerOnofri.EntropyTailRowAssembly
import BecknerOnofri.EntropyHeatCertificate.Segments000
import BecknerOnofri.EntropyHeatCertificate.Segments001
import BecknerOnofri.EntropyHeatCertificate.Segments002
import BecknerOnofri.EntropyHeatCertificate.Segments003
import BecknerOnofri.EntropyHeatCertificate.Segments004
import BecknerOnofri.EntropyHeatCertificate.Segments005
import BecknerOnofri.EntropyHeatCertificate.Segments006
import BecknerOnofri.EntropyHeatCertificate.Segments007
import BecknerOnofri.EntropyHeatCertificate.Segments008
import BecknerOnofri.EntropyHeatCertificate.Segments009
import BecknerOnofri.EntropyHeatCertificate.Segments010
import BecknerOnofri.EntropyHeatCertificate.Segments011
import BecknerOnofri.EntropyHeatCertificate.Segments012
import BecknerOnofri.EntropyHeatCertificate.Segments013
import BecknerOnofri.EntropyHeatCertificate.Segments014
import BecknerOnofri.EntropyHeatCertificate.Segments015
import BecknerOnofri.EntropyHeatCertificate.Segments016
import BecknerOnofri.EntropyHeatCertificate.Segments017
import BecknerOnofri.EntropyHeatCertificate.Segments018
import BecknerOnofri.EntropyHeatCertificate.Segments019
import BecknerOnofri.EntropyHeatCertificate.Segments020
import BecknerOnofri.EntropyHeatCertificate.Segments021
import BecknerOnofri.EntropyHeatCertificate.Segments022
import BecknerOnofri.EntropyHeatCertificate.Segments023
import BecknerOnofri.EntropyHeatCertificate.Segments024
import BecknerOnofri.EntropyHeatCertificate.Segments025
import BecknerOnofri.EntropyHeatCertificate.Segments026
import BecknerOnofri.EntropyHeatCertificate.Segments027
import BecknerOnofri.EntropyHeatCertificate.Segments028
import BecknerOnofri.EntropyHeatCertificate.Segments029
import BecknerOnofri.EntropyHeatCertificate.Segments030
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Row00
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def segments : List (WeightedSegment (285714285714285714285714285714/10^30)) := [
  Segments000.Row00.segment,
  Segments001.Row00.segment,
  Segments002.Row00.segment,
  Segments003.Row00.segment,
  Segments004.Row00.segment,
  Segments005.Row00.segment,
  Segments006.Row00.segment,
  Segments007.Row00.segment,
  Segments008.Row00.segment,
  Segments009.Row00.segment,
  Segments010.Row00.segment,
  Segments011.Row00.segment,
  Segments012.Row00.segment,
  Segments013.Row00.segment,
  Segments014.Row00.segment,
  Segments015.Row00.segment,
  Segments016.Row00.segment,
  Segments017.Row00.segment,
  Segments018.Row00.segment,
  Segments019.Row00.segment,
  Segments020.Row00.segment,
  Segments021.Row00.segment,
  Segments022.Row00.segment,
  Segments023.Row00.segment,
  Segments024.Row00.segment,
  Segments025.Row00.segment,
  Segments026.Row00.segment,
  Segments027.Row00.segment,
  Segments028.Row00.segment,
  Segments029.Row00.segment,
  Segments030.Row00.segment
]
theorem chain_checked : segmentChainCheck (9950248756218905472636815920/10^30) 20 segments=true := by decide +kernel
theorem weight_checked : segmentTotal segments=226590550947783281662566072054151867419194012326815232706129133328564235648068618141350209047164470277854395764029695754619727531838700090324114456338042280244023659772085186717219793568501502226484657600783751005/(720*10^210) := by decide +kernel
theorem heat_upper : heatIntegral (2/7) < 314710/10^6 := by
  have h := segments_heatIntegral_bound segments chain_checked (by norm_num)
    (η := 2/7) (by norm_num) (by norm_num) (by norm_num)
  rw [weight_checked] at h
  apply h.trans_le
  norm_num
theorem budget_checked : (314710/10^6 : ℚ) < rationalScalarBudget 3 := by decide +kernel
theorem scalar_interval {n : ℕ} (ha : 3≤n) (hb : n≤3) :
    scalarTail n < scalarBudget n := by
  apply scalarTail_lt_budget_of_rational_row (by omega) ha hb _ budget_checked
  convert! heat_upper using 1 <;> norm_num
#print axioms heat_upper
#print axioms scalar_interval
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Row00
