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
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Row04
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def segments : List (WeightedSegment (86956521739130434782608695652/10^30)) := [
  Segments000.Row04.segment,
  Segments001.Row04.segment,
  Segments002.Row04.segment,
  Segments003.Row04.segment,
  Segments004.Row04.segment,
  Segments005.Row04.segment,
  Segments006.Row04.segment,
  Segments007.Row04.segment,
  Segments008.Row04.segment,
  Segments009.Row04.segment,
  Segments010.Row04.segment,
  Segments011.Row04.segment,
  Segments012.Row04.segment,
  Segments013.Row04.segment,
  Segments014.Row04.segment,
  Segments015.Row04.segment,
  Segments016.Row04.segment,
  Segments017.Row04.segment,
  Segments018.Row04.segment,
  Segments019.Row04.segment,
  Segments020.Row04.segment,
  Segments021.Row04.segment,
  Segments022.Row04.segment,
  Segments023.Row04.segment,
  Segments024.Row04.segment,
  Segments025.Row04.segment,
  Segments026.Row04.segment,
  Segments027.Row04.segment,
  Segments028.Row04.segment,
  Segments029.Row04.segment,
  Segments030.Row04.segment
]
theorem chain_checked : segmentChainCheck (9950248756218905472636815920/10^30) 20 segments=true := by decide +kernel
theorem weight_checked : segmentTotal segments=2259601450965515720652243241272813553192691658887710338838220232574462696269230056711268611026238552500805848032599544669152333218501116404042461772696386798196025888153306201834693935390806455209851067604108059468/(720*10^210) := by decide +kernel
theorem heat_upper : heatIntegral (2/23) < 3138336/10^6 := by
  have h := segments_heatIntegral_bound segments chain_checked (by norm_num)
    (η := 2/23) (by norm_num) (by norm_num) (by norm_num)
  rw [weight_checked] at h
  apply h.trans_le
  norm_num
theorem budget_checked : (3138336/10^6 : ℚ) < rationalScalarBudget 9 := by decide +kernel
theorem scalar_interval {n : ℕ} (ha : 9≤n) (hb : n≤11) :
    scalarTail n < scalarBudget n := by
  apply scalarTail_lt_budget_of_rational_row (by omega) ha hb _ budget_checked
  convert! heat_upper using 1 <;> norm_num
#print axioms heat_upper
#print axioms scalar_interval
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Row04
