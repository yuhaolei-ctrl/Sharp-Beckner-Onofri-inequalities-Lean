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
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Row02
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def segments : List (WeightedSegment (153846153846153846153846153846/10^30)) := [
  Segments000.Row02.segment,
  Segments001.Row02.segment,
  Segments002.Row02.segment,
  Segments003.Row02.segment,
  Segments004.Row02.segment,
  Segments005.Row02.segment,
  Segments006.Row02.segment,
  Segments007.Row02.segment,
  Segments008.Row02.segment,
  Segments009.Row02.segment,
  Segments010.Row02.segment,
  Segments011.Row02.segment,
  Segments012.Row02.segment,
  Segments013.Row02.segment,
  Segments014.Row02.segment,
  Segments015.Row02.segment,
  Segments016.Row02.segment,
  Segments017.Row02.segment,
  Segments018.Row02.segment,
  Segments019.Row02.segment,
  Segments020.Row02.segment,
  Segments021.Row02.segment,
  Segments022.Row02.segment,
  Segments023.Row02.segment,
  Segments024.Row02.segment,
  Segments025.Row02.segment,
  Segments026.Row02.segment,
  Segments027.Row02.segment,
  Segments028.Row02.segment,
  Segments029.Row02.segment,
  Segments030.Row02.segment
]
theorem chain_checked : segmentChainCheck (9950248756218905472636815920/10^30) 20 segments=true := by decide +kernel
theorem weight_checked : segmentTotal segments=936749986256254332826290503868715978991436654930583839713403655426610286934799043691418636669314152898081826017072420444110665021573318521479794800791075210578525190324409156116666274607392660692139716965363002013/(720*10^210) := by decide +kernel
theorem heat_upper : heatIntegral (2/13) < 1301042/10^6 := by
  have h := segments_heatIntegral_bound segments chain_checked (by norm_num)
    (η := 2/13) (by norm_num) (by norm_num) (by norm_num)
  rw [weight_checked] at h
  apply h.trans_le
  norm_num
theorem budget_checked : (1301042/10^6 : ℚ) < rationalScalarBudget 5 := by decide +kernel
theorem scalar_interval {n : ℕ} (ha : 5≤n) (hb : n≤6) :
    scalarTail n < scalarBudget n := by
  apply scalarTail_lt_budget_of_rational_row (by omega) ha hb _ budget_checked
  convert! heat_upper using 1 <;> norm_num
#print axioms heat_upper
#print axioms scalar_interval
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Row02
