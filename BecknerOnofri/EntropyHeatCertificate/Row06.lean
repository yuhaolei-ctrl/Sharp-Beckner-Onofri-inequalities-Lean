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
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Row06
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def segments : List (WeightedSegment (46511627906976744186046511627/10^30)) := [
  Segments000.Row06.segment,
  Segments001.Row06.segment,
  Segments002.Row06.segment,
  Segments003.Row06.segment,
  Segments004.Row06.segment,
  Segments005.Row06.segment,
  Segments006.Row06.segment,
  Segments007.Row06.segment,
  Segments008.Row06.segment,
  Segments009.Row06.segment,
  Segments010.Row06.segment,
  Segments011.Row06.segment,
  Segments012.Row06.segment,
  Segments013.Row06.segment,
  Segments014.Row06.segment,
  Segments015.Row06.segment,
  Segments016.Row06.segment,
  Segments017.Row06.segment,
  Segments018.Row06.segment,
  Segments019.Row06.segment,
  Segments020.Row06.segment,
  Segments021.Row06.segment,
  Segments022.Row06.segment,
  Segments023.Row06.segment,
  Segments024.Row06.segment,
  Segments025.Row06.segment,
  Segments026.Row06.segment,
  Segments027.Row06.segment,
  Segments028.Row06.segment,
  Segments029.Row06.segment,
  Segments030.Row06.segment
]
theorem chain_checked : segmentChainCheck (9950248756218905472636815920/10^30) 20 segments=true := by decide +kernel
theorem weight_checked : segmentTotal segments=4432089000590648335560705485900973421258019052520792732339266344885353640101294598374605418496931921525168096454928435978391289374434646761705156682447301188231562125092166489005274317757134237481222995415343858443/(720*10^210) := by decide +kernel
theorem heat_upper : heatIntegral (2/43) < 6155680/10^6 := by
  have h := segments_heatIntegral_bound segments chain_checked (by norm_num)
    (η := 2/43) (by norm_num) (by norm_num) (by norm_num)
  rw [weight_checked] at h
  apply h.trans_le
  norm_num
theorem budget_checked : (6155680/10^6 : ℚ) < rationalScalarBudget 16 := by decide +kernel
theorem scalar_interval {n : ℕ} (ha : 16≤n) (hb : n≤21) :
    scalarTail n < scalarBudget n := by
  apply scalarTail_lt_budget_of_rational_row (by omega) ha hb _ budget_checked
  convert! heat_upper using 1 <;> norm_num
#print axioms heat_upper
#print axioms scalar_interval
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Row06
