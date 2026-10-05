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
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Row03
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def segments : List (WeightedSegment (117647058823529411764705882352/10^30)) := [
  Segments000.Row03.segment,
  Segments001.Row03.segment,
  Segments002.Row03.segment,
  Segments003.Row03.segment,
  Segments004.Row03.segment,
  Segments005.Row03.segment,
  Segments006.Row03.segment,
  Segments007.Row03.segment,
  Segments008.Row03.segment,
  Segments009.Row03.segment,
  Segments010.Row03.segment,
  Segments011.Row03.segment,
  Segments012.Row03.segment,
  Segments013.Row03.segment,
  Segments014.Row03.segment,
  Segments015.Row03.segment,
  Segments016.Row03.segment,
  Segments017.Row03.segment,
  Segments018.Row03.segment,
  Segments019.Row03.segment,
  Segments020.Row03.segment,
  Segments021.Row03.segment,
  Segments022.Row03.segment,
  Segments023.Row03.segment,
  Segments024.Row03.segment,
  Segments025.Row03.segment,
  Segments026.Row03.segment,
  Segments027.Row03.segment,
  Segments028.Row03.segment,
  Segments029.Row03.segment,
  Segments030.Row03.segment
]
theorem chain_checked : segmentChainCheck (9950248756218905472636815920/10^30) 20 segments=true := by decide +kernel
theorem weight_checked : segmentTotal segments=1474759919721907327879568931986341625560118853047113417766165231893888188190145742449737710949640541510642955394357314439702710653437333995890099197567417772647282282839814216627725584136025728828725749762429133563/(720*10^210) := by decide +kernel
theorem heat_upper : heatIntegral (2/17) < 2048278/10^6 := by
  have h := segments_heatIntegral_bound segments chain_checked (by norm_num)
    (η := 2/17) (by norm_num) (by norm_num) (by norm_num)
  rw [weight_checked] at h
  apply h.trans_le
  norm_num
theorem budget_checked : (2048278/10^6 : ℚ) < rationalScalarBudget 7 := by decide +kernel
theorem scalar_interval {n : ℕ} (ha : 7≤n) (hb : n≤8) :
    scalarTail n < scalarBudget n := by
  apply scalarTail_lt_budget_of_rational_row (by omega) ha hb _ budget_checked
  convert! heat_upper using 1 <;> norm_num
#print axioms heat_upper
#print axioms scalar_interval
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Row03
