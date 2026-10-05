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
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Row11
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def segments : List (WeightedSegment (10152284263959390862944162436/10^30)) := [
  Segments000.Row11.segment,
  Segments001.Row11.segment,
  Segments002.Row11.segment,
  Segments003.Row11.segment,
  Segments004.Row11.segment,
  Segments005.Row11.segment,
  Segments006.Row11.segment,
  Segments007.Row11.segment,
  Segments008.Row11.segment,
  Segments009.Row11.segment,
  Segments010.Row11.segment,
  Segments011.Row11.segment,
  Segments012.Row11.segment,
  Segments013.Row11.segment,
  Segments014.Row11.segment,
  Segments015.Row11.segment,
  Segments016.Row11.segment,
  Segments017.Row11.segment,
  Segments018.Row11.segment,
  Segments019.Row11.segment,
  Segments020.Row11.segment,
  Segments021.Row11.segment,
  Segments022.Row11.segment,
  Segments023.Row11.segment,
  Segments024.Row11.segment,
  Segments025.Row11.segment,
  Segments026.Row11.segment,
  Segments027.Row11.segment,
  Segments028.Row11.segment,
  Segments029.Row11.segment,
  Segments030.Row11.segment
]
theorem chain_checked : segmentChainCheck (9950248756218905472636815920/10^30) 20 segments=true := by decide +kernel
theorem weight_checked : segmentTotal segments=11719094962240642969282854070634523323498791385356825335834564180225637546068874562828053244267115221703573199059267435018756889847296200811194606801931025819227582400199599229265845446138687589072290662837966390661/(720*10^210) := by decide +kernel
theorem heat_upper : heatIntegral (2/197) < 16276521/10^6 := by
  have h := segments_heatIntegral_bound segments chain_checked (by norm_num)
    (η := 2/197) (by norm_num) (by norm_num) (by norm_num)
  rw [weight_checked] at h
  apply h.trans_le
  norm_num
theorem budget_checked : (16276521/10^6 : ℚ) < rationalScalarBudget 73 := by decide +kernel
theorem scalar_interval {n : ℕ} (ha : 73≤n) (hb : n≤98) :
    scalarTail n < scalarBudget n := by
  apply scalarTail_lt_budget_of_rational_row (by omega) ha hb _ budget_checked
  convert! heat_upper using 1 <;> norm_num
#print axioms heat_upper
#print axioms scalar_interval
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Row11
