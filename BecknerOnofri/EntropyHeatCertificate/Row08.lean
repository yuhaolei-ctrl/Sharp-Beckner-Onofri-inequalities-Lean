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
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Row08
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def segments : List (WeightedSegment (25316455696202531645569620253/10^30)) := [
  Segments000.Row08.segment,
  Segments001.Row08.segment,
  Segments002.Row08.segment,
  Segments003.Row08.segment,
  Segments004.Row08.segment,
  Segments005.Row08.segment,
  Segments006.Row08.segment,
  Segments007.Row08.segment,
  Segments008.Row08.segment,
  Segments009.Row08.segment,
  Segments010.Row08.segment,
  Segments011.Row08.segment,
  Segments012.Row08.segment,
  Segments013.Row08.segment,
  Segments014.Row08.segment,
  Segments015.Row08.segment,
  Segments016.Row08.segment,
  Segments017.Row08.segment,
  Segments018.Row08.segment,
  Segments019.Row08.segment,
  Segments020.Row08.segment,
  Segments021.Row08.segment,
  Segments022.Row08.segment,
  Segments023.Row08.segment,
  Segments024.Row08.segment,
  Segments025.Row08.segment,
  Segments026.Row08.segment,
  Segments027.Row08.segment,
  Segments028.Row08.segment,
  Segments029.Row08.segment,
  Segments030.Row08.segment
]
theorem chain_checked : segmentChainCheck (9950248756218905472636815920/10^30) 20 segments=true := by decide +kernel
theorem weight_checked : segmentTotal segments=7095793836150044591163534613455240110706262392923135607093705080328155182122524611405552492267162412130735347857302389743318899271227097696932941596719544267221336614602756091508651122580190362247650901195553148990/(720*10^210) := by decide +kernel
theorem heat_upper : heatIntegral (2/79) < 9855270/10^6 := by
  have h := segments_heatIntegral_bound segments chain_checked (by norm_num)
    (η := 2/79) (by norm_num) (by norm_num) (by norm_num)
  rw [weight_checked] at h
  apply h.trans_le
  norm_num
theorem budget_checked : (9855270/10^6 : ℚ) < rationalScalarBudget 30 := by decide +kernel
theorem scalar_interval {n : ℕ} (ha : 30≤n) (hb : n≤39) :
    scalarTail n < scalarBudget n := by
  apply scalarTail_lt_budget_of_rational_row (by omega) ha hb _ budget_checked
  convert! heat_upper using 1 <;> norm_num
#print axioms heat_upper
#print axioms scalar_interval
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Row08
