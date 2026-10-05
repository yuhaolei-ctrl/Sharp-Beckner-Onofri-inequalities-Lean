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
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Row05
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def segments : List (WeightedSegment (64516129032258064516129032258/10^30)) := [
  Segments000.Row05.segment,
  Segments001.Row05.segment,
  Segments002.Row05.segment,
  Segments003.Row05.segment,
  Segments004.Row05.segment,
  Segments005.Row05.segment,
  Segments006.Row05.segment,
  Segments007.Row05.segment,
  Segments008.Row05.segment,
  Segments009.Row05.segment,
  Segments010.Row05.segment,
  Segments011.Row05.segment,
  Segments012.Row05.segment,
  Segments013.Row05.segment,
  Segments014.Row05.segment,
  Segments015.Row05.segment,
  Segments016.Row05.segment,
  Segments017.Row05.segment,
  Segments018.Row05.segment,
  Segments019.Row05.segment,
  Segments020.Row05.segment,
  Segments021.Row05.segment,
  Segments022.Row05.segment,
  Segments023.Row05.segment,
  Segments024.Row05.segment,
  Segments025.Row05.segment,
  Segments026.Row05.segment,
  Segments027.Row05.segment,
  Segments028.Row05.segment,
  Segments029.Row05.segment,
  Segments030.Row05.segment
]
theorem chain_checked : segmentChainCheck (9950248756218905472636815920/10^30) 20 segments=true := by decide +kernel
theorem weight_checked : segmentTotal segments=3210815345477073038470188504800534544380478355233845716952491169727309691268257887088791371179230330428588299778324160255352614238553395294051664760737086517243782261697529258651701359949612356431489183795034041000/(720*10^210) := by decide +kernel
theorem heat_upper : heatIntegral (2/31) < 4459466/10^6 := by
  have h := segments_heatIntegral_bound segments chain_checked (by norm_num)
    (η := 2/31) (by norm_num) (by norm_num) (by norm_num)
  rw [weight_checked] at h
  apply h.trans_le
  norm_num
theorem budget_checked : (4459466/10^6 : ℚ) < rationalScalarBudget 12 := by decide +kernel
theorem scalar_interval {n : ℕ} (ha : 12≤n) (hb : n≤15) :
    scalarTail n < scalarBudget n := by
  apply scalarTail_lt_budget_of_rational_row (by omega) ha hb _ budget_checked
  convert! heat_upper using 1 <;> norm_num
#print axioms heat_upper
#print axioms scalar_interval
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Row05
