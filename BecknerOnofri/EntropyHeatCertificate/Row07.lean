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
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Row07
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def segments : List (WeightedSegment (33898305084745762711864406779/10^30)) := [
  Segments000.Row07.segment,
  Segments001.Row07.segment,
  Segments002.Row07.segment,
  Segments003.Row07.segment,
  Segments004.Row07.segment,
  Segments005.Row07.segment,
  Segments006.Row07.segment,
  Segments007.Row07.segment,
  Segments008.Row07.segment,
  Segments009.Row07.segment,
  Segments010.Row07.segment,
  Segments011.Row07.segment,
  Segments012.Row07.segment,
  Segments013.Row07.segment,
  Segments014.Row07.segment,
  Segments015.Row07.segment,
  Segments016.Row07.segment,
  Segments017.Row07.segment,
  Segments018.Row07.segment,
  Segments019.Row07.segment,
  Segments020.Row07.segment,
  Segments021.Row07.segment,
  Segments022.Row07.segment,
  Segments023.Row07.segment,
  Segments024.Row07.segment,
  Segments025.Row07.segment,
  Segments026.Row07.segment,
  Segments027.Row07.segment,
  Segments028.Row07.segment,
  Segments029.Row07.segment,
  Segments030.Row07.segment
]
theorem chain_checked : segmentChainCheck (9950248756218905472636815920/10^30) 20 segments=true := by decide +kernel
theorem weight_checked : segmentTotal segments=5762321769164489559998632075338498629569797148262897756630805499384943680396123859037040693104648122993593266319625130562393526654711658279778168272534280074501239043175922679755193057482274910578450181502933683219/(720*10^210) := by decide +kernel
theorem heat_upper : heatIntegral (2/59) < 8003225/10^6 := by
  have h := segments_heatIntegral_bound segments chain_checked (by norm_num)
    (η := 2/59) (by norm_num) (by norm_num) (by norm_num)
  rw [weight_checked] at h
  apply h.trans_le
  norm_num
theorem budget_checked : (8003225/10^6 : ℚ) < rationalScalarBudget 22 := by decide +kernel
theorem scalar_interval {n : ℕ} (ha : 22≤n) (hb : n≤29) :
    scalarTail n < scalarBudget n := by
  apply scalarTail_lt_budget_of_rational_row (by omega) ha hb _ budget_checked
  convert! heat_upper using 1 <;> norm_num
#print axioms heat_upper
#print axioms scalar_interval
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Row07
