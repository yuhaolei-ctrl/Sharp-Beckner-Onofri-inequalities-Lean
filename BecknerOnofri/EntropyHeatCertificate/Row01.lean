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
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Row01
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def segments : List (WeightedSegment (222222222222222222222222222222/10^30)) := [
  Segments000.Row01.segment,
  Segments001.Row01.segment,
  Segments002.Row01.segment,
  Segments003.Row01.segment,
  Segments004.Row01.segment,
  Segments005.Row01.segment,
  Segments006.Row01.segment,
  Segments007.Row01.segment,
  Segments008.Row01.segment,
  Segments009.Row01.segment,
  Segments010.Row01.segment,
  Segments011.Row01.segment,
  Segments012.Row01.segment,
  Segments013.Row01.segment,
  Segments014.Row01.segment,
  Segments015.Row01.segment,
  Segments016.Row01.segment,
  Segments017.Row01.segment,
  Segments018.Row01.segment,
  Segments019.Row01.segment,
  Segments020.Row01.segment,
  Segments021.Row01.segment,
  Segments022.Row01.segment,
  Segments023.Row01.segment,
  Segments024.Row01.segment,
  Segments025.Row01.segment,
  Segments026.Row01.segment,
  Segments027.Row01.segment,
  Segments028.Row01.segment,
  Segments029.Row01.segment,
  Segments030.Row01.segment
]
theorem chain_checked : segmentChainCheck (9950248756218905472636815920/10^30) 20 segments=true := by decide +kernel
theorem weight_checked : segmentTotal segments=433912042345147443714158698792054816065421645148169425012330025701616738108856910440251928522930387896947013571640911939872632564244639672766227139344216333679955427358675714931616901467704927236788543984219308598/(720*10^210) := by decide +kernel
theorem heat_upper : heatIntegral (2/9) < 602656/10^6 := by
  have h := segments_heatIntegral_bound segments chain_checked (by norm_num)
    (η := 2/9) (by norm_num) (by norm_num) (by norm_num)
  rw [weight_checked] at h
  apply h.trans_le
  norm_num
theorem budget_checked : (602656/10^6 : ℚ) < rationalScalarBudget 4 := by decide +kernel
theorem scalar_interval {n : ℕ} (ha : 4≤n) (hb : n≤4) :
    scalarTail n < scalarBudget n := by
  apply scalarTail_lt_budget_of_rational_row (by omega) ha hb _ budget_checked
  convert! heat_upper using 1 <;> norm_num
#print axioms heat_upper
#print axioms scalar_interval
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Row01
