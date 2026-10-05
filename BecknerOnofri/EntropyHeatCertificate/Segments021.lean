module

public import BecknerOnofri.EntropyHeatCheckedWeights
public import BecknerOnofri.EntropyHeatSegments
public import BecknerOnofri.EntropyHeatCertificate.Panels0168
public import BecknerOnofri.EntropyHeatCertificate.Panels0169
public import BecknerOnofri.EntropyHeatCertificate.Panels0170
public import BecknerOnofri.EntropyHeatCertificate.Panels0171
public import BecknerOnofri.EntropyHeatCertificate.Panels0172
public import BecknerOnofri.EntropyHeatCertificate.Panels0173
public import BecknerOnofri.EntropyHeatCertificate.Panels0174
public import BecknerOnofri.EntropyHeatCertificate.Panels0175

@[expose] public section
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments021
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace Row00
abbrev ζ : ℚ := 285714285714285714285714285714/10^30
def b0168 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0168.block Panels0168.accepted Panels0168.integerPanels Panels0168.aligned
    Panels0168.weightRows Panels0168.weights_checked ⟨0, by decide⟩
def b0169 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0169.block Panels0169.accepted Panels0169.integerPanels Panels0169.aligned
    Panels0169.weightRows Panels0169.weights_checked ⟨0, by decide⟩
def b0170 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0170.block Panels0170.accepted Panels0170.integerPanels Panels0170.aligned
    Panels0170.weightRows Panels0170.weights_checked ⟨0, by decide⟩
def b0171 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0171.block Panels0171.accepted Panels0171.integerPanels Panels0171.aligned
    Panels0171.weightRows Panels0171.weights_checked ⟨0, by decide⟩
def b0172 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0172.block Panels0172.accepted Panels0172.integerPanels Panels0172.aligned
    Panels0172.weightRows Panels0172.weights_checked ⟨0, by decide⟩
def b0173 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0173.block Panels0173.accepted Panels0173.integerPanels Panels0173.aligned
    Panels0173.weightRows Panels0173.weights_checked ⟨0, by decide⟩
def b0174 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0174.block Panels0174.accepted Panels0174.integerPanels Panels0174.aligned
    Panels0174.weightRows Panels0174.weights_checked ⟨0, by decide⟩
def b0175 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0175.block Panels0175.accepted Panels0175.integerPanels Panels0175.aligned
    Panels0175.weightRows Panels0175.weights_checked ⟨0, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0168, b0169, b0170, b0171, b0172, b0173, b0174, b0175]
theorem chain_checked : blockChainCheck (1894967158257301031874623425110/10^30) (2433111753263434836465548498036/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=3535376313955880607789130226311843725671665002954528505427113115391371931774397853312500575346182688396134171940275290426514602983037832605822836043458822267925091669578220912005949799141772331298264267095635797/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row00
namespace Row01
abbrev ζ : ℚ := 222222222222222222222222222222/10^30
def b0168 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0168.block Panels0168.accepted Panels0168.integerPanels Panels0168.aligned
    Panels0168.weightRows Panels0168.weights_checked ⟨1, by decide⟩
def b0169 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0169.block Panels0169.accepted Panels0169.integerPanels Panels0169.aligned
    Panels0169.weightRows Panels0169.weights_checked ⟨1, by decide⟩
def b0170 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0170.block Panels0170.accepted Panels0170.integerPanels Panels0170.aligned
    Panels0170.weightRows Panels0170.weights_checked ⟨1, by decide⟩
def b0171 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0171.block Panels0171.accepted Panels0171.integerPanels Panels0171.aligned
    Panels0171.weightRows Panels0171.weights_checked ⟨1, by decide⟩
def b0172 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0172.block Panels0172.accepted Panels0172.integerPanels Panels0172.aligned
    Panels0172.weightRows Panels0172.weights_checked ⟨1, by decide⟩
def b0173 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0173.block Panels0173.accepted Panels0173.integerPanels Panels0173.aligned
    Panels0173.weightRows Panels0173.weights_checked ⟨1, by decide⟩
def b0174 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0174.block Panels0174.accepted Panels0174.integerPanels Panels0174.aligned
    Panels0174.weightRows Panels0174.weights_checked ⟨1, by decide⟩
def b0175 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0175.block Panels0175.accepted Panels0175.integerPanels Panels0175.aligned
    Panels0175.weightRows Panels0175.weights_checked ⟨1, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0168, b0169, b0170, b0171, b0172, b0173, b0174, b0175]
theorem chain_checked : blockChainCheck (1894967158257301031874623425110/10^30) (2433111753263434836465548498036/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=4208979426395159421227599221032378869649028462531171169825714147352095074997847325573935051346181649340286903464282874601301570152646718691385838375968490498681416976425016255393015674665643935562189402776075677/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row01
namespace Row02
abbrev ζ : ℚ := 153846153846153846153846153846/10^30
def b0168 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0168.block Panels0168.accepted Panels0168.integerPanels Panels0168.aligned
    Panels0168.weightRows Panels0168.weights_checked ⟨2, by decide⟩
def b0169 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0169.block Panels0169.accepted Panels0169.integerPanels Panels0169.aligned
    Panels0169.weightRows Panels0169.weights_checked ⟨2, by decide⟩
def b0170 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0170.block Panels0170.accepted Panels0170.integerPanels Panels0170.aligned
    Panels0170.weightRows Panels0170.weights_checked ⟨2, by decide⟩
def b0171 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0171.block Panels0171.accepted Panels0171.integerPanels Panels0171.aligned
    Panels0171.weightRows Panels0171.weights_checked ⟨2, by decide⟩
def b0172 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0172.block Panels0172.accepted Panels0172.integerPanels Panels0172.aligned
    Panels0172.weightRows Panels0172.weights_checked ⟨2, by decide⟩
def b0173 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0173.block Panels0173.accepted Panels0173.integerPanels Panels0173.aligned
    Panels0173.weightRows Panels0173.weights_checked ⟨2, by decide⟩
def b0174 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0174.block Panels0174.accepted Panels0174.integerPanels Panels0174.aligned
    Panels0174.weightRows Panels0174.weights_checked ⟨2, by decide⟩
def b0175 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0175.block Panels0175.accepted Panels0175.integerPanels Panels0175.aligned
    Panels0175.weightRows Panels0175.weights_checked ⟨2, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0168, b0169, b0170, b0171, b0172, b0173, b0174, b0175]
theorem chain_checked : blockChainCheck (1894967158257301031874623425110/10^30) (2433111753263434836465548498036/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=5046076141456847711424938959155961993909615322257814741337997863409802260074884403039357426198358556717090686625918866542270811768315087241196853729232665812688727902831358698413839849346738438146088476997344557/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row02
namespace Row03
abbrev ζ : ℚ := 117647058823529411764705882352/10^30
def b0168 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0168.block Panels0168.accepted Panels0168.integerPanels Panels0168.aligned
    Panels0168.weightRows Panels0168.weights_checked ⟨3, by decide⟩
def b0169 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0169.block Panels0169.accepted Panels0169.integerPanels Panels0169.aligned
    Panels0169.weightRows Panels0169.weights_checked ⟨3, by decide⟩
def b0170 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0170.block Panels0170.accepted Panels0170.integerPanels Panels0170.aligned
    Panels0170.weightRows Panels0170.weights_checked ⟨3, by decide⟩
def b0171 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0171.block Panels0171.accepted Panels0171.integerPanels Panels0171.aligned
    Panels0171.weightRows Panels0171.weights_checked ⟨3, by decide⟩
def b0172 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0172.block Panels0172.accepted Panels0172.integerPanels Panels0172.aligned
    Panels0172.weightRows Panels0172.weights_checked ⟨3, by decide⟩
def b0173 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0173.block Panels0173.accepted Panels0173.integerPanels Panels0173.aligned
    Panels0173.weightRows Panels0173.weights_checked ⟨3, by decide⟩
def b0174 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0174.block Panels0174.accepted Panels0174.integerPanels Panels0174.aligned
    Panels0174.weightRows Panels0174.weights_checked ⟨3, by decide⟩
def b0175 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0175.block Panels0175.accepted Panels0175.integerPanels Panels0175.aligned
    Panels0175.weightRows Panels0175.weights_checked ⟨3, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0168, b0169, b0170, b0171, b0172, b0173, b0174, b0175]
theorem chain_checked : blockChainCheck (1894967158257301031874623425110/10^30) (2433111753263434836465548498036/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=5540549654282957665579642810652798504145182016952691303521065992394007610481269758482637834277174222128487039470663169309351042651123399970644341141416258769423568866824918963354981607523250358539557530146671677/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row03
namespace Row04
abbrev ζ : ℚ := 86956521739130434782608695652/10^30
def b0168 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0168.block Panels0168.accepted Panels0168.integerPanels Panels0168.aligned
    Panels0168.weightRows Panels0168.weights_checked ⟨4, by decide⟩
def b0169 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0169.block Panels0169.accepted Panels0169.integerPanels Panels0169.aligned
    Panels0169.weightRows Panels0169.weights_checked ⟨4, by decide⟩
def b0170 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0170.block Panels0170.accepted Panels0170.integerPanels Panels0170.aligned
    Panels0170.weightRows Panels0170.weights_checked ⟨4, by decide⟩
def b0171 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0171.block Panels0171.accepted Panels0171.integerPanels Panels0171.aligned
    Panels0171.weightRows Panels0171.weights_checked ⟨4, by decide⟩
def b0172 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0172.block Panels0172.accepted Panels0172.integerPanels Panels0172.aligned
    Panels0172.weightRows Panels0172.weights_checked ⟨4, by decide⟩
def b0173 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0173.block Panels0173.accepted Panels0173.integerPanels Panels0173.aligned
    Panels0173.weightRows Panels0173.weights_checked ⟨4, by decide⟩
def b0174 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0174.block Panels0174.accepted Panels0174.integerPanels Panels0174.aligned
    Panels0174.weightRows Panels0174.weights_checked ⟨4, by decide⟩
def b0175 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0175.block Panels0175.accepted Panels0175.integerPanels Panels0175.aligned
    Panels0175.weightRows Panels0175.weights_checked ⟨4, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0168, b0169, b0170, b0171, b0172, b0173, b0174, b0175]
theorem chain_checked : blockChainCheck (1894967158257301031874623425110/10^30) (2433111753263434836465548498036/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=5989632551630099228491904944992791828622088524937817218466076049327798735489507520646727203706516949431892284124691026794320321917759504343175020739997709227364669676641088647271796010773665835839781467652156677/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row04
namespace Row05
abbrev ζ : ℚ := 64516129032258064516129032258/10^30
def b0168 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0168.block Panels0168.accepted Panels0168.integerPanels Panels0168.aligned
    Panels0168.weightRows Panels0168.weights_checked ⟨5, by decide⟩
def b0169 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0169.block Panels0169.accepted Panels0169.integerPanels Panels0169.aligned
    Panels0169.weightRows Panels0169.weights_checked ⟨5, by decide⟩
def b0170 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0170.block Panels0170.accepted Panels0170.integerPanels Panels0170.aligned
    Panels0170.weightRows Panels0170.weights_checked ⟨5, by decide⟩
def b0171 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0171.block Panels0171.accepted Panels0171.integerPanels Panels0171.aligned
    Panels0171.weightRows Panels0171.weights_checked ⟨5, by decide⟩
def b0172 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0172.block Panels0172.accepted Panels0172.integerPanels Panels0172.aligned
    Panels0172.weightRows Panels0172.weights_checked ⟨5, by decide⟩
def b0173 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0173.block Panels0173.accepted Panels0173.integerPanels Panels0173.aligned
    Panels0173.weightRows Panels0173.weights_checked ⟨5, by decide⟩
def b0174 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0174.block Panels0174.accepted Panels0174.integerPanels Panels0174.aligned
    Panels0174.weightRows Panels0174.weights_checked ⟨5, by decide⟩
def b0175 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0175.block Panels0175.accepted Panels0175.integerPanels Panels0175.aligned
    Panels0175.weightRows Panels0175.weights_checked ⟨5, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0168, b0169, b0170, b0171, b0172, b0173, b0174, b0175]
theorem chain_checked : blockChainCheck (1894967158257301031874623425110/10^30) (2433111753263434836465548498036/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=6336146147525545826680357501301766016805269776144636293241263487686101138770038045639492465372066482608860116791504453893269908365626180651110110567718043035033545866484119164448768950677716961874425029780834357/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row05
namespace Row06
abbrev ζ : ℚ := 46511627906976744186046511627/10^30
def b0168 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0168.block Panels0168.accepted Panels0168.integerPanels Panels0168.aligned
    Panels0168.weightRows Panels0168.weights_checked ⟨6, by decide⟩
def b0169 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0169.block Panels0169.accepted Panels0169.integerPanels Panels0169.aligned
    Panels0169.weightRows Panels0169.weights_checked ⟨6, by decide⟩
def b0170 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0170.block Panels0170.accepted Panels0170.integerPanels Panels0170.aligned
    Panels0170.weightRows Panels0170.weights_checked ⟨6, by decide⟩
def b0171 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0171.block Panels0171.accepted Panels0171.integerPanels Panels0171.aligned
    Panels0171.weightRows Panels0171.weights_checked ⟨6, by decide⟩
def b0172 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0172.block Panels0172.accepted Panels0172.integerPanels Panels0172.aligned
    Panels0172.weightRows Panels0172.weights_checked ⟨6, by decide⟩
def b0173 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0173.block Panels0173.accepted Panels0173.integerPanels Panels0173.aligned
    Panels0173.weightRows Panels0173.weights_checked ⟨6, by decide⟩
def b0174 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0174.block Panels0174.accepted Panels0174.integerPanels Panels0174.aligned
    Panels0174.weightRows Panels0174.weights_checked ⟨6, by decide⟩
def b0175 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0175.block Panels0175.accepted Panels0175.integerPanels Panels0175.aligned
    Panels0175.weightRows Panels0175.weights_checked ⟨6, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0168, b0169, b0170, b0171, b0172, b0173, b0174, b0175]
theorem chain_checked : blockChainCheck (1894967158257301031874623425110/10^30) (2433111753263434836465548498036/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=6625655353655199151822671113463590254556073903686335038866364619419833995588096324230617194703138453853636376051335398554916186901415751046348453338328088182121874248062552117933331708038179619522179368403220427/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row06
namespace Row07
abbrev ζ : ℚ := 33898305084745762711864406779/10^30
def b0168 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0168.block Panels0168.accepted Panels0168.integerPanels Panels0168.aligned
    Panels0168.weightRows Panels0168.weights_checked ⟨7, by decide⟩
def b0169 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0169.block Panels0169.accepted Panels0169.integerPanels Panels0169.aligned
    Panels0169.weightRows Panels0169.weights_checked ⟨7, by decide⟩
def b0170 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0170.block Panels0170.accepted Panels0170.integerPanels Panels0170.aligned
    Panels0170.weightRows Panels0170.weights_checked ⟨7, by decide⟩
def b0171 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0171.block Panels0171.accepted Panels0171.integerPanels Panels0171.aligned
    Panels0171.weightRows Panels0171.weights_checked ⟨7, by decide⟩
def b0172 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0172.block Panels0172.accepted Panels0172.integerPanels Panels0172.aligned
    Panels0172.weightRows Panels0172.weights_checked ⟨7, by decide⟩
def b0173 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0173.block Panels0173.accepted Panels0173.integerPanels Panels0173.aligned
    Panels0173.weightRows Panels0173.weights_checked ⟨7, by decide⟩
def b0174 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0174.block Panels0174.accepted Panels0174.integerPanels Panels0174.aligned
    Panels0174.weightRows Panels0174.weights_checked ⟨7, by decide⟩
def b0175 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0175.block Panels0175.accepted Panels0175.integerPanels Panels0175.aligned
    Panels0175.weightRows Panels0175.weights_checked ⟨7, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0168, b0169, b0170, b0171, b0172, b0173, b0174, b0175]
theorem chain_checked : blockChainCheck (1894967158257301031874623425110/10^30) (2433111753263434836465548498036/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=6834734438605658612827941279268766282936103275395048381023811143426223104748364070462390007418952433285006741142843045419006954055904403716028642531294933363737479474742713231913877861746472067924628497237623147/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row07
namespace Row08
abbrev ζ : ℚ := 25316455696202531645569620253/10^30
def b0168 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0168.block Panels0168.accepted Panels0168.integerPanels Panels0168.aligned
    Panels0168.weightRows Panels0168.weights_checked ⟨8, by decide⟩
def b0169 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0169.block Panels0169.accepted Panels0169.integerPanels Panels0169.aligned
    Panels0169.weightRows Panels0169.weights_checked ⟨8, by decide⟩
def b0170 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0170.block Panels0170.accepted Panels0170.integerPanels Panels0170.aligned
    Panels0170.weightRows Panels0170.weights_checked ⟨8, by decide⟩
def b0171 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0171.block Panels0171.accepted Panels0171.integerPanels Panels0171.aligned
    Panels0171.weightRows Panels0171.weights_checked ⟨8, by decide⟩
def b0172 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0172.block Panels0172.accepted Panels0172.integerPanels Panels0172.aligned
    Panels0172.weightRows Panels0172.weights_checked ⟨8, by decide⟩
def b0173 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0173.block Panels0173.accepted Panels0173.integerPanels Panels0173.aligned
    Panels0173.weightRows Panels0173.weights_checked ⟨8, by decide⟩
def b0174 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0174.block Panels0174.accepted Panels0174.integerPanels Panels0174.aligned
    Panels0174.weightRows Panels0174.weights_checked ⟨8, by decide⟩
def b0175 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0175.block Panels0175.accepted Panels0175.integerPanels Panels0175.aligned
    Panels0175.weightRows Panels0175.weights_checked ⟨8, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0168, b0169, b0170, b0171, b0172, b0173, b0174, b0175]
theorem chain_checked : blockChainCheck (1894967158257301031874623425110/10^30) (2433111753263434836465548498036/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=6979993577814356228811254833440523662445459470655257524400196004873375949240432596748539146197334239691089071894482613528526804585285398049013915948254060620802234838370622777173604992563900831633806295213806907/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row08
namespace Row09
abbrev ζ : ℚ := 18691588785046728971962616822/10^30
def b0168 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0168.block Panels0168.accepted Panels0168.integerPanels Panels0168.aligned
    Panels0168.weightRows Panels0168.weights_checked ⟨9, by decide⟩
def b0169 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0169.block Panels0169.accepted Panels0169.integerPanels Panels0169.aligned
    Panels0169.weightRows Panels0169.weights_checked ⟨9, by decide⟩
def b0170 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0170.block Panels0170.accepted Panels0170.integerPanels Panels0170.aligned
    Panels0170.weightRows Panels0170.weights_checked ⟨9, by decide⟩
def b0171 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0171.block Panels0171.accepted Panels0171.integerPanels Panels0171.aligned
    Panels0171.weightRows Panels0171.weights_checked ⟨9, by decide⟩
def b0172 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0172.block Panels0172.accepted Panels0172.integerPanels Panels0172.aligned
    Panels0172.weightRows Panels0172.weights_checked ⟨9, by decide⟩
def b0173 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0173.block Panels0173.accepted Panels0173.integerPanels Panels0173.aligned
    Panels0173.weightRows Panels0173.weights_checked ⟨9, by decide⟩
def b0174 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0174.block Panels0174.accepted Panels0174.integerPanels Panels0174.aligned
    Panels0174.weightRows Panels0174.weights_checked ⟨9, by decide⟩
def b0175 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0175.block Panels0175.accepted Panels0175.integerPanels Panels0175.aligned
    Panels0175.weightRows Panels0175.weights_checked ⟨9, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0168, b0169, b0170, b0171, b0172, b0173, b0174, b0175]
theorem chain_checked : blockChainCheck (1894967158257301031874623425110/10^30) (2433111753263434836465548498036/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=7093816120529913610300060074030822224047619128179407279735089526714352945015184834224702638492160954045945901881263900251391178830741409656714613440908263445961575516513476460101516286366842803649538036242245677/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row09
namespace Row10
abbrev ζ : ℚ := 13793103448275862068965517241/10^30
def b0168 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0168.block Panels0168.accepted Panels0168.integerPanels Panels0168.aligned
    Panels0168.weightRows Panels0168.weights_checked ⟨10, by decide⟩
def b0169 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0169.block Panels0169.accepted Panels0169.integerPanels Panels0169.aligned
    Panels0169.weightRows Panels0169.weights_checked ⟨10, by decide⟩
def b0170 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0170.block Panels0170.accepted Panels0170.integerPanels Panels0170.aligned
    Panels0170.weightRows Panels0170.weights_checked ⟨10, by decide⟩
def b0171 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0171.block Panels0171.accepted Panels0171.integerPanels Panels0171.aligned
    Panels0171.weightRows Panels0171.weights_checked ⟨10, by decide⟩
def b0172 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0172.block Panels0172.accepted Panels0172.integerPanels Panels0172.aligned
    Panels0172.weightRows Panels0172.weights_checked ⟨10, by decide⟩
def b0173 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0173.block Panels0173.accepted Panels0173.integerPanels Panels0173.aligned
    Panels0173.weightRows Panels0173.weights_checked ⟨10, by decide⟩
def b0174 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0174.block Panels0174.accepted Panels0174.integerPanels Panels0174.aligned
    Panels0174.weightRows Panels0174.weights_checked ⟨10, by decide⟩
def b0175 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0175.block Panels0175.accepted Panels0175.integerPanels Panels0175.aligned
    Panels0175.weightRows Panels0175.weights_checked ⟨10, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0168, b0169, b0170, b0171, b0172, b0173, b0174, b0175]
theorem chain_checked : blockChainCheck (1894967158257301031874623425110/10^30) (2433111753263434836465548498036/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=7178932685505538193387867233971673189272781707318310774671832464989064570225245789905101134957831764062043580964761738221979375219364458677895326418119622278212697079444394836622544773697150578191218680410862307/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row10
namespace Row11
abbrev ζ : ℚ := 10152284263959390862944162436/10^30
def b0168 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0168.block Panels0168.accepted Panels0168.integerPanels Panels0168.aligned
    Panels0168.weightRows Panels0168.weights_checked ⟨11, by decide⟩
def b0169 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0169.block Panels0169.accepted Panels0169.integerPanels Panels0169.aligned
    Panels0169.weightRows Panels0169.weights_checked ⟨11, by decide⟩
def b0170 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0170.block Panels0170.accepted Panels0170.integerPanels Panels0170.aligned
    Panels0170.weightRows Panels0170.weights_checked ⟨11, by decide⟩
def b0171 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0171.block Panels0171.accepted Panels0171.integerPanels Panels0171.aligned
    Panels0171.weightRows Panels0171.weights_checked ⟨11, by decide⟩
def b0172 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0172.block Panels0172.accepted Panels0172.integerPanels Panels0172.aligned
    Panels0172.weightRows Panels0172.weights_checked ⟨11, by decide⟩
def b0173 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0173.block Panels0173.accepted Panels0173.integerPanels Panels0173.aligned
    Panels0173.weightRows Panels0173.weights_checked ⟨11, by decide⟩
def b0174 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0174.block Panels0174.accepted Panels0174.integerPanels Panels0174.aligned
    Panels0174.weightRows Panels0174.weights_checked ⟨11, by decide⟩
def b0175 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0175.block Panels0175.accepted Panels0175.integerPanels Panels0175.aligned
    Panels0175.weightRows Panels0175.weights_checked ⟨11, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0168, b0169, b0170, b0171, b0172, b0173, b0174, b0175]
theorem chain_checked : blockChainCheck (1894967158257301031874623425110/10^30) (2433111753263434836465548498036/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=7242725942492382001458680223355033785200458967570484248066251906188476557981644634194103737499353482912752458334351300557879178358788878794287537584081679703151822014741269936043281153555456081307167992467375557/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row11
namespace Row12
abbrev ζ : ℚ := 9950248756218905472636815920/10^30
def b0168 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0168.block Panels0168.accepted Panels0168.integerPanels Panels0168.aligned
    Panels0168.weightRows Panels0168.weights_checked ⟨12, by decide⟩
def b0169 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0169.block Panels0169.accepted Panels0169.integerPanels Panels0169.aligned
    Panels0169.weightRows Panels0169.weights_checked ⟨12, by decide⟩
def b0170 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0170.block Panels0170.accepted Panels0170.integerPanels Panels0170.aligned
    Panels0170.weightRows Panels0170.weights_checked ⟨12, by decide⟩
def b0171 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0171.block Panels0171.accepted Panels0171.integerPanels Panels0171.aligned
    Panels0171.weightRows Panels0171.weights_checked ⟨12, by decide⟩
def b0172 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0172.block Panels0172.accepted Panels0172.integerPanels Panels0172.aligned
    Panels0172.weightRows Panels0172.weights_checked ⟨12, by decide⟩
def b0173 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0173.block Panels0173.accepted Panels0173.integerPanels Panels0173.aligned
    Panels0173.weightRows Panels0173.weights_checked ⟨12, by decide⟩
def b0174 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0174.block Panels0174.accepted Panels0174.integerPanels Panels0174.aligned
    Panels0174.weightRows Panels0174.weights_checked ⟨12, by decide⟩
def b0175 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0175.block Panels0175.accepted Panels0175.integerPanels Panels0175.aligned
    Panels0175.weightRows Panels0175.weights_checked ⟨12, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0168, b0169, b0170, b0171, b0172, b0173, b0174, b0175]
theorem chain_checked : blockChainCheck (1894967158257301031874623425110/10^30) (2433111753263434836465548498036/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=7246279236131249942527172013825457223533160435069450453919349953388733128507559227261502964952119145330330231219316308712033765858616248219772413185860928566378263511278912678377577769896322504938696295659600317/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row12
#print axioms Row12.segment
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments021
