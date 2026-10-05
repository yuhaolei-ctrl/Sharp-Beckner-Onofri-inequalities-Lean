module

public import BecknerOnofri.EntropyHeatCheckedWeights
public import BecknerOnofri.EntropyHeatSegments
public import BecknerOnofri.EntropyHeatCertificate.Panels0088
public import BecknerOnofri.EntropyHeatCertificate.Panels0089
public import BecknerOnofri.EntropyHeatCertificate.Panels0090
public import BecknerOnofri.EntropyHeatCertificate.Panels0091
public import BecknerOnofri.EntropyHeatCertificate.Panels0092
public import BecknerOnofri.EntropyHeatCertificate.Panels0093
public import BecknerOnofri.EntropyHeatCertificate.Panels0094
public import BecknerOnofri.EntropyHeatCertificate.Panels0095

@[expose] public section
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments011
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace Row00
abbrev ζ : ℚ := 285714285714285714285714285714/10^30
def b0088 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0088.block Panels0088.accepted Panels0088.integerPanels Panels0088.aligned
    Panels0088.weightRows Panels0088.weights_checked ⟨0, by decide⟩
def b0089 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0089.block Panels0089.accepted Panels0089.integerPanels Panels0089.aligned
    Panels0089.weightRows Panels0089.weights_checked ⟨0, by decide⟩
def b0090 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0090.block Panels0090.accepted Panels0090.integerPanels Panels0090.aligned
    Panels0090.weightRows Panels0090.weights_checked ⟨0, by decide⟩
def b0091 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0091.block Panels0091.accepted Panels0091.integerPanels Panels0091.aligned
    Panels0091.weightRows Panels0091.weights_checked ⟨0, by decide⟩
def b0092 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0092.block Panels0092.accepted Panels0092.integerPanels Panels0092.aligned
    Panels0092.weightRows Panels0092.weights_checked ⟨0, by decide⟩
def b0093 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0093.block Panels0093.accepted Panels0093.integerPanels Panels0093.aligned
    Panels0093.weightRows Panels0093.weights_checked ⟨0, by decide⟩
def b0094 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0094.block Panels0094.accepted Panels0094.integerPanels Panels0094.aligned
    Panels0094.weightRows Panels0094.weights_checked ⟨0, by decide⟩
def b0095 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0095.block Panels0095.accepted Panels0095.integerPanels Panels0095.aligned
    Panels0095.weightRows Panels0095.weights_checked ⟨0, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0088, b0089, b0090, b0091, b0092, b0093, b0094, b0095]
theorem chain_checked : blockChainCheck (155595845692136308077834748264/10^30) (199782924607866098106963165277/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row00
namespace Row01
abbrev ζ : ℚ := 222222222222222222222222222222/10^30
def b0088 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0088.block Panels0088.accepted Panels0088.integerPanels Panels0088.aligned
    Panels0088.weightRows Panels0088.weights_checked ⟨1, by decide⟩
def b0089 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0089.block Panels0089.accepted Panels0089.integerPanels Panels0089.aligned
    Panels0089.weightRows Panels0089.weights_checked ⟨1, by decide⟩
def b0090 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0090.block Panels0090.accepted Panels0090.integerPanels Panels0090.aligned
    Panels0090.weightRows Panels0090.weights_checked ⟨1, by decide⟩
def b0091 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0091.block Panels0091.accepted Panels0091.integerPanels Panels0091.aligned
    Panels0091.weightRows Panels0091.weights_checked ⟨1, by decide⟩
def b0092 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0092.block Panels0092.accepted Panels0092.integerPanels Panels0092.aligned
    Panels0092.weightRows Panels0092.weights_checked ⟨1, by decide⟩
def b0093 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0093.block Panels0093.accepted Panels0093.integerPanels Panels0093.aligned
    Panels0093.weightRows Panels0093.weights_checked ⟨1, by decide⟩
def b0094 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0094.block Panels0094.accepted Panels0094.integerPanels Panels0094.aligned
    Panels0094.weightRows Panels0094.weights_checked ⟨1, by decide⟩
def b0095 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0095.block Panels0095.accepted Panels0095.integerPanels Panels0095.aligned
    Panels0095.weightRows Panels0095.weights_checked ⟨1, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0088, b0089, b0090, b0091, b0092, b0093, b0094, b0095]
theorem chain_checked : blockChainCheck (155595845692136308077834748264/10^30) (199782924607866098106963165277/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row01
namespace Row02
abbrev ζ : ℚ := 153846153846153846153846153846/10^30
def b0088 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0088.block Panels0088.accepted Panels0088.integerPanels Panels0088.aligned
    Panels0088.weightRows Panels0088.weights_checked ⟨2, by decide⟩
def b0089 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0089.block Panels0089.accepted Panels0089.integerPanels Panels0089.aligned
    Panels0089.weightRows Panels0089.weights_checked ⟨2, by decide⟩
def b0090 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0090.block Panels0090.accepted Panels0090.integerPanels Panels0090.aligned
    Panels0090.weightRows Panels0090.weights_checked ⟨2, by decide⟩
def b0091 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0091.block Panels0091.accepted Panels0091.integerPanels Panels0091.aligned
    Panels0091.weightRows Panels0091.weights_checked ⟨2, by decide⟩
def b0092 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0092.block Panels0092.accepted Panels0092.integerPanels Panels0092.aligned
    Panels0092.weightRows Panels0092.weights_checked ⟨2, by decide⟩
def b0093 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0093.block Panels0093.accepted Panels0093.integerPanels Panels0093.aligned
    Panels0093.weightRows Panels0093.weights_checked ⟨2, by decide⟩
def b0094 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0094.block Panels0094.accepted Panels0094.integerPanels Panels0094.aligned
    Panels0094.weightRows Panels0094.weights_checked ⟨2, by decide⟩
def b0095 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0095.block Panels0095.accepted Panels0095.integerPanels Panels0095.aligned
    Panels0095.weightRows Panels0095.weights_checked ⟨2, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0088, b0089, b0090, b0091, b0092, b0093, b0094, b0095]
theorem chain_checked : blockChainCheck (155595845692136308077834748264/10^30) (199782924607866098106963165277/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=176168749824289695573295585617374511999583539895929001925927979902923731758696690832679480422620126820299228181003749305092954358840660195150483570634523497819405643666253201574055569306792316941190850282298788/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row02
namespace Row03
abbrev ζ : ℚ := 117647058823529411764705882352/10^30
def b0088 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0088.block Panels0088.accepted Panels0088.integerPanels Panels0088.aligned
    Panels0088.weightRows Panels0088.weights_checked ⟨3, by decide⟩
def b0089 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0089.block Panels0089.accepted Panels0089.integerPanels Panels0089.aligned
    Panels0089.weightRows Panels0089.weights_checked ⟨3, by decide⟩
def b0090 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0090.block Panels0090.accepted Panels0090.integerPanels Panels0090.aligned
    Panels0090.weightRows Panels0090.weights_checked ⟨3, by decide⟩
def b0091 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0091.block Panels0091.accepted Panels0091.integerPanels Panels0091.aligned
    Panels0091.weightRows Panels0091.weights_checked ⟨3, by decide⟩
def b0092 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0092.block Panels0092.accepted Panels0092.integerPanels Panels0092.aligned
    Panels0092.weightRows Panels0092.weights_checked ⟨3, by decide⟩
def b0093 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0093.block Panels0093.accepted Panels0093.integerPanels Panels0093.aligned
    Panels0093.weightRows Panels0093.weights_checked ⟨3, by decide⟩
def b0094 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0094.block Panels0094.accepted Panels0094.integerPanels Panels0094.aligned
    Panels0094.weightRows Panels0094.weights_checked ⟨3, by decide⟩
def b0095 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0095.block Panels0095.accepted Panels0095.integerPanels Panels0095.aligned
    Panels0095.weightRows Panels0095.weights_checked ⟨3, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0088, b0089, b0090, b0091, b0092, b0093, b0094, b0095]
theorem chain_checked : blockChainCheck (155595845692136308077834748264/10^30) (199782924607866098106963165277/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=6920648652749113488067874522240415337635859411087381187186495712080918472284481633031392630307092641539893284954925334904296979237943399112244466701668379170449121334716394947804120054040840171292455044821080580/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row03
namespace Row04
abbrev ζ : ℚ := 86956521739130434782608695652/10^30
def b0088 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0088.block Panels0088.accepted Panels0088.integerPanels Panels0088.aligned
    Panels0088.weightRows Panels0088.weights_checked ⟨4, by decide⟩
def b0089 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0089.block Panels0089.accepted Panels0089.integerPanels Panels0089.aligned
    Panels0089.weightRows Panels0089.weights_checked ⟨4, by decide⟩
def b0090 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0090.block Panels0090.accepted Panels0090.integerPanels Panels0090.aligned
    Panels0090.weightRows Panels0090.weights_checked ⟨4, by decide⟩
def b0091 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0091.block Panels0091.accepted Panels0091.integerPanels Panels0091.aligned
    Panels0091.weightRows Panels0091.weights_checked ⟨4, by decide⟩
def b0092 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0092.block Panels0092.accepted Panels0092.integerPanels Panels0092.aligned
    Panels0092.weightRows Panels0092.weights_checked ⟨4, by decide⟩
def b0093 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0093.block Panels0093.accepted Panels0093.integerPanels Panels0093.aligned
    Panels0093.weightRows Panels0093.weights_checked ⟨4, by decide⟩
def b0094 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0094.block Panels0094.accepted Panels0094.integerPanels Panels0094.aligned
    Panels0094.weightRows Panels0094.weights_checked ⟨4, by decide⟩
def b0095 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0095.block Panels0095.accepted Panels0095.integerPanels Panels0095.aligned
    Panels0095.weightRows Panels0095.weights_checked ⟨4, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0088, b0089, b0090, b0091, b0092, b0093, b0094, b0095]
theorem chain_checked : blockChainCheck (155595845692136308077834748264/10^30) (199782924607866098106963165277/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=49753606475273891490472009082758004705424496797876825897956548881747978196125454726025238925344295553948566271427821247776760301322263576452684457972128139677454040388867015037430292725008295946073193209104841380/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row04
namespace Row05
abbrev ζ : ℚ := 64516129032258064516129032258/10^30
def b0088 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0088.block Panels0088.accepted Panels0088.integerPanels Panels0088.aligned
    Panels0088.weightRows Panels0088.weights_checked ⟨5, by decide⟩
def b0089 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0089.block Panels0089.accepted Panels0089.integerPanels Panels0089.aligned
    Panels0089.weightRows Panels0089.weights_checked ⟨5, by decide⟩
def b0090 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0090.block Panels0090.accepted Panels0090.integerPanels Panels0090.aligned
    Panels0090.weightRows Panels0090.weights_checked ⟨5, by decide⟩
def b0091 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0091.block Panels0091.accepted Panels0091.integerPanels Panels0091.aligned
    Panels0091.weightRows Panels0091.weights_checked ⟨5, by decide⟩
def b0092 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0092.block Panels0092.accepted Panels0092.integerPanels Panels0092.aligned
    Panels0092.weightRows Panels0092.weights_checked ⟨5, by decide⟩
def b0093 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0093.block Panels0093.accepted Panels0093.integerPanels Panels0093.aligned
    Panels0093.weightRows Panels0093.weights_checked ⟨5, by decide⟩
def b0094 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0094.block Panels0094.accepted Panels0094.integerPanels Panels0094.aligned
    Panels0094.weightRows Panels0094.weights_checked ⟨5, by decide⟩
def b0095 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0095.block Panels0095.accepted Panels0095.integerPanels Panels0095.aligned
    Panels0095.weightRows Panels0095.weights_checked ⟨5, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0088, b0089, b0090, b0091, b0092, b0093, b0094, b0095]
theorem chain_checked : blockChainCheck (155595845692136308077834748264/10^30) (199782924607866098106963165277/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=148638402902818671806548226018101661026769375214514804853511614783876844819291783035766722294107524960320854640900449997964057239198519682488940866032494813383928053192306178335017129350461020214239916557073066692/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row05
namespace Row06
abbrev ζ : ℚ := 46511627906976744186046511627/10^30
def b0088 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0088.block Panels0088.accepted Panels0088.integerPanels Panels0088.aligned
    Panels0088.weightRows Panels0088.weights_checked ⟨6, by decide⟩
def b0089 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0089.block Panels0089.accepted Panels0089.integerPanels Panels0089.aligned
    Panels0089.weightRows Panels0089.weights_checked ⟨6, by decide⟩
def b0090 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0090.block Panels0090.accepted Panels0090.integerPanels Panels0090.aligned
    Panels0090.weightRows Panels0090.weights_checked ⟨6, by decide⟩
def b0091 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0091.block Panels0091.accepted Panels0091.integerPanels Panels0091.aligned
    Panels0091.weightRows Panels0091.weights_checked ⟨6, by decide⟩
def b0092 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0092.block Panels0092.accepted Panels0092.integerPanels Panels0092.aligned
    Panels0092.weightRows Panels0092.weights_checked ⟨6, by decide⟩
def b0093 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0093.block Panels0093.accepted Panels0093.integerPanels Panels0093.aligned
    Panels0093.weightRows Panels0093.weights_checked ⟨6, by decide⟩
def b0094 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0094.block Panels0094.accepted Panels0094.integerPanels Panels0094.aligned
    Panels0094.weightRows Panels0094.weights_checked ⟨6, by decide⟩
def b0095 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0095.block Panels0095.accepted Panels0095.integerPanels Panels0095.aligned
    Panels0095.weightRows Panels0095.weights_checked ⟨6, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0088, b0089, b0090, b0091, b0092, b0093, b0094, b0095]
theorem chain_checked : blockChainCheck (155595845692136308077834748264/10^30) (199782924607866098106963165277/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=311226689100667480513944747649406724413939997867174568245501508831381074856365668139475068623807953648168015408484733958211650333355493016784564022035852861919454290876657642463106713690077684324992378862456217980/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row06
namespace Row07
abbrev ζ : ℚ := 33898305084745762711864406779/10^30
def b0088 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0088.block Panels0088.accepted Panels0088.integerPanels Panels0088.aligned
    Panels0088.weightRows Panels0088.weights_checked ⟨7, by decide⟩
def b0089 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0089.block Panels0089.accepted Panels0089.integerPanels Panels0089.aligned
    Panels0089.weightRows Panels0089.weights_checked ⟨7, by decide⟩
def b0090 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0090.block Panels0090.accepted Panels0090.integerPanels Panels0090.aligned
    Panels0090.weightRows Panels0090.weights_checked ⟨7, by decide⟩
def b0091 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0091.block Panels0091.accepted Panels0091.integerPanels Panels0091.aligned
    Panels0091.weightRows Panels0091.weights_checked ⟨7, by decide⟩
def b0092 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0092.block Panels0092.accepted Panels0092.integerPanels Panels0092.aligned
    Panels0092.weightRows Panels0092.weights_checked ⟨7, by decide⟩
def b0093 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0093.block Panels0093.accepted Panels0093.integerPanels Panels0093.aligned
    Panels0093.weightRows Panels0093.weights_checked ⟨7, by decide⟩
def b0094 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0094.block Panels0094.accepted Panels0094.integerPanels Panels0094.aligned
    Panels0094.weightRows Panels0094.weights_checked ⟨7, by decide⟩
def b0095 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0095.block Panels0095.accepted Panels0095.integerPanels Panels0095.aligned
    Panels0095.weightRows Panels0095.weights_checked ⟨7, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0088, b0089, b0090, b0091, b0092, b0093, b0094, b0095]
theorem chain_checked : blockChainCheck (155595845692136308077834748264/10^30) (199782924607866098106963165277/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=493792982083756591141408902477379290112262511080015598353774936819107124305152987512407555385753632067231825843771968116221616732853931679959612688356656361481341953313395660481120083338796521738942141538323955964/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row07
namespace Row08
abbrev ζ : ℚ := 25316455696202531645569620253/10^30
def b0088 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0088.block Panels0088.accepted Panels0088.integerPanels Panels0088.aligned
    Panels0088.weightRows Panels0088.weights_checked ⟨8, by decide⟩
def b0089 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0089.block Panels0089.accepted Panels0089.integerPanels Panels0089.aligned
    Panels0089.weightRows Panels0089.weights_checked ⟨8, by decide⟩
def b0090 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0090.block Panels0090.accepted Panels0090.integerPanels Panels0090.aligned
    Panels0090.weightRows Panels0090.weights_checked ⟨8, by decide⟩
def b0091 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0091.block Panels0091.accepted Panels0091.integerPanels Panels0091.aligned
    Panels0091.weightRows Panels0091.weights_checked ⟨8, by decide⟩
def b0092 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0092.block Panels0092.accepted Panels0092.integerPanels Panels0092.aligned
    Panels0092.weightRows Panels0092.weights_checked ⟨8, by decide⟩
def b0093 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0093.block Panels0093.accepted Panels0093.integerPanels Panels0093.aligned
    Panels0093.weightRows Panels0093.weights_checked ⟨8, by decide⟩
def b0094 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0094.block Panels0094.accepted Panels0094.integerPanels Panels0094.aligned
    Panels0094.weightRows Panels0094.weights_checked ⟨8, by decide⟩
def b0095 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0095.block Panels0095.accepted Panels0095.integerPanels Panels0095.aligned
    Panels0095.weightRows Panels0095.weights_checked ⟨8, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0088, b0089, b0090, b0091, b0092, b0093, b0094, b0095]
theorem chain_checked : blockChainCheck (155595845692136308077834748264/10^30) (199782924607866098106963165277/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=661265333871847791844917443566756070592727385562468789135373212749311627233218187376171184230479141319623749830570746746189206731261329527389067177160156302624584760270071436010066384891403551561831466802793150012/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row08
namespace Row09
abbrev ζ : ℚ := 18691588785046728971962616822/10^30
def b0088 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0088.block Panels0088.accepted Panels0088.integerPanels Panels0088.aligned
    Panels0088.weightRows Panels0088.weights_checked ⟨9, by decide⟩
def b0089 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0089.block Panels0089.accepted Panels0089.integerPanels Panels0089.aligned
    Panels0089.weightRows Panels0089.weights_checked ⟨9, by decide⟩
def b0090 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0090.block Panels0090.accepted Panels0090.integerPanels Panels0090.aligned
    Panels0090.weightRows Panels0090.weights_checked ⟨9, by decide⟩
def b0091 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0091.block Panels0091.accepted Panels0091.integerPanels Panels0091.aligned
    Panels0091.weightRows Panels0091.weights_checked ⟨9, by decide⟩
def b0092 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0092.block Panels0092.accepted Panels0092.integerPanels Panels0092.aligned
    Panels0092.weightRows Panels0092.weights_checked ⟨9, by decide⟩
def b0093 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0093.block Panels0093.accepted Panels0093.integerPanels Panels0093.aligned
    Panels0093.weightRows Panels0093.weights_checked ⟨9, by decide⟩
def b0094 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0094.block Panels0094.accepted Panels0094.integerPanels Panels0094.aligned
    Panels0094.weightRows Panels0094.weights_checked ⟨9, by decide⟩
def b0095 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0095.block Panels0095.accepted Panels0095.integerPanels Panels0095.aligned
    Panels0095.weightRows Panels0095.weights_checked ⟨9, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0088, b0089, b0090, b0091, b0092, b0093, b0094, b0095]
theorem chain_checked : blockChainCheck (155595845692136308077834748264/10^30) (199782924607866098106963165277/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=819574997211190622231990614625434506593691319632773520996621799277414020393587854004212595384117793430924008942920485590368281950759198819503631350069442001385248307991631313235783388122371699999720098925033339300/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row09
namespace Row10
abbrev ζ : ℚ := 13793103448275862068965517241/10^30
def b0088 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0088.block Panels0088.accepted Panels0088.integerPanels Panels0088.aligned
    Panels0088.weightRows Panels0088.weights_checked ⟨10, by decide⟩
def b0089 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0089.block Panels0089.accepted Panels0089.integerPanels Panels0089.aligned
    Panels0089.weightRows Panels0089.weights_checked ⟨10, by decide⟩
def b0090 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0090.block Panels0090.accepted Panels0090.integerPanels Panels0090.aligned
    Panels0090.weightRows Panels0090.weights_checked ⟨10, by decide⟩
def b0091 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0091.block Panels0091.accepted Panels0091.integerPanels Panels0091.aligned
    Panels0091.weightRows Panels0091.weights_checked ⟨10, by decide⟩
def b0092 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0092.block Panels0092.accepted Panels0092.integerPanels Panels0092.aligned
    Panels0092.weightRows Panels0092.weights_checked ⟨10, by decide⟩
def b0093 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0093.block Panels0093.accepted Panels0093.integerPanels Panels0093.aligned
    Panels0093.weightRows Panels0093.weights_checked ⟨10, by decide⟩
def b0094 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0094.block Panels0094.accepted Panels0094.integerPanels Panels0094.aligned
    Panels0094.weightRows Panels0094.weights_checked ⟨10, by decide⟩
def b0095 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0095.block Panels0095.accepted Panels0095.integerPanels Panels0095.aligned
    Panels0095.weightRows Panels0095.weights_checked ⟨10, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0088, b0089, b0090, b0091, b0092, b0093, b0094, b0095]
theorem chain_checked : blockChainCheck (155595845692136308077834748264/10^30) (199782924607866098106963165277/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=955188887947520516016130174043396202832559736842709709657510279971984233526190575066378441199818697447217228738032794003198286707939759105616766817523373949826276184332205371138563234314003088134198226047052839708/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row10
namespace Row11
abbrev ζ : ℚ := 10152284263959390862944162436/10^30
def b0088 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0088.block Panels0088.accepted Panels0088.integerPanels Panels0088.aligned
    Panels0088.weightRows Panels0088.weights_checked ⟨11, by decide⟩
def b0089 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0089.block Panels0089.accepted Panels0089.integerPanels Panels0089.aligned
    Panels0089.weightRows Panels0089.weights_checked ⟨11, by decide⟩
def b0090 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0090.block Panels0090.accepted Panels0090.integerPanels Panels0090.aligned
    Panels0090.weightRows Panels0090.weights_checked ⟨11, by decide⟩
def b0091 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0091.block Panels0091.accepted Panels0091.integerPanels Panels0091.aligned
    Panels0091.weightRows Panels0091.weights_checked ⟨11, by decide⟩
def b0092 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0092.block Panels0092.accepted Panels0092.integerPanels Panels0092.aligned
    Panels0092.weightRows Panels0092.weights_checked ⟨11, by decide⟩
def b0093 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0093.block Panels0093.accepted Panels0093.integerPanels Panels0093.aligned
    Panels0093.weightRows Panels0093.weights_checked ⟨11, by decide⟩
def b0094 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0094.block Panels0094.accepted Panels0094.integerPanels Panels0094.aligned
    Panels0094.weightRows Panels0094.weights_checked ⟨11, by decide⟩
def b0095 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0095.block Panels0095.accepted Panels0095.integerPanels Panels0095.aligned
    Panels0095.weightRows Panels0095.weights_checked ⟨11, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0088, b0089, b0090, b0091, b0092, b0093, b0094, b0095]
theorem chain_checked : blockChainCheck (155595845692136308077834748264/10^30) (199782924607866098106963165277/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=1067235595817932400969559623998930326262859598745049264608078362427869842901187725893193608118211470868384321788481751175595783264813270739503685473112279701257854979456170893680202299320997717809783114233093035428/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row11
namespace Row12
abbrev ζ : ℚ := 9950248756218905472636815920/10^30
def b0088 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0088.block Panels0088.accepted Panels0088.integerPanels Panels0088.aligned
    Panels0088.weightRows Panels0088.weights_checked ⟨12, by decide⟩
def b0089 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0089.block Panels0089.accepted Panels0089.integerPanels Panels0089.aligned
    Panels0089.weightRows Panels0089.weights_checked ⟨12, by decide⟩
def b0090 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0090.block Panels0090.accepted Panels0090.integerPanels Panels0090.aligned
    Panels0090.weightRows Panels0090.weights_checked ⟨12, by decide⟩
def b0091 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0091.block Panels0091.accepted Panels0091.integerPanels Panels0091.aligned
    Panels0091.weightRows Panels0091.weights_checked ⟨12, by decide⟩
def b0092 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0092.block Panels0092.accepted Panels0092.integerPanels Panels0092.aligned
    Panels0092.weightRows Panels0092.weights_checked ⟨12, by decide⟩
def b0093 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0093.block Panels0093.accepted Panels0093.integerPanels Panels0093.aligned
    Panels0093.weightRows Panels0093.weights_checked ⟨12, by decide⟩
def b0094 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0094.block Panels0094.accepted Panels0094.integerPanels Panels0094.aligned
    Panels0094.weightRows Panels0094.weights_checked ⟨12, by decide⟩
def b0095 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0095.block Panels0095.accepted Panels0095.integerPanels Panels0095.aligned
    Panels0095.weightRows Panels0095.weights_checked ⟨12, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0088, b0089, b0090, b0091, b0092, b0093, b0094, b0095]
theorem chain_checked : blockChainCheck (155595845692136308077834748264/10^30) (199782924607866098106963165277/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=1073749788987099437443647740785217946799123580656783525769467797240256907629282153258127888623264718625586430790033408094120679175662626217298262916781487997447738090347339213985437193303044113549451402699914760196/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row12
#print axioms Row12.segment
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments011
