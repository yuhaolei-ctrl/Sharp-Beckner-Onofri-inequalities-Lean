module

public import BecknerOnofri.EntropyHeatCheckedWeights
public import BecknerOnofri.EntropyHeatSegments
public import BecknerOnofri.EntropyHeatCertificate.Panels0136
public import BecknerOnofri.EntropyHeatCertificate.Panels0137
public import BecknerOnofri.EntropyHeatCertificate.Panels0138
public import BecknerOnofri.EntropyHeatCertificate.Panels0139
public import BecknerOnofri.EntropyHeatCertificate.Panels0140
public import BecknerOnofri.EntropyHeatCertificate.Panels0141
public import BecknerOnofri.EntropyHeatCertificate.Panels0142
public import BecknerOnofri.EntropyHeatCertificate.Panels0143

@[expose] public section
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments017
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace Row00
abbrev ζ : ℚ := 285714285714285714285714285714/10^30
def b0136 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0136.block Panels0136.accepted Panels0136.integerPanels Panels0136.aligned
    Panels0136.weightRows Panels0136.weights_checked ⟨0, by decide⟩
def b0137 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0137.block Panels0137.accepted Panels0137.integerPanels Panels0137.aligned
    Panels0137.weightRows Panels0137.weights_checked ⟨0, by decide⟩
def b0138 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0138.block Panels0138.accepted Panels0138.integerPanels Panels0138.aligned
    Panels0138.weightRows Panels0138.weights_checked ⟨0, by decide⟩
def b0139 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0139.block Panels0139.accepted Panels0139.integerPanels Panels0139.aligned
    Panels0139.weightRows Panels0139.weights_checked ⟨0, by decide⟩
def b0140 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0140.block Panels0140.accepted Panels0140.integerPanels Panels0140.aligned
    Panels0140.weightRows Panels0140.weights_checked ⟨0, by decide⟩
def b0141 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0141.block Panels0141.accepted Panels0141.integerPanels Panels0141.aligned
    Panels0141.weightRows Panels0141.weights_checked ⟨0, by decide⟩
def b0142 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0142.block Panels0142.accepted Panels0142.integerPanels Panels0142.aligned
    Panels0142.weightRows Panels0142.weights_checked ⟨0, by decide⟩
def b0143 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0143.block Panels0143.accepted Panels0143.integerPanels Panels0143.aligned
    Panels0143.weightRows Panels0143.weights_checked ⟨0, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0136, b0137, b0138, b0139, b0140, b0141, b0142, b0143]
theorem chain_checked : blockChainCheck (697204548152650608931256665441/10^30) (895201045119432327478050281094/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=61871565759854721611490670728851308656478405508181855516618715604725537477019222784079768586666039669710055770029089129682433312165942719775850344802585600507869938458163125214398768655138104696643616317008450216/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row00
namespace Row01
abbrev ζ : ℚ := 222222222222222222222222222222/10^30
def b0136 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0136.block Panels0136.accepted Panels0136.integerPanels Panels0136.aligned
    Panels0136.weightRows Panels0136.weights_checked ⟨1, by decide⟩
def b0137 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0137.block Panels0137.accepted Panels0137.integerPanels Panels0137.aligned
    Panels0137.weightRows Panels0137.weights_checked ⟨1, by decide⟩
def b0138 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0138.block Panels0138.accepted Panels0138.integerPanels Panels0138.aligned
    Panels0138.weightRows Panels0138.weights_checked ⟨1, by decide⟩
def b0139 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0139.block Panels0139.accepted Panels0139.integerPanels Panels0139.aligned
    Panels0139.weightRows Panels0139.weights_checked ⟨1, by decide⟩
def b0140 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0140.block Panels0140.accepted Panels0140.integerPanels Panels0140.aligned
    Panels0140.weightRows Panels0140.weights_checked ⟨1, by decide⟩
def b0141 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0141.block Panels0141.accepted Panels0141.integerPanels Panels0141.aligned
    Panels0141.weightRows Panels0141.weights_checked ⟨1, by decide⟩
def b0142 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0142.block Panels0142.accepted Panels0142.integerPanels Panels0142.aligned
    Panels0142.weightRows Panels0142.weights_checked ⟨1, by decide⟩
def b0143 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0143.block Panels0143.accepted Panels0143.integerPanels Panels0143.aligned
    Panels0143.weightRows Panels0143.weights_checked ⟨1, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0136, b0137, b0138, b0139, b0140, b0141, b0142, b0143]
theorem chain_checked : blockChainCheck (697204548152650608931256665441/10^30) (895201045119432327478050281094/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=112294058038269660769824004181808463957133606616100634349574563827818096175004970835165093635957355784961959804105759611163687984820717366985578948381272908173408397959979150235512477095836399134652969418699637672/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row01
namespace Row02
abbrev ζ : ℚ := 153846153846153846153846153846/10^30
def b0136 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0136.block Panels0136.accepted Panels0136.integerPanels Panels0136.aligned
    Panels0136.weightRows Panels0136.weights_checked ⟨2, by decide⟩
def b0137 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0137.block Panels0137.accepted Panels0137.integerPanels Panels0137.aligned
    Panels0137.weightRows Panels0137.weights_checked ⟨2, by decide⟩
def b0138 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0138.block Panels0138.accepted Panels0138.integerPanels Panels0138.aligned
    Panels0138.weightRows Panels0138.weights_checked ⟨2, by decide⟩
def b0139 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0139.block Panels0139.accepted Panels0139.integerPanels Panels0139.aligned
    Panels0139.weightRows Panels0139.weights_checked ⟨2, by decide⟩
def b0140 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0140.block Panels0140.accepted Panels0140.integerPanels Panels0140.aligned
    Panels0140.weightRows Panels0140.weights_checked ⟨2, by decide⟩
def b0141 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0141.block Panels0141.accepted Panels0141.integerPanels Panels0141.aligned
    Panels0141.weightRows Panels0141.weights_checked ⟨2, by decide⟩
def b0142 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0142.block Panels0142.accepted Panels0142.integerPanels Panels0142.aligned
    Panels0142.weightRows Panels0142.weights_checked ⟨2, by decide⟩
def b0143 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0143.block Panels0143.accepted Panels0143.integerPanels Panels0143.aligned
    Panels0143.weightRows Panels0143.weights_checked ⟨2, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0136, b0137, b0138, b0139, b0140, b0141, b0142, b0143]
theorem chain_checked : blockChainCheck (697204548152650608931256665441/10^30) (895201045119432327478050281094/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=199312470647203345644332276707176851689857953701227679660332975072422796268472574366200203961605224140722388524660949925202132033321484362857374133583031884887770900669307700973282474248250018525153238304762829480/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row02
namespace Row03
abbrev ζ : ℚ := 117647058823529411764705882352/10^30
def b0136 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0136.block Panels0136.accepted Panels0136.integerPanels Panels0136.aligned
    Panels0136.weightRows Panels0136.weights_checked ⟨3, by decide⟩
def b0137 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0137.block Panels0137.accepted Panels0137.integerPanels Panels0137.aligned
    Panels0137.weightRows Panels0137.weights_checked ⟨3, by decide⟩
def b0138 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0138.block Panels0138.accepted Panels0138.integerPanels Panels0138.aligned
    Panels0138.weightRows Panels0138.weights_checked ⟨3, by decide⟩
def b0139 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0139.block Panels0139.accepted Panels0139.integerPanels Panels0139.aligned
    Panels0139.weightRows Panels0139.weights_checked ⟨3, by decide⟩
def b0140 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0140.block Panels0140.accepted Panels0140.integerPanels Panels0140.aligned
    Panels0140.weightRows Panels0140.weights_checked ⟨3, by decide⟩
def b0141 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0141.block Panels0141.accepted Panels0141.integerPanels Panels0141.aligned
    Panels0141.weightRows Panels0141.weights_checked ⟨3, by decide⟩
def b0142 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0142.block Panels0142.accepted Panels0142.integerPanels Panels0142.aligned
    Panels0142.weightRows Panels0142.weights_checked ⟨3, by decide⟩
def b0143 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0143.block Panels0143.accepted Panels0143.integerPanels Panels0143.aligned
    Panels0143.weightRows Panels0143.weights_checked ⟨3, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0136, b0137, b0138, b0139, b0140, b0141, b0142, b0143]
theorem chain_checked : blockChainCheck (697204548152650608931256665441/10^30) (895201045119432327478050281094/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=263661889433944759187160256383652223619712347751773250128895352432436396204775142500443959169115778453998826299884686455506680765500455557369563106551635058022074831042050724020249142459177463355902841231991790152/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row03
namespace Row04
abbrev ζ : ℚ := 86956521739130434782608695652/10^30
def b0136 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0136.block Panels0136.accepted Panels0136.integerPanels Panels0136.aligned
    Panels0136.weightRows Panels0136.weights_checked ⟨4, by decide⟩
def b0137 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0137.block Panels0137.accepted Panels0137.integerPanels Panels0137.aligned
    Panels0137.weightRows Panels0137.weights_checked ⟨4, by decide⟩
def b0138 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0138.block Panels0138.accepted Panels0138.integerPanels Panels0138.aligned
    Panels0138.weightRows Panels0138.weights_checked ⟨4, by decide⟩
def b0139 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0139.block Panels0139.accepted Panels0139.integerPanels Panels0139.aligned
    Panels0139.weightRows Panels0139.weights_checked ⟨4, by decide⟩
def b0140 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0140.block Panels0140.accepted Panels0140.integerPanels Panels0140.aligned
    Panels0140.weightRows Panels0140.weights_checked ⟨4, by decide⟩
def b0141 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0141.block Panels0141.accepted Panels0141.integerPanels Panels0141.aligned
    Panels0141.weightRows Panels0141.weights_checked ⟨4, by decide⟩
def b0142 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0142.block Panels0142.accepted Panels0142.integerPanels Panels0142.aligned
    Panels0142.weightRows Panels0142.weights_checked ⟨4, by decide⟩
def b0143 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0143.block Panels0143.accepted Panels0143.integerPanels Panels0143.aligned
    Panels0143.weightRows Panels0143.weights_checked ⟨4, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0136, b0137, b0138, b0139, b0140, b0141, b0142, b0143]
theorem chain_checked : blockChainCheck (697204548152650608931256665441/10^30) (895201045119432327478050281094/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=330471554300377870793479856134681174869869109564171184267031542028542721227604505335217497825122831514078825781033490021592903813191097228502402964049928680787197267397758652537084933248308266051577100536496586952/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row04
namespace Row05
abbrev ζ : ℚ := 64516129032258064516129032258/10^30
def b0136 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0136.block Panels0136.accepted Panels0136.integerPanels Panels0136.aligned
    Panels0136.weightRows Panels0136.weights_checked ⟨5, by decide⟩
def b0137 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0137.block Panels0137.accepted Panels0137.integerPanels Panels0137.aligned
    Panels0137.weightRows Panels0137.weights_checked ⟨5, by decide⟩
def b0138 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0138.block Panels0138.accepted Panels0138.integerPanels Panels0138.aligned
    Panels0138.weightRows Panels0138.weights_checked ⟨5, by decide⟩
def b0139 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0139.block Panels0139.accepted Panels0139.integerPanels Panels0139.aligned
    Panels0139.weightRows Panels0139.weights_checked ⟨5, by decide⟩
def b0140 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0140.block Panels0140.accepted Panels0140.integerPanels Panels0140.aligned
    Panels0140.weightRows Panels0140.weights_checked ⟨5, by decide⟩
def b0141 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0141.block Panels0141.accepted Panels0141.integerPanels Panels0141.aligned
    Panels0141.weightRows Panels0141.weights_checked ⟨5, by decide⟩
def b0142 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0142.block Panels0142.accepted Panels0142.integerPanels Panels0142.aligned
    Panels0142.weightRows Panels0142.weights_checked ⟨5, by decide⟩
def b0143 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0143.block Panels0143.accepted Panels0143.integerPanels Panels0143.aligned
    Panels0143.weightRows Panels0143.weights_checked ⟨5, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0136, b0137, b0138, b0139, b0140, b0141, b0142, b0143]
theorem chain_checked : blockChainCheck (697204548152650608931256665441/10^30) (895201045119432327478050281094/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=387451012869141457381461328514866309497774370804382190328217962157096505601190859778703566168578391354450149143522032216517585075947244975276019705244901624155111981026448366864553859605222935677919163477016882344/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row05
namespace Row06
abbrev ζ : ℚ := 46511627906976744186046511627/10^30
def b0136 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0136.block Panels0136.accepted Panels0136.integerPanels Panels0136.aligned
    Panels0136.weightRows Panels0136.weights_checked ⟨6, by decide⟩
def b0137 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0137.block Panels0137.accepted Panels0137.integerPanels Panels0137.aligned
    Panels0137.weightRows Panels0137.weights_checked ⟨6, by decide⟩
def b0138 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0138.block Panels0138.accepted Panels0138.integerPanels Panels0138.aligned
    Panels0138.weightRows Panels0138.weights_checked ⟨6, by decide⟩
def b0139 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0139.block Panels0139.accepted Panels0139.integerPanels Panels0139.aligned
    Panels0139.weightRows Panels0139.weights_checked ⟨6, by decide⟩
def b0140 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0140.block Panels0140.accepted Panels0140.integerPanels Panels0140.aligned
    Panels0140.weightRows Panels0140.weights_checked ⟨6, by decide⟩
def b0141 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0141.block Panels0141.accepted Panels0141.integerPanels Panels0141.aligned
    Panels0141.weightRows Panels0141.weights_checked ⟨6, by decide⟩
def b0142 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0142.block Panels0142.accepted Panels0142.integerPanels Panels0142.aligned
    Panels0142.weightRows Panels0142.weights_checked ⟨6, by decide⟩
def b0143 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0143.block Panels0143.accepted Panels0143.integerPanels Panels0143.aligned
    Panels0143.weightRows Panels0143.weights_checked ⟨6, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0136, b0137, b0138, b0139, b0140, b0141, b0142, b0143]
theorem chain_checked : blockChainCheck (697204548152650608931256665441/10^30) (895201045119432327478050281094/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=438665566671037289581550816885964002934002967355157745620227594568340148889223194781154091000064538970594141201354951059348941846903599366385324874399928028838517018991694989647370996330044418633867232358582935552/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row06
namespace Row07
abbrev ζ : ℚ := 33898305084745762711864406779/10^30
def b0136 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0136.block Panels0136.accepted Panels0136.integerPanels Panels0136.aligned
    Panels0136.weightRows Panels0136.weights_checked ⟨7, by decide⟩
def b0137 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0137.block Panels0137.accepted Panels0137.integerPanels Panels0137.aligned
    Panels0137.weightRows Panels0137.weights_checked ⟨7, by decide⟩
def b0138 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0138.block Panels0138.accepted Panels0138.integerPanels Panels0138.aligned
    Panels0138.weightRows Panels0138.weights_checked ⟨7, by decide⟩
def b0139 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0139.block Panels0139.accepted Panels0139.integerPanels Panels0139.aligned
    Panels0139.weightRows Panels0139.weights_checked ⟨7, by decide⟩
def b0140 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0140.block Panels0140.accepted Panels0140.integerPanels Panels0140.aligned
    Panels0140.weightRows Panels0140.weights_checked ⟨7, by decide⟩
def b0141 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0141.block Panels0141.accepted Panels0141.integerPanels Panels0141.aligned
    Panels0141.weightRows Panels0141.weights_checked ⟨7, by decide⟩
def b0142 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0142.block Panels0142.accepted Panels0142.integerPanels Panels0142.aligned
    Panels0142.weightRows Panels0142.weights_checked ⟨7, by decide⟩
def b0143 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0143.block Panels0143.accepted Panels0143.integerPanels Panels0143.aligned
    Panels0143.weightRows Panels0143.weights_checked ⟨7, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0136, b0137, b0138, b0139, b0140, b0141, b0142, b0143]
theorem chain_checked : blockChainCheck (697204548152650608931256665441/10^30) (895201045119432327478050281094/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=477684764749652284392103611384687624077833995209969348493310640132433349566091832367175679027169826019713723374697363043211068626023661379159208193209210320218325389998417284021554106675146550199787744464990459456/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row07
namespace Row08
abbrev ζ : ℚ := 25316455696202531645569620253/10^30
def b0136 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0136.block Panels0136.accepted Panels0136.integerPanels Panels0136.aligned
    Panels0136.weightRows Panels0136.weights_checked ⟨8, by decide⟩
def b0137 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0137.block Panels0137.accepted Panels0137.integerPanels Panels0137.aligned
    Panels0137.weightRows Panels0137.weights_checked ⟨8, by decide⟩
def b0138 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0138.block Panels0138.accepted Panels0138.integerPanels Panels0138.aligned
    Panels0138.weightRows Panels0138.weights_checked ⟨8, by decide⟩
def b0139 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0139.block Panels0139.accepted Panels0139.integerPanels Panels0139.aligned
    Panels0139.weightRows Panels0139.weights_checked ⟨8, by decide⟩
def b0140 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0140.block Panels0140.accepted Panels0140.integerPanels Panels0140.aligned
    Panels0140.weightRows Panels0140.weights_checked ⟨8, by decide⟩
def b0141 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0141.block Panels0141.accepted Panels0141.integerPanels Panels0141.aligned
    Panels0141.weightRows Panels0141.weights_checked ⟨8, by decide⟩
def b0142 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0142.block Panels0142.accepted Panels0142.integerPanels Panels0142.aligned
    Panels0142.weightRows Panels0142.weights_checked ⟨8, by decide⟩
def b0143 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0143.block Panels0143.accepted Panels0143.integerPanels Panels0143.aligned
    Panels0143.weightRows Panels0143.weights_checked ⟨8, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0136, b0137, b0138, b0139, b0140, b0141, b0142, b0143]
theorem chain_checked : blockChainCheck (697204548152650608931256665441/10^30) (895201045119432327478050281094/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=505792940401352496362114845114193501315802529179976334504781307787558437865473977869153309045452482344881123231678777137328928541101364647459039972861788170020462188127480600573952549539210951866888578310317114264/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row08
namespace Row09
abbrev ζ : ℚ := 18691588785046728971962616822/10^30
def b0136 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0136.block Panels0136.accepted Panels0136.integerPanels Panels0136.aligned
    Panels0136.weightRows Panels0136.weights_checked ⟨9, by decide⟩
def b0137 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0137.block Panels0137.accepted Panels0137.integerPanels Panels0137.aligned
    Panels0137.weightRows Panels0137.weights_checked ⟨9, by decide⟩
def b0138 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0138.block Panels0138.accepted Panels0138.integerPanels Panels0138.aligned
    Panels0138.weightRows Panels0138.weights_checked ⟨9, by decide⟩
def b0139 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0139.block Panels0139.accepted Panels0139.integerPanels Panels0139.aligned
    Panels0139.weightRows Panels0139.weights_checked ⟨9, by decide⟩
def b0140 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0140.block Panels0140.accepted Panels0140.integerPanels Panels0140.aligned
    Panels0140.weightRows Panels0140.weights_checked ⟨9, by decide⟩
def b0141 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0141.block Panels0141.accepted Panels0141.integerPanels Panels0141.aligned
    Panels0141.weightRows Panels0141.weights_checked ⟨9, by decide⟩
def b0142 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0142.block Panels0142.accepted Panels0142.integerPanels Panels0142.aligned
    Panels0142.weightRows Panels0142.weights_checked ⟨9, by decide⟩
def b0143 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0143.block Panels0143.accepted Panels0143.integerPanels Panels0143.aligned
    Panels0143.weightRows Panels0143.weights_checked ⟨9, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0136, b0137, b0138, b0139, b0140, b0141, b0142, b0143]
theorem chain_checked : blockChainCheck (697204548152650608931256665441/10^30) (895201045119432327478050281094/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=528388573454944526650302904356362816131484905853723771476293613576974362704585151565121622134240365777072222716295917841666957251822515852887486127332073168896987305750733030717281444287978814473335565200820079272/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row09
namespace Row10
abbrev ζ : ℚ := 13793103448275862068965517241/10^30
def b0136 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0136.block Panels0136.accepted Panels0136.integerPanels Panels0136.aligned
    Panels0136.weightRows Panels0136.weights_checked ⟨10, by decide⟩
def b0137 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0137.block Panels0137.accepted Panels0137.integerPanels Panels0137.aligned
    Panels0137.weightRows Panels0137.weights_checked ⟨10, by decide⟩
def b0138 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0138.block Panels0138.accepted Panels0138.integerPanels Panels0138.aligned
    Panels0138.weightRows Panels0138.weights_checked ⟨10, by decide⟩
def b0139 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0139.block Panels0139.accepted Panels0139.integerPanels Panels0139.aligned
    Panels0139.weightRows Panels0139.weights_checked ⟨10, by decide⟩
def b0140 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0140.block Panels0140.accepted Panels0140.integerPanels Panels0140.aligned
    Panels0140.weightRows Panels0140.weights_checked ⟨10, by decide⟩
def b0141 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0141.block Panels0141.accepted Panels0141.integerPanels Panels0141.aligned
    Panels0141.weightRows Panels0141.weights_checked ⟨10, by decide⟩
def b0142 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0142.block Panels0142.accepted Panels0142.integerPanels Panels0142.aligned
    Panels0142.weightRows Panels0142.weights_checked ⟨10, by decide⟩
def b0143 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0143.block Panels0143.accepted Panels0143.integerPanels Panels0143.aligned
    Panels0143.weightRows Panels0143.weights_checked ⟨10, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0136, b0137, b0138, b0139, b0140, b0141, b0142, b0143]
theorem chain_checked : blockChainCheck (697204548152650608931256665441/10^30) (895201045119432327478050281094/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=545612336747201902088836988286424548729104283882522178308937093606246539764149539510064238939644527904556753985578475422101167095294179781076067735086757678415851342453084648295157783637919911653866411790636354600/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row10
namespace Row11
abbrev ζ : ℚ := 10152284263959390862944162436/10^30
def b0136 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0136.block Panels0136.accepted Panels0136.integerPanels Panels0136.aligned
    Panels0136.weightRows Panels0136.weights_checked ⟨11, by decide⟩
def b0137 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0137.block Panels0137.accepted Panels0137.integerPanels Panels0137.aligned
    Panels0137.weightRows Panels0137.weights_checked ⟨11, by decide⟩
def b0138 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0138.block Panels0138.accepted Panels0138.integerPanels Panels0138.aligned
    Panels0138.weightRows Panels0138.weights_checked ⟨11, by decide⟩
def b0139 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0139.block Panels0139.accepted Panels0139.integerPanels Panels0139.aligned
    Panels0139.weightRows Panels0139.weights_checked ⟨11, by decide⟩
def b0140 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0140.block Panels0140.accepted Panels0140.integerPanels Panels0140.aligned
    Panels0140.weightRows Panels0140.weights_checked ⟨11, by decide⟩
def b0141 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0141.block Panels0141.accepted Panels0141.integerPanels Panels0141.aligned
    Panels0141.weightRows Panels0141.weights_checked ⟨11, by decide⟩
def b0142 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0142.block Panels0142.accepted Panels0142.integerPanels Panels0142.aligned
    Panels0142.weightRows Panels0142.weights_checked ⟨11, by decide⟩
def b0143 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0143.block Panels0143.accepted Panels0143.integerPanels Panels0143.aligned
    Panels0143.weightRows Panels0143.weights_checked ⟨11, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0136, b0137, b0138, b0139, b0140, b0141, b0142, b0143]
theorem chain_checked : blockChainCheck (697204548152650608931256665441/10^30) (895201045119432327478050281094/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=558704131511408242068211500232212181412439231643910102375808129802261084928547405526648076146015224999773820815535804538221695969094978970819010430078338973191088680552072018188542451119993186751134514724032952520/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row11
namespace Row12
abbrev ζ : ℚ := 9950248756218905472636815920/10^30
def b0136 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0136.block Panels0136.accepted Panels0136.integerPanels Panels0136.aligned
    Panels0136.weightRows Panels0136.weights_checked ⟨12, by decide⟩
def b0137 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0137.block Panels0137.accepted Panels0137.integerPanels Panels0137.aligned
    Panels0137.weightRows Panels0137.weights_checked ⟨12, by decide⟩
def b0138 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0138.block Panels0138.accepted Panels0138.integerPanels Panels0138.aligned
    Panels0138.weightRows Panels0138.weights_checked ⟨12, by decide⟩
def b0139 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0139.block Panels0139.accepted Panels0139.integerPanels Panels0139.aligned
    Panels0139.weightRows Panels0139.weights_checked ⟨12, by decide⟩
def b0140 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0140.block Panels0140.accepted Panels0140.integerPanels Panels0140.aligned
    Panels0140.weightRows Panels0140.weights_checked ⟨12, by decide⟩
def b0141 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0141.block Panels0141.accepted Panels0141.integerPanels Panels0141.aligned
    Panels0141.weightRows Panels0141.weights_checked ⟨12, by decide⟩
def b0142 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0142.block Panels0142.accepted Panels0142.integerPanels Panels0142.aligned
    Panels0142.weightRows Panels0142.weights_checked ⟨12, by decide⟩
def b0143 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0143.block Panels0143.accepted Panels0143.integerPanels Panels0143.aligned
    Panels0143.weightRows Panels0143.weights_checked ⟨12, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0136, b0137, b0138, b0139, b0140, b0141, b0142, b0143]
theorem chain_checked : blockChainCheck (697204548152650608931256665441/10^30) (895201045119432327478050281094/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=559437948281628252497699221192565076547191548091493172440411257850799643490485828066833059615328254534136234961809349338477912758555146965303546231189309992323025618736432108135833540522960525470342642613687466568/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row12
#print axioms Row12.segment
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments017
