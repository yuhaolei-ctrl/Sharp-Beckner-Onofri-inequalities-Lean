module

public import BecknerOnofri.EntropyHeatCheckedWeights
public import BecknerOnofri.EntropyHeatSegments
public import BecknerOnofri.EntropyHeatCertificate.Panels0080
public import BecknerOnofri.EntropyHeatCertificate.Panels0081
public import BecknerOnofri.EntropyHeatCertificate.Panels0082
public import BecknerOnofri.EntropyHeatCertificate.Panels0083
public import BecknerOnofri.EntropyHeatCertificate.Panels0084
public import BecknerOnofri.EntropyHeatCertificate.Panels0085
public import BecknerOnofri.EntropyHeatCertificate.Panels0086
public import BecknerOnofri.EntropyHeatCertificate.Panels0087

@[expose] public section
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments010
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace Row00
abbrev ζ : ℚ := 285714285714285714285714285714/10^30
def b0080 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0080.block Panels0080.accepted Panels0080.integerPanels Panels0080.aligned
    Panels0080.weightRows Panels0080.weights_checked ⟨0, by decide⟩
def b0081 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0081.block Panels0081.accepted Panels0081.integerPanels Panels0081.aligned
    Panels0081.weightRows Panels0081.weights_checked ⟨0, by decide⟩
def b0082 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0082.block Panels0082.accepted Panels0082.integerPanels Panels0082.aligned
    Panels0082.weightRows Panels0082.weights_checked ⟨0, by decide⟩
def b0083 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0083.block Panels0083.accepted Panels0083.integerPanels Panels0083.aligned
    Panels0083.weightRows Panels0083.weights_checked ⟨0, by decide⟩
def b0084 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0084.block Panels0084.accepted Panels0084.integerPanels Panels0084.aligned
    Panels0084.weightRows Panels0084.weights_checked ⟨0, by decide⟩
def b0085 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0085.block Panels0085.accepted Panels0085.integerPanels Panels0085.aligned
    Panels0085.weightRows Panels0085.weights_checked ⟨0, by decide⟩
def b0086 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0086.block Panels0086.accepted Panels0086.integerPanels Panels0086.aligned
    Panels0086.weightRows Panels0086.weights_checked ⟨0, by decide⟩
def b0087 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0087.block Panels0087.accepted Panels0087.integerPanels Panels0087.aligned
    Panels0087.weightRows Panels0087.weights_checked ⟨0, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0080, b0081, b0082, b0083, b0084, b0085, b0086, b0087]
theorem chain_checked : blockChainCheck (121181863986477373198151782158/10^30) (155595845692136308077834748264/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row00
namespace Row01
abbrev ζ : ℚ := 222222222222222222222222222222/10^30
def b0080 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0080.block Panels0080.accepted Panels0080.integerPanels Panels0080.aligned
    Panels0080.weightRows Panels0080.weights_checked ⟨1, by decide⟩
def b0081 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0081.block Panels0081.accepted Panels0081.integerPanels Panels0081.aligned
    Panels0081.weightRows Panels0081.weights_checked ⟨1, by decide⟩
def b0082 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0082.block Panels0082.accepted Panels0082.integerPanels Panels0082.aligned
    Panels0082.weightRows Panels0082.weights_checked ⟨1, by decide⟩
def b0083 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0083.block Panels0083.accepted Panels0083.integerPanels Panels0083.aligned
    Panels0083.weightRows Panels0083.weights_checked ⟨1, by decide⟩
def b0084 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0084.block Panels0084.accepted Panels0084.integerPanels Panels0084.aligned
    Panels0084.weightRows Panels0084.weights_checked ⟨1, by decide⟩
def b0085 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0085.block Panels0085.accepted Panels0085.integerPanels Panels0085.aligned
    Panels0085.weightRows Panels0085.weights_checked ⟨1, by decide⟩
def b0086 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0086.block Panels0086.accepted Panels0086.integerPanels Panels0086.aligned
    Panels0086.weightRows Panels0086.weights_checked ⟨1, by decide⟩
def b0087 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0087.block Panels0087.accepted Panels0087.integerPanels Panels0087.aligned
    Panels0087.weightRows Panels0087.weights_checked ⟨1, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0080, b0081, b0082, b0083, b0084, b0085, b0086, b0087]
theorem chain_checked : blockChainCheck (121181863986477373198151782158/10^30) (155595845692136308077834748264/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row01
namespace Row02
abbrev ζ : ℚ := 153846153846153846153846153846/10^30
def b0080 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0080.block Panels0080.accepted Panels0080.integerPanels Panels0080.aligned
    Panels0080.weightRows Panels0080.weights_checked ⟨2, by decide⟩
def b0081 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0081.block Panels0081.accepted Panels0081.integerPanels Panels0081.aligned
    Panels0081.weightRows Panels0081.weights_checked ⟨2, by decide⟩
def b0082 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0082.block Panels0082.accepted Panels0082.integerPanels Panels0082.aligned
    Panels0082.weightRows Panels0082.weights_checked ⟨2, by decide⟩
def b0083 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0083.block Panels0083.accepted Panels0083.integerPanels Panels0083.aligned
    Panels0083.weightRows Panels0083.weights_checked ⟨2, by decide⟩
def b0084 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0084.block Panels0084.accepted Panels0084.integerPanels Panels0084.aligned
    Panels0084.weightRows Panels0084.weights_checked ⟨2, by decide⟩
def b0085 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0085.block Panels0085.accepted Panels0085.integerPanels Panels0085.aligned
    Panels0085.weightRows Panels0085.weights_checked ⟨2, by decide⟩
def b0086 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0086.block Panels0086.accepted Panels0086.integerPanels Panels0086.aligned
    Panels0086.weightRows Panels0086.weights_checked ⟨2, by decide⟩
def b0087 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0087.block Panels0087.accepted Panels0087.integerPanels Panels0087.aligned
    Panels0087.weightRows Panels0087.weights_checked ⟨2, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0080, b0081, b0082, b0083, b0084, b0085, b0086, b0087]
theorem chain_checked : blockChainCheck (121181863986477373198151782158/10^30) (155595845692136308077834748264/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=1959774916270051200988268933103014441187176973097127003957136110569615888249694462221641470255954905508751527192305255704677312613029938587002478394077315653106941176564824214951606577735906849226111252/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row02
namespace Row03
abbrev ζ : ℚ := 117647058823529411764705882352/10^30
def b0080 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0080.block Panels0080.accepted Panels0080.integerPanels Panels0080.aligned
    Panels0080.weightRows Panels0080.weights_checked ⟨3, by decide⟩
def b0081 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0081.block Panels0081.accepted Panels0081.integerPanels Panels0081.aligned
    Panels0081.weightRows Panels0081.weights_checked ⟨3, by decide⟩
def b0082 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0082.block Panels0082.accepted Panels0082.integerPanels Panels0082.aligned
    Panels0082.weightRows Panels0082.weights_checked ⟨3, by decide⟩
def b0083 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0083.block Panels0083.accepted Panels0083.integerPanels Panels0083.aligned
    Panels0083.weightRows Panels0083.weights_checked ⟨3, by decide⟩
def b0084 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0084.block Panels0084.accepted Panels0084.integerPanels Panels0084.aligned
    Panels0084.weightRows Panels0084.weights_checked ⟨3, by decide⟩
def b0085 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0085.block Panels0085.accepted Panels0085.integerPanels Panels0085.aligned
    Panels0085.weightRows Panels0085.weights_checked ⟨3, by decide⟩
def b0086 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0086.block Panels0086.accepted Panels0086.integerPanels Panels0086.aligned
    Panels0086.weightRows Panels0086.weights_checked ⟨3, by decide⟩
def b0087 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0087.block Panels0087.accepted Panels0087.integerPanels Panels0087.aligned
    Panels0087.weightRows Panels0087.weights_checked ⟨3, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0080, b0081, b0082, b0083, b0084, b0085, b0086, b0087]
theorem chain_checked : blockChainCheck (121181863986477373198151782158/10^30) (155595845692136308077834748264/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=255880349548952301443196683826925037438081324029619235904857988944976894155648016418547631559882583186003814556933511037612599487453080876679505418084966695252409421142820107168721173895456726180006303903711482/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row03
namespace Row04
abbrev ζ : ℚ := 86956521739130434782608695652/10^30
def b0080 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0080.block Panels0080.accepted Panels0080.integerPanels Panels0080.aligned
    Panels0080.weightRows Panels0080.weights_checked ⟨4, by decide⟩
def b0081 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0081.block Panels0081.accepted Panels0081.integerPanels Panels0081.aligned
    Panels0081.weightRows Panels0081.weights_checked ⟨4, by decide⟩
def b0082 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0082.block Panels0082.accepted Panels0082.integerPanels Panels0082.aligned
    Panels0082.weightRows Panels0082.weights_checked ⟨4, by decide⟩
def b0083 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0083.block Panels0083.accepted Panels0083.integerPanels Panels0083.aligned
    Panels0083.weightRows Panels0083.weights_checked ⟨4, by decide⟩
def b0084 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0084.block Panels0084.accepted Panels0084.integerPanels Panels0084.aligned
    Panels0084.weightRows Panels0084.weights_checked ⟨4, by decide⟩
def b0085 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0085.block Panels0085.accepted Panels0085.integerPanels Panels0085.aligned
    Panels0085.weightRows Panels0085.weights_checked ⟨4, by decide⟩
def b0086 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0086.block Panels0086.accepted Panels0086.integerPanels Panels0086.aligned
    Panels0086.weightRows Panels0086.weights_checked ⟨4, by decide⟩
def b0087 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0087.block Panels0087.accepted Panels0087.integerPanels Panels0087.aligned
    Panels0087.weightRows Panels0087.weights_checked ⟨4, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0080, b0081, b0082, b0083, b0084, b0085, b0086, b0087]
theorem chain_checked : blockChainCheck (121181863986477373198151782158/10^30) (155595845692136308077834748264/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=10818818756465663458340711983972294580144419480134969433296284957810595752971399054236553341437608536881769213758994028056528566916054415183336442712981674163491415903236498220453604427207367772497596530732435082/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row04
namespace Row05
abbrev ζ : ℚ := 64516129032258064516129032258/10^30
def b0080 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0080.block Panels0080.accepted Panels0080.integerPanels Panels0080.aligned
    Panels0080.weightRows Panels0080.weights_checked ⟨5, by decide⟩
def b0081 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0081.block Panels0081.accepted Panels0081.integerPanels Panels0081.aligned
    Panels0081.weightRows Panels0081.weights_checked ⟨5, by decide⟩
def b0082 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0082.block Panels0082.accepted Panels0082.integerPanels Panels0082.aligned
    Panels0082.weightRows Panels0082.weights_checked ⟨5, by decide⟩
def b0083 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0083.block Panels0083.accepted Panels0083.integerPanels Panels0083.aligned
    Panels0083.weightRows Panels0083.weights_checked ⟨5, by decide⟩
def b0084 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0084.block Panels0084.accepted Panels0084.integerPanels Panels0084.aligned
    Panels0084.weightRows Panels0084.weights_checked ⟨5, by decide⟩
def b0085 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0085.block Panels0085.accepted Panels0085.integerPanels Panels0085.aligned
    Panels0085.weightRows Panels0085.weights_checked ⟨5, by decide⟩
def b0086 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0086.block Panels0086.accepted Panels0086.integerPanels Panels0086.aligned
    Panels0086.weightRows Panels0086.weights_checked ⟨5, by decide⟩
def b0087 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0087.block Panels0087.accepted Panels0087.integerPanels Panels0087.aligned
    Panels0087.weightRows Panels0087.weights_checked ⟨5, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0080, b0081, b0082, b0083, b0084, b0085, b0086, b0087]
theorem chain_checked : blockChainCheck (121181863986477373198151782158/10^30) (155595845692136308077834748264/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=62107761132199882883993977054784076550566892207767036145862932496246249433840729522236368867388036396187450728380494060761205372260538610573816758958670439266945337995220261509177662917893466473664111287889541226/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row05
namespace Row06
abbrev ζ : ℚ := 46511627906976744186046511627/10^30
def b0080 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0080.block Panels0080.accepted Panels0080.integerPanels Panels0080.aligned
    Panels0080.weightRows Panels0080.weights_checked ⟨6, by decide⟩
def b0081 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0081.block Panels0081.accepted Panels0081.integerPanels Panels0081.aligned
    Panels0081.weightRows Panels0081.weights_checked ⟨6, by decide⟩
def b0082 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0082.block Panels0082.accepted Panels0082.integerPanels Panels0082.aligned
    Panels0082.weightRows Panels0082.weights_checked ⟨6, by decide⟩
def b0083 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0083.block Panels0083.accepted Panels0083.integerPanels Panels0083.aligned
    Panels0083.weightRows Panels0083.weights_checked ⟨6, by decide⟩
def b0084 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0084.block Panels0084.accepted Panels0084.integerPanels Panels0084.aligned
    Panels0084.weightRows Panels0084.weights_checked ⟨6, by decide⟩
def b0085 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0085.block Panels0085.accepted Panels0085.integerPanels Panels0085.aligned
    Panels0085.weightRows Panels0085.weights_checked ⟨6, by decide⟩
def b0086 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0086.block Panels0086.accepted Panels0086.integerPanels Panels0086.aligned
    Panels0086.weightRows Panels0086.weights_checked ⟨6, by decide⟩
def b0087 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0087.block Panels0087.accepted Panels0087.integerPanels Panels0087.aligned
    Panels0087.weightRows Panels0087.weights_checked ⟨6, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0080, b0081, b0082, b0083, b0084, b0085, b0086, b0087]
theorem chain_checked : blockChainCheck (121181863986477373198151782158/10^30) (155595845692136308077834748264/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=183474090823080447935048616863901865535346213961898277960077746499682158863171450874484072853102228066064971832650146219939706731146993054894523834559893297823641488089588939529399634565614666292056479278754529782/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row06
namespace Row07
abbrev ζ : ℚ := 33898305084745762711864406779/10^30
def b0080 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0080.block Panels0080.accepted Panels0080.integerPanels Panels0080.aligned
    Panels0080.weightRows Panels0080.weights_checked ⟨7, by decide⟩
def b0081 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0081.block Panels0081.accepted Panels0081.integerPanels Panels0081.aligned
    Panels0081.weightRows Panels0081.weights_checked ⟨7, by decide⟩
def b0082 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0082.block Panels0082.accepted Panels0082.integerPanels Panels0082.aligned
    Panels0082.weightRows Panels0082.weights_checked ⟨7, by decide⟩
def b0083 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0083.block Panels0083.accepted Panels0083.integerPanels Panels0083.aligned
    Panels0083.weightRows Panels0083.weights_checked ⟨7, by decide⟩
def b0084 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0084.block Panels0084.accepted Panels0084.integerPanels Panels0084.aligned
    Panels0084.weightRows Panels0084.weights_checked ⟨7, by decide⟩
def b0085 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0085.block Panels0085.accepted Panels0085.integerPanels Panels0085.aligned
    Panels0085.weightRows Panels0085.weights_checked ⟨7, by decide⟩
def b0086 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0086.block Panels0086.accepted Panels0086.integerPanels Panels0086.aligned
    Panels0086.weightRows Panels0086.weights_checked ⟨7, by decide⟩
def b0087 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0087.block Panels0087.accepted Panels0087.integerPanels Panels0087.aligned
    Panels0087.weightRows Panels0087.weights_checked ⟨7, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0080, b0081, b0082, b0083, b0084, b0085, b0086, b0087]
theorem chain_checked : blockChainCheck (121181863986477373198151782158/10^30) (155595845692136308077834748264/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=349613419605784804104504518235179044609433046892555641517874861517659565707932140603323199035246470910058129767555703648678816206530494750201149293075176500963556108934264091981949925275863256753561749197378922870/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row07
namespace Row08
abbrev ζ : ℚ := 25316455696202531645569620253/10^30
def b0080 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0080.block Panels0080.accepted Panels0080.integerPanels Panels0080.aligned
    Panels0080.weightRows Panels0080.weights_checked ⟨8, by decide⟩
def b0081 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0081.block Panels0081.accepted Panels0081.integerPanels Panels0081.aligned
    Panels0081.weightRows Panels0081.weights_checked ⟨8, by decide⟩
def b0082 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0082.block Panels0082.accepted Panels0082.integerPanels Panels0082.aligned
    Panels0082.weightRows Panels0082.weights_checked ⟨8, by decide⟩
def b0083 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0083.block Panels0083.accepted Panels0083.integerPanels Panels0083.aligned
    Panels0083.weightRows Panels0083.weights_checked ⟨8, by decide⟩
def b0084 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0084.block Panels0084.accepted Panels0084.integerPanels Panels0084.aligned
    Panels0084.weightRows Panels0084.weights_checked ⟨8, by decide⟩
def b0085 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0085.block Panels0085.accepted Panels0085.integerPanels Panels0085.aligned
    Panels0085.weightRows Panels0085.weights_checked ⟨8, by decide⟩
def b0086 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0086.block Panels0086.accepted Panels0086.integerPanels Panels0086.aligned
    Panels0086.weightRows Panels0086.weights_checked ⟨8, by decide⟩
def b0087 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0087.block Panels0087.accepted Panels0087.integerPanels Panels0087.aligned
    Panels0087.weightRows Panels0087.weights_checked ⟨8, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0080, b0081, b0082, b0083, b0084, b0085, b0086, b0087]
theorem chain_checked : blockChainCheck (121181863986477373198151782158/10^30) (155595845692136308077834748264/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=520002749592651823429705380818098110554696999889258251252714047663942592874376704462824658470392820261910366582649106233554188365982919640527598080688162062037509134105023499305180469048587193220956546319558399566/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row08
namespace Row09
abbrev ζ : ℚ := 18691588785046728971962616822/10^30
def b0080 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0080.block Panels0080.accepted Panels0080.integerPanels Panels0080.aligned
    Panels0080.weightRows Panels0080.weights_checked ⟨9, by decide⟩
def b0081 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0081.block Panels0081.accepted Panels0081.integerPanels Panels0081.aligned
    Panels0081.weightRows Panels0081.weights_checked ⟨9, by decide⟩
def b0082 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0082.block Panels0082.accepted Panels0082.integerPanels Panels0082.aligned
    Panels0082.weightRows Panels0082.weights_checked ⟨9, by decide⟩
def b0083 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0083.block Panels0083.accepted Panels0083.integerPanels Panels0083.aligned
    Panels0083.weightRows Panels0083.weights_checked ⟨9, by decide⟩
def b0084 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0084.block Panels0084.accepted Panels0084.integerPanels Panels0084.aligned
    Panels0084.weightRows Panels0084.weights_checked ⟨9, by decide⟩
def b0085 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0085.block Panels0085.accepted Panels0085.integerPanels Panels0085.aligned
    Panels0085.weightRows Panels0085.weights_checked ⟨9, by decide⟩
def b0086 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0086.block Panels0086.accepted Panels0086.integerPanels Panels0086.aligned
    Panels0086.weightRows Panels0086.weights_checked ⟨9, by decide⟩
def b0087 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0087.block Panels0087.accepted Panels0087.integerPanels Panels0087.aligned
    Panels0087.weightRows Panels0087.weights_checked ⟨9, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0080, b0081, b0082, b0083, b0084, b0085, b0086, b0087]
theorem chain_checked : blockChainCheck (121181863986477373198151782158/10^30) (155595845692136308077834748264/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=692776492041832346695165269807591612356349978040437476782499603572996163532863514580371893912030828286139358007130151823933834189184238475741468166445867967110345622767406128605631120456385455084133889188545733722/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row09
namespace Row10
abbrev ζ : ℚ := 13793103448275862068965517241/10^30
def b0080 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0080.block Panels0080.accepted Panels0080.integerPanels Panels0080.aligned
    Panels0080.weightRows Panels0080.weights_checked ⟨10, by decide⟩
def b0081 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0081.block Panels0081.accepted Panels0081.integerPanels Panels0081.aligned
    Panels0081.weightRows Panels0081.weights_checked ⟨10, by decide⟩
def b0082 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0082.block Panels0082.accepted Panels0082.integerPanels Panels0082.aligned
    Panels0082.weightRows Panels0082.weights_checked ⟨10, by decide⟩
def b0083 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0083.block Panels0083.accepted Panels0083.integerPanels Panels0083.aligned
    Panels0083.weightRows Panels0083.weights_checked ⟨10, by decide⟩
def b0084 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0084.block Panels0084.accepted Panels0084.integerPanels Panels0084.aligned
    Panels0084.weightRows Panels0084.weights_checked ⟨10, by decide⟩
def b0085 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0085.block Panels0085.accepted Panels0085.integerPanels Panels0085.aligned
    Panels0085.weightRows Panels0085.weights_checked ⟨10, by decide⟩
def b0086 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0086.block Panels0086.accepted Panels0086.integerPanels Panels0086.aligned
    Panels0086.weightRows Panels0086.weights_checked ⟨10, by decide⟩
def b0087 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0087.block Panels0087.accepted Panels0087.integerPanels Panels0087.aligned
    Panels0087.weightRows Panels0087.weights_checked ⟨10, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0080, b0081, b0082, b0083, b0084, b0085, b0086, b0087]
theorem chain_checked : blockChainCheck (121181863986477373198151782158/10^30) (155595845692136308077834748264/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=848093428528500871121713749536499517070626599834503754600199067484572633669795239342724444867355581430686319267875833348869133048027038558681898540424716495936361395246585907285471552614193790724254494224352294318/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row10
namespace Row11
abbrev ζ : ℚ := 10152284263959390862944162436/10^30
def b0080 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0080.block Panels0080.accepted Panels0080.integerPanels Panels0080.aligned
    Panels0080.weightRows Panels0080.weights_checked ⟨11, by decide⟩
def b0081 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0081.block Panels0081.accepted Panels0081.integerPanels Panels0081.aligned
    Panels0081.weightRows Panels0081.weights_checked ⟨11, by decide⟩
def b0082 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0082.block Panels0082.accepted Panels0082.integerPanels Panels0082.aligned
    Panels0082.weightRows Panels0082.weights_checked ⟨11, by decide⟩
def b0083 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0083.block Panels0083.accepted Panels0083.integerPanels Panels0083.aligned
    Panels0083.weightRows Panels0083.weights_checked ⟨11, by decide⟩
def b0084 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0084.block Panels0084.accepted Panels0084.integerPanels Panels0084.aligned
    Panels0084.weightRows Panels0084.weights_checked ⟨11, by decide⟩
def b0085 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0085.block Panels0085.accepted Panels0085.integerPanels Panels0085.aligned
    Panels0085.weightRows Panels0085.weights_checked ⟨11, by decide⟩
def b0086 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0086.block Panels0086.accepted Panels0086.integerPanels Panels0086.aligned
    Panels0086.weightRows Panels0086.weights_checked ⟨11, by decide⟩
def b0087 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0087.block Panels0087.accepted Panels0087.integerPanels Panels0087.aligned
    Panels0087.weightRows Panels0087.weights_checked ⟨11, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0080, b0081, b0082, b0083, b0084, b0085, b0086, b0087]
theorem chain_checked : blockChainCheck (121181863986477373198151782158/10^30) (155595845692136308077834748264/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=980769751797112314953267233926708612783379089191233112158064354836867396293228349351602092277868831088008033644934663304285635546769243604779253198898962659597436390639815622175180085912846802381039839525091586058/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row11
namespace Row12
abbrev ζ : ℚ := 9950248756218905472636815920/10^30
def b0080 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0080.block Panels0080.accepted Panels0080.integerPanels Panels0080.aligned
    Panels0080.weightRows Panels0080.weights_checked ⟨12, by decide⟩
def b0081 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0081.block Panels0081.accepted Panels0081.integerPanels Panels0081.aligned
    Panels0081.weightRows Panels0081.weights_checked ⟨12, by decide⟩
def b0082 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0082.block Panels0082.accepted Panels0082.integerPanels Panels0082.aligned
    Panels0082.weightRows Panels0082.weights_checked ⟨12, by decide⟩
def b0083 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0083.block Panels0083.accepted Panels0083.integerPanels Panels0083.aligned
    Panels0083.weightRows Panels0083.weights_checked ⟨12, by decide⟩
def b0084 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0084.block Panels0084.accepted Panels0084.integerPanels Panels0084.aligned
    Panels0084.weightRows Panels0084.weights_checked ⟨12, by decide⟩
def b0085 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0085.block Panels0085.accepted Panels0085.integerPanels Panels0085.aligned
    Panels0085.weightRows Panels0085.weights_checked ⟨12, by decide⟩
def b0086 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0086.block Panels0086.accepted Panels0086.integerPanels Panels0086.aligned
    Panels0086.weightRows Panels0086.weights_checked ⟨12, by decide⟩
def b0087 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0087.block Panels0087.accepted Panels0087.integerPanels Panels0087.aligned
    Panels0087.weightRows Panels0087.weights_checked ⟨12, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0080, b0081, b0082, b0083, b0084, b0085, b0086, b0087]
theorem chain_checked : blockChainCheck (121181863986477373198151782158/10^30) (155595845692136308077834748264/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=988594133069830322843999899704712780073664742301838696537338754322692110968577909645681012339767627109030760562545804662880527909263371807800539196071072157725406004948559645407637788652467035312926266590128286714/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row12
#print axioms Row12.segment
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments010
