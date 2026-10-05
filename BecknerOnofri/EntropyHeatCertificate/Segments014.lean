import BecknerOnofri.EntropyHeatCheckedWeights
import BecknerOnofri.EntropyHeatSegments
import BecknerOnofri.EntropyHeatCertificate.Panels0112
import BecknerOnofri.EntropyHeatCertificate.Panels0113
import BecknerOnofri.EntropyHeatCertificate.Panels0114
import BecknerOnofri.EntropyHeatCertificate.Panels0115
import BecknerOnofri.EntropyHeatCertificate.Panels0116
import BecknerOnofri.EntropyHeatCertificate.Panels0117
import BecknerOnofri.EntropyHeatCertificate.Panels0118
import BecknerOnofri.EntropyHeatCertificate.Panels0119
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments014
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace Row00
abbrev ζ : ℚ := 285714285714285714285714285714/10^30
def b0112 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0112.block Panels0112.accepted Panels0112.integerPanels Panels0112.aligned
    Panels0112.weightRows Panels0112.weights_checked ⟨0, by decide⟩
def b0113 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0113.block Panels0113.accepted Panels0113.integerPanels Panels0113.aligned
    Panels0113.weightRows Panels0113.weights_checked ⟨0, by decide⟩
def b0114 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0114.block Panels0114.accepted Panels0114.integerPanels Panels0114.aligned
    Panels0114.weightRows Panels0114.weights_checked ⟨0, by decide⟩
def b0115 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0115.block Panels0115.accepted Panels0115.integerPanels Panels0115.aligned
    Panels0115.weightRows Panels0115.weights_checked ⟨0, by decide⟩
def b0116 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0116.block Panels0116.accepted Panels0116.integerPanels Panels0116.aligned
    Panels0116.weightRows Panels0116.weights_checked ⟨0, by decide⟩
def b0117 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0117.block Panels0117.accepted Panels0117.integerPanels Panels0117.aligned
    Panels0117.weightRows Panels0117.weights_checked ⟨0, by decide⟩
def b0118 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0118.block Panels0118.accepted Panels0118.integerPanels Panels0118.aligned
    Panels0118.weightRows Panels0118.weights_checked ⟨0, by decide⟩
def b0119 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0119.block Panels0119.accepted Panels0119.integerPanels Panels0119.aligned
    Panels0119.weightRows Panels0119.weights_checked ⟨0, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0112, b0113, b0114, b0115, b0116, b0117, b0118, b0119]
theorem chain_checked : blockChainCheck (329366257060761223357774101419/10^30) (422901741431716601440210218652/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=1374291432808079728976492234515858383752434520335796566612054576002841889230274523914935838874771792585544281908020311921713101217128509318962302351838002704593860742710889351080646564110040215077275904058471367/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row00
namespace Row01
abbrev ζ : ℚ := 222222222222222222222222222222/10^30
def b0112 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0112.block Panels0112.accepted Panels0112.integerPanels Panels0112.aligned
    Panels0112.weightRows Panels0112.weights_checked ⟨1, by decide⟩
def b0113 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0113.block Panels0113.accepted Panels0113.integerPanels Panels0113.aligned
    Panels0113.weightRows Panels0113.weights_checked ⟨1, by decide⟩
def b0114 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0114.block Panels0114.accepted Panels0114.integerPanels Panels0114.aligned
    Panels0114.weightRows Panels0114.weights_checked ⟨1, by decide⟩
def b0115 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0115.block Panels0115.accepted Panels0115.integerPanels Panels0115.aligned
    Panels0115.weightRows Panels0115.weights_checked ⟨1, by decide⟩
def b0116 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0116.block Panels0116.accepted Panels0116.integerPanels Panels0116.aligned
    Panels0116.weightRows Panels0116.weights_checked ⟨1, by decide⟩
def b0117 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0117.block Panels0117.accepted Panels0117.integerPanels Panels0117.aligned
    Panels0117.weightRows Panels0117.weights_checked ⟨1, by decide⟩
def b0118 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0118.block Panels0118.accepted Panels0118.integerPanels Panels0118.aligned
    Panels0118.weightRows Panels0118.weights_checked ⟨1, by decide⟩
def b0119 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0119.block Panels0119.accepted Panels0119.integerPanels Panels0119.aligned
    Panels0119.weightRows Panels0119.weights_checked ⟨1, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0112, b0113, b0114, b0115, b0116, b0117, b0118, b0119]
theorem chain_checked : blockChainCheck (329366257060761223357774101419/10^30) (422901741431716601440210218652/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=15300871630666389887610646033974771577579683526176588148833214977742303508466227879664967423758238384735574325236715094238767410016886766768420235424805011098429002609088170304275082281189231200276214959753274191/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row01
namespace Row02
abbrev ζ : ℚ := 153846153846153846153846153846/10^30
def b0112 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0112.block Panels0112.accepted Panels0112.integerPanels Panels0112.aligned
    Panels0112.weightRows Panels0112.weights_checked ⟨2, by decide⟩
def b0113 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0113.block Panels0113.accepted Panels0113.integerPanels Panels0113.aligned
    Panels0113.weightRows Panels0113.weights_checked ⟨2, by decide⟩
def b0114 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0114.block Panels0114.accepted Panels0114.integerPanels Panels0114.aligned
    Panels0114.weightRows Panels0114.weights_checked ⟨2, by decide⟩
def b0115 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0115.block Panels0115.accepted Panels0115.integerPanels Panels0115.aligned
    Panels0115.weightRows Panels0115.weights_checked ⟨2, by decide⟩
def b0116 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0116.block Panels0116.accepted Panels0116.integerPanels Panels0116.aligned
    Panels0116.weightRows Panels0116.weights_checked ⟨2, by decide⟩
def b0117 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0117.block Panels0117.accepted Panels0117.integerPanels Panels0117.aligned
    Panels0117.weightRows Panels0117.weights_checked ⟨2, by decide⟩
def b0118 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0118.block Panels0118.accepted Panels0118.integerPanels Panels0118.aligned
    Panels0118.weightRows Panels0118.weights_checked ⟨2, by decide⟩
def b0119 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0119.block Panels0119.accepted Panels0119.integerPanels Panels0119.aligned
    Panels0119.weightRows Panels0119.weights_checked ⟨2, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0112, b0113, b0114, b0115, b0116, b0117, b0118, b0119]
theorem chain_checked : blockChainCheck (329366257060761223357774101419/10^30) (422901741431716601440210218652/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=92678711808903172415943502113223647153689170369256171731469789098591098880521029471884969996864110100710696057345476776635573133626162667902040008621486300101251814525754141144898706911454205169861401956847258143/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row02
namespace Row03
abbrev ζ : ℚ := 117647058823529411764705882352/10^30
def b0112 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0112.block Panels0112.accepted Panels0112.integerPanels Panels0112.aligned
    Panels0112.weightRows Panels0112.weights_checked ⟨3, by decide⟩
def b0113 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0113.block Panels0113.accepted Panels0113.integerPanels Panels0113.aligned
    Panels0113.weightRows Panels0113.weights_checked ⟨3, by decide⟩
def b0114 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0114.block Panels0114.accepted Panels0114.integerPanels Panels0114.aligned
    Panels0114.weightRows Panels0114.weights_checked ⟨3, by decide⟩
def b0115 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0115.block Panels0115.accepted Panels0115.integerPanels Panels0115.aligned
    Panels0115.weightRows Panels0115.weights_checked ⟨3, by decide⟩
def b0116 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0116.block Panels0116.accepted Panels0116.integerPanels Panels0116.aligned
    Panels0116.weightRows Panels0116.weights_checked ⟨3, by decide⟩
def b0117 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0117.block Panels0117.accepted Panels0117.integerPanels Panels0117.aligned
    Panels0117.weightRows Panels0117.weights_checked ⟨3, by decide⟩
def b0118 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0118.block Panels0118.accepted Panels0118.integerPanels Panels0118.aligned
    Panels0118.weightRows Panels0118.weights_checked ⟨3, by decide⟩
def b0119 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0119.block Panels0119.accepted Panels0119.integerPanels Panels0119.aligned
    Panels0119.weightRows Panels0119.weights_checked ⟨3, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0112, b0113, b0114, b0115, b0116, b0117, b0118, b0119]
theorem chain_checked : blockChainCheck (329366257060761223357774101419/10^30) (422901741431716601440210218652/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=197090907327838284828635713534682618030261385720028173743519798646775088853692741954564300240701553782373151716460291588833635936744567324303149966219430230517778600952790177846736275762222230038116011452116885911/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row03
namespace Row04
abbrev ζ : ℚ := 86956521739130434782608695652/10^30
def b0112 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0112.block Panels0112.accepted Panels0112.integerPanels Panels0112.aligned
    Panels0112.weightRows Panels0112.weights_checked ⟨4, by decide⟩
def b0113 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0113.block Panels0113.accepted Panels0113.integerPanels Panels0113.aligned
    Panels0113.weightRows Panels0113.weights_checked ⟨4, by decide⟩
def b0114 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0114.block Panels0114.accepted Panels0114.integerPanels Panels0114.aligned
    Panels0114.weightRows Panels0114.weights_checked ⟨4, by decide⟩
def b0115 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0115.block Panels0115.accepted Panels0115.integerPanels Panels0115.aligned
    Panels0115.weightRows Panels0115.weights_checked ⟨4, by decide⟩
def b0116 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0116.block Panels0116.accepted Panels0116.integerPanels Panels0116.aligned
    Panels0116.weightRows Panels0116.weights_checked ⟨4, by decide⟩
def b0117 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0117.block Panels0117.accepted Panels0117.integerPanels Panels0117.aligned
    Panels0117.weightRows Panels0117.weights_checked ⟨4, by decide⟩
def b0118 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0118.block Panels0118.accepted Panels0118.integerPanels Panels0118.aligned
    Panels0118.weightRows Panels0118.weights_checked ⟨4, by decide⟩
def b0119 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0119.block Panels0119.accepted Panels0119.integerPanels Panels0119.aligned
    Panels0119.weightRows Panels0119.weights_checked ⟨4, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0112, b0113, b0114, b0115, b0116, b0117, b0118, b0119]
theorem chain_checked : blockChainCheck (329366257060761223357774101419/10^30) (422901741431716601440210218652/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=346515898735074659215688257437205800063977881897024677151871102858982970543874417910947837573749022553388274686326108005218246627991656306154645821356519500529656407841843760305252046226216727678409476013877866111/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row04
namespace Row05
abbrev ζ : ℚ := 64516129032258064516129032258/10^30
def b0112 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0112.block Panels0112.accepted Panels0112.integerPanels Panels0112.aligned
    Panels0112.weightRows Panels0112.weights_checked ⟨5, by decide⟩
def b0113 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0113.block Panels0113.accepted Panels0113.integerPanels Panels0113.aligned
    Panels0113.weightRows Panels0113.weights_checked ⟨5, by decide⟩
def b0114 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0114.block Panels0114.accepted Panels0114.integerPanels Panels0114.aligned
    Panels0114.weightRows Panels0114.weights_checked ⟨5, by decide⟩
def b0115 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0115.block Panels0115.accepted Panels0115.integerPanels Panels0115.aligned
    Panels0115.weightRows Panels0115.weights_checked ⟨5, by decide⟩
def b0116 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0116.block Panels0116.accepted Panels0116.integerPanels Panels0116.aligned
    Panels0116.weightRows Panels0116.weights_checked ⟨5, by decide⟩
def b0117 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0117.block Panels0117.accepted Panels0117.integerPanels Panels0117.aligned
    Panels0117.weightRows Panels0117.weights_checked ⟨5, by decide⟩
def b0118 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0118.block Panels0118.accepted Panels0118.integerPanels Panels0118.aligned
    Panels0118.weightRows Panels0118.weights_checked ⟨5, by decide⟩
def b0119 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0119.block Panels0119.accepted Panels0119.integerPanels Panels0119.aligned
    Panels0119.weightRows Panels0119.weights_checked ⟨5, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0112, b0113, b0114, b0115, b0116, b0117, b0118, b0119]
theorem chain_checked : blockChainCheck (329366257060761223357774101419/10^30) (422901741431716601440210218652/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=505141426356986980040876406123515329131676097145266849944689991828176587002091611343649456154089783520362091628312627405704789226981613165656148270750599531502266437126183881803880909277159757077481419732335488039/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row05
namespace Row06
abbrev ζ : ℚ := 46511627906976744186046511627/10^30
def b0112 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0112.block Panels0112.accepted Panels0112.integerPanels Panels0112.aligned
    Panels0112.weightRows Panels0112.weights_checked ⟨6, by decide⟩
def b0113 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0113.block Panels0113.accepted Panels0113.integerPanels Panels0113.aligned
    Panels0113.weightRows Panels0113.weights_checked ⟨6, by decide⟩
def b0114 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0114.block Panels0114.accepted Panels0114.integerPanels Panels0114.aligned
    Panels0114.weightRows Panels0114.weights_checked ⟨6, by decide⟩
def b0115 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0115.block Panels0115.accepted Panels0115.integerPanels Panels0115.aligned
    Panels0115.weightRows Panels0115.weights_checked ⟨6, by decide⟩
def b0116 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0116.block Panels0116.accepted Panels0116.integerPanels Panels0116.aligned
    Panels0116.weightRows Panels0116.weights_checked ⟨6, by decide⟩
def b0117 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0117.block Panels0117.accepted Panels0117.integerPanels Panels0117.aligned
    Panels0117.weightRows Panels0117.weights_checked ⟨6, by decide⟩
def b0118 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0118.block Panels0118.accepted Panels0118.integerPanels Panels0118.aligned
    Panels0118.weightRows Panels0118.weights_checked ⟨6, by decide⟩
def b0119 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0119.block Panels0119.accepted Panels0119.integerPanels Panels0119.aligned
    Panels0119.weightRows Panels0119.weights_checked ⟨6, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0112, b0113, b0114, b0115, b0116, b0117, b0118, b0119]
theorem chain_checked : blockChainCheck (329366257060761223357774101419/10^30) (422901741431716601440210218652/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=670830328053192477871050525811371426673119978542829465421580377899702649195050222503830394049736803694854116886135965168690726593672308613555337376410963777602037693386780315767586290785503531208729269494772102761/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row06
namespace Row07
abbrev ζ : ℚ := 33898305084745762711864406779/10^30
def b0112 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0112.block Panels0112.accepted Panels0112.integerPanels Panels0112.aligned
    Panels0112.weightRows Panels0112.weights_checked ⟨7, by decide⟩
def b0113 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0113.block Panels0113.accepted Panels0113.integerPanels Panels0113.aligned
    Panels0113.weightRows Panels0113.weights_checked ⟨7, by decide⟩
def b0114 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0114.block Panels0114.accepted Panels0114.integerPanels Panels0114.aligned
    Panels0114.weightRows Panels0114.weights_checked ⟨7, by decide⟩
def b0115 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0115.block Panels0115.accepted Panels0115.integerPanels Panels0115.aligned
    Panels0115.weightRows Panels0115.weights_checked ⟨7, by decide⟩
def b0116 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0116.block Panels0116.accepted Panels0116.integerPanels Panels0116.aligned
    Panels0116.weightRows Panels0116.weights_checked ⟨7, by decide⟩
def b0117 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0117.block Panels0117.accepted Panels0117.integerPanels Panels0117.aligned
    Panels0117.weightRows Panels0117.weights_checked ⟨7, by decide⟩
def b0118 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0118.block Panels0118.accepted Panels0118.integerPanels Panels0118.aligned
    Panels0118.weightRows Panels0118.weights_checked ⟨7, by decide⟩
def b0119 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0119.block Panels0119.accepted Panels0119.integerPanels Panels0119.aligned
    Panels0119.weightRows Panels0119.weights_checked ⟨7, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0112, b0113, b0114, b0115, b0116, b0117, b0118, b0119]
theorem chain_checked : blockChainCheck (329366257060761223357774101419/10^30) (422901741431716601440210218652/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=811042696280044469778300170597083309642313975222233747417498277771996131493954358757030461871685734422377338391871021073748134633134797462165705483136962427327660339619308218356457277825092868019943900662527045577/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row07
namespace Row08
abbrev ζ : ℚ := 25316455696202531645569620253/10^30
def b0112 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0112.block Panels0112.accepted Panels0112.integerPanels Panels0112.aligned
    Panels0112.weightRows Panels0112.weights_checked ⟨8, by decide⟩
def b0113 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0113.block Panels0113.accepted Panels0113.integerPanels Panels0113.aligned
    Panels0113.weightRows Panels0113.weights_checked ⟨8, by decide⟩
def b0114 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0114.block Panels0114.accepted Panels0114.integerPanels Panels0114.aligned
    Panels0114.weightRows Panels0114.weights_checked ⟨8, by decide⟩
def b0115 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0115.block Panels0115.accepted Panels0115.integerPanels Panels0115.aligned
    Panels0115.weightRows Panels0115.weights_checked ⟨8, by decide⟩
def b0116 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0116.block Panels0116.accepted Panels0116.integerPanels Panels0116.aligned
    Panels0116.weightRows Panels0116.weights_checked ⟨8, by decide⟩
def b0117 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0117.block Panels0117.accepted Panels0117.integerPanels Panels0117.aligned
    Panels0117.weightRows Panels0117.weights_checked ⟨8, by decide⟩
def b0118 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0118.block Panels0118.accepted Panels0118.integerPanels Panels0118.aligned
    Panels0118.weightRows Panels0118.weights_checked ⟨8, by decide⟩
def b0119 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0119.block Panels0119.accepted Panels0119.integerPanels Panels0119.aligned
    Panels0119.weightRows Panels0119.weights_checked ⟨8, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0112, b0113, b0114, b0115, b0116, b0117, b0118, b0119]
theorem chain_checked : blockChainCheck (329366257060761223357774101419/10^30) (422901741431716601440210218652/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=919250649511138832822301724971076880602568917530237288837110352177890130985865057760431726213919871006027873185523076021578044746401489453278553053225320196920613025004443602759573663276545661000185461542248592169/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row08
namespace Row09
abbrev ζ : ℚ := 18691588785046728971962616822/10^30
def b0112 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0112.block Panels0112.accepted Panels0112.integerPanels Panels0112.aligned
    Panels0112.weightRows Panels0112.weights_checked ⟨9, by decide⟩
def b0113 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0113.block Panels0113.accepted Panels0113.integerPanels Panels0113.aligned
    Panels0113.weightRows Panels0113.weights_checked ⟨9, by decide⟩
def b0114 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0114.block Panels0114.accepted Panels0114.integerPanels Panels0114.aligned
    Panels0114.weightRows Panels0114.weights_checked ⟨9, by decide⟩
def b0115 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0115.block Panels0115.accepted Panels0115.integerPanels Panels0115.aligned
    Panels0115.weightRows Panels0115.weights_checked ⟨9, by decide⟩
def b0116 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0116.block Panels0116.accepted Panels0116.integerPanels Panels0116.aligned
    Panels0116.weightRows Panels0116.weights_checked ⟨9, by decide⟩
def b0117 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0117.block Panels0117.accepted Panels0117.integerPanels Panels0117.aligned
    Panels0117.weightRows Panels0117.weights_checked ⟨9, by decide⟩
def b0118 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0118.block Panels0118.accepted Panels0118.integerPanels Panels0118.aligned
    Panels0118.weightRows Panels0118.weights_checked ⟨9, by decide⟩
def b0119 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0119.block Panels0119.accepted Panels0119.integerPanels Panels0119.aligned
    Panels0119.weightRows Panels0119.weights_checked ⟨9, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0112, b0113, b0114, b0115, b0116, b0117, b0118, b0119]
theorem chain_checked : blockChainCheck (329366257060761223357774101419/10^30) (422901741431716601440210218652/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=1010485759385066693744635358799933459801792620906732482753198122174679352613693831444380147482608271532422207451743751562371075588227121370302652868898149076712100088919759068515154448831751633017893687862777186591/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row09
namespace Row10
abbrev ζ : ℚ := 13793103448275862068965517241/10^30
def b0112 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0112.block Panels0112.accepted Panels0112.integerPanels Panels0112.aligned
    Panels0112.weightRows Panels0112.weights_checked ⟨10, by decide⟩
def b0113 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0113.block Panels0113.accepted Panels0113.integerPanels Panels0113.aligned
    Panels0113.weightRows Panels0113.weights_checked ⟨10, by decide⟩
def b0114 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0114.block Panels0114.accepted Panels0114.integerPanels Panels0114.aligned
    Panels0114.weightRows Panels0114.weights_checked ⟨10, by decide⟩
def b0115 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0115.block Panels0115.accepted Panels0115.integerPanels Panels0115.aligned
    Panels0115.weightRows Panels0115.weights_checked ⟨10, by decide⟩
def b0116 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0116.block Panels0116.accepted Panels0116.integerPanels Panels0116.aligned
    Panels0116.weightRows Panels0116.weights_checked ⟨10, by decide⟩
def b0117 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0117.block Panels0117.accepted Panels0117.integerPanels Panels0117.aligned
    Panels0117.weightRows Panels0117.weights_checked ⟨10, by decide⟩
def b0118 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0118.block Panels0118.accepted Panels0118.integerPanels Panels0118.aligned
    Panels0118.weightRows Panels0118.weights_checked ⟨10, by decide⟩
def b0119 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0119.block Panels0119.accepted Panels0119.integerPanels Panels0119.aligned
    Panels0119.weightRows Panels0119.weights_checked ⟨10, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0112, b0113, b0114, b0115, b0116, b0117, b0118, b0119]
theorem chain_checked : blockChainCheck (329366257060761223357774101419/10^30) (422901741431716601440210218652/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=1082519825047218935139157066720810461229855834694802233485200994831807627414073617886513122404640878492133632981147861884036415337820450223899277226492657442456026947580742278174223017998728107440676671038731102273/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row10
namespace Row11
abbrev ζ : ℚ := 10152284263959390862944162436/10^30
def b0112 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0112.block Panels0112.accepted Panels0112.integerPanels Panels0112.aligned
    Panels0112.weightRows Panels0112.weights_checked ⟨11, by decide⟩
def b0113 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0113.block Panels0113.accepted Panels0113.integerPanels Panels0113.aligned
    Panels0113.weightRows Panels0113.weights_checked ⟨11, by decide⟩
def b0114 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0114.block Panels0114.accepted Panels0114.integerPanels Panels0114.aligned
    Panels0114.weightRows Panels0114.weights_checked ⟨11, by decide⟩
def b0115 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0115.block Panels0115.accepted Panels0115.integerPanels Panels0115.aligned
    Panels0115.weightRows Panels0115.weights_checked ⟨11, by decide⟩
def b0116 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0116.block Panels0116.accepted Panels0116.integerPanels Panels0116.aligned
    Panels0116.weightRows Panels0116.weights_checked ⟨11, by decide⟩
def b0117 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0117.block Panels0117.accepted Panels0117.integerPanels Panels0117.aligned
    Panels0117.weightRows Panels0117.weights_checked ⟨11, by decide⟩
def b0118 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0118.block Panels0118.accepted Panels0118.integerPanels Panels0118.aligned
    Panels0118.weightRows Panels0118.weights_checked ⟨11, by decide⟩
def b0119 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0119.block Panels0119.accepted Panels0119.integerPanels Panels0119.aligned
    Panels0119.weightRows Panels0119.weights_checked ⟨11, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0112, b0113, b0114, b0115, b0116, b0117, b0118, b0119]
theorem chain_checked : blockChainCheck (329366257060761223357774101419/10^30) (422901741431716601440210218652/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=1138689718069304461421865396956765967477951046049581075975495078057701303167323197183478264771043019917731484666430699709963911524228235016017985965636229469532057288842677696540054641892983231159784911426813879103/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row11
namespace Row12
abbrev ζ : ℚ := 9950248756218905472636815920/10^30
def b0112 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0112.block Panels0112.accepted Panels0112.integerPanels Panels0112.aligned
    Panels0112.weightRows Panels0112.weights_checked ⟨12, by decide⟩
def b0113 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0113.block Panels0113.accepted Panels0113.integerPanels Panels0113.aligned
    Panels0113.weightRows Panels0113.weights_checked ⟨12, by decide⟩
def b0114 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0114.block Panels0114.accepted Panels0114.integerPanels Panels0114.aligned
    Panels0114.weightRows Panels0114.weights_checked ⟨12, by decide⟩
def b0115 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0115.block Panels0115.accepted Panels0115.integerPanels Panels0115.aligned
    Panels0115.weightRows Panels0115.weights_checked ⟨12, by decide⟩
def b0116 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0116.block Panels0116.accepted Panels0116.integerPanels Panels0116.aligned
    Panels0116.weightRows Panels0116.weights_checked ⟨12, by decide⟩
def b0117 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0117.block Panels0117.accepted Panels0117.integerPanels Panels0117.aligned
    Panels0117.weightRows Panels0117.weights_checked ⟨12, by decide⟩
def b0118 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0118.block Panels0118.accepted Panels0118.integerPanels Panels0118.aligned
    Panels0118.weightRows Panels0118.weights_checked ⟨12, by decide⟩
def b0119 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0119.block Panels0119.accepted Panels0119.integerPanels Panels0119.aligned
    Panels0119.weightRows Panels0119.weights_checked ⟨12, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0112, b0113, b0114, b0115, b0116, b0117, b0118, b0119]
theorem chain_checked : blockChainCheck (329366257060761223357774101419/10^30) (422901741431716601440210218652/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=1141874002335038989862954406998914602899195109389713644464383806546253209274093622879446272128245807882235309247894743483406933062234163469438158796954846813549265162361360923812834568534744316683368286095584733975/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row12
#print axioms Row12.segment
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments014
