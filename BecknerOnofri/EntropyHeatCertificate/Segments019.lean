import BecknerOnofri.EntropyHeatCheckedWeights
import BecknerOnofri.EntropyHeatSegments
import BecknerOnofri.EntropyHeatCertificate.Panels0152
import BecknerOnofri.EntropyHeatCertificate.Panels0153
import BecknerOnofri.EntropyHeatCertificate.Panels0154
import BecknerOnofri.EntropyHeatCertificate.Panels0155
import BecknerOnofri.EntropyHeatCertificate.Panels0156
import BecknerOnofri.EntropyHeatCertificate.Panels0157
import BecknerOnofri.EntropyHeatCertificate.Panels0158
import BecknerOnofri.EntropyHeatCertificate.Panels0159
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments019
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace Row00
abbrev ζ : ℚ := 285714285714285714285714285714/10^30
def b0152 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0152.block Panels0152.accepted Panels0152.integerPanels Panels0152.aligned
    Panels0152.weightRows Panels0152.weights_checked ⟨0, by decide⟩
def b0153 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0153.block Panels0153.accepted Panels0153.integerPanels Panels0153.aligned
    Panels0153.weightRows Panels0153.weights_checked ⟨0, by decide⟩
def b0154 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0154.block Panels0154.accepted Panels0154.integerPanels Panels0154.aligned
    Panels0154.weightRows Panels0154.weights_checked ⟨0, by decide⟩
def b0155 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0155.block Panels0155.accepted Panels0155.integerPanels Panels0155.aligned
    Panels0155.weightRows Panels0155.weights_checked ⟨0, by decide⟩
def b0156 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0156.block Panels0156.accepted Panels0156.integerPanels Panels0156.aligned
    Panels0156.weightRows Panels0156.weights_checked ⟨0, by decide⟩
def b0157 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0157.block Panels0157.accepted Panels0157.integerPanels Panels0157.aligned
    Panels0157.weightRows Panels0157.weights_checked ⟨0, by decide⟩
def b0158 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0158.block Panels0158.accepted Panels0158.integerPanels Panels0158.aligned
    Panels0158.weightRows Panels0158.weights_checked ⟨0, by decide⟩
def b0159 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0159.block Panels0159.accepted Panels0159.integerPanels Panels0159.aligned
    Panels0159.weightRows Panels0159.weights_checked ⟨0, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0152, b0153, b0154, b0155, b0156, b0157, b0158, b0159]
theorem chain_checked : blockChainCheck (1149425822459585220641394231371/10^30) (1475846938003328726491487854557/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=34619166083543042245461080023249606133300110043051216272301201791319924612195496916608216380649797740639601468379982822823167021661774298606537871902670127172664847986752307823185659194617964466632362011850540943/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row00
namespace Row01
abbrev ζ : ℚ := 222222222222222222222222222222/10^30
def b0152 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0152.block Panels0152.accepted Panels0152.integerPanels Panels0152.aligned
    Panels0152.weightRows Panels0152.weights_checked ⟨1, by decide⟩
def b0153 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0153.block Panels0153.accepted Panels0153.integerPanels Panels0153.aligned
    Panels0153.weightRows Panels0153.weights_checked ⟨1, by decide⟩
def b0154 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0154.block Panels0154.accepted Panels0154.integerPanels Panels0154.aligned
    Panels0154.weightRows Panels0154.weights_checked ⟨1, by decide⟩
def b0155 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0155.block Panels0155.accepted Panels0155.integerPanels Panels0155.aligned
    Panels0155.weightRows Panels0155.weights_checked ⟨1, by decide⟩
def b0156 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0156.block Panels0156.accepted Panels0156.integerPanels Panels0156.aligned
    Panels0156.weightRows Panels0156.weights_checked ⟨1, by decide⟩
def b0157 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0157.block Panels0157.accepted Panels0157.integerPanels Panels0157.aligned
    Panels0157.weightRows Panels0157.weights_checked ⟨1, by decide⟩
def b0158 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0158.block Panels0158.accepted Panels0158.integerPanels Panels0158.aligned
    Panels0158.weightRows Panels0158.weights_checked ⟨1, by decide⟩
def b0159 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0159.block Panels0159.accepted Panels0159.integerPanels Panels0159.aligned
    Panels0159.weightRows Panels0159.weights_checked ⟨1, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0152, b0153, b0154, b0155, b0156, b0157, b0158, b0159]
theorem chain_checked : blockChainCheck (1149425822459585220641394231371/10^30) (1475846938003328726491487854557/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=47226981848260418156154409266618252967785006759852319824909676373941962580715182314078413862264460972224055031152190351577057843124346213585360245672523584604579927176831000016459311727762400981794677864057252679/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row01
namespace Row02
abbrev ζ : ℚ := 153846153846153846153846153846/10^30
def b0152 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0152.block Panels0152.accepted Panels0152.integerPanels Panels0152.aligned
    Panels0152.weightRows Panels0152.weights_checked ⟨2, by decide⟩
def b0153 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0153.block Panels0153.accepted Panels0153.integerPanels Panels0153.aligned
    Panels0153.weightRows Panels0153.weights_checked ⟨2, by decide⟩
def b0154 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0154.block Panels0154.accepted Panels0154.integerPanels Panels0154.aligned
    Panels0154.weightRows Panels0154.weights_checked ⟨2, by decide⟩
def b0155 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0155.block Panels0155.accepted Panels0155.integerPanels Panels0155.aligned
    Panels0155.weightRows Panels0155.weights_checked ⟨2, by decide⟩
def b0156 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0156.block Panels0156.accepted Panels0156.integerPanels Panels0156.aligned
    Panels0156.weightRows Panels0156.weights_checked ⟨2, by decide⟩
def b0157 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0157.block Panels0157.accepted Panels0157.integerPanels Panels0157.aligned
    Panels0157.weightRows Panels0157.weights_checked ⟨2, by decide⟩
def b0158 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0158.block Panels0158.accepted Panels0158.integerPanels Panels0158.aligned
    Panels0158.weightRows Panels0158.weights_checked ⟨2, by decide⟩
def b0159 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0159.block Panels0159.accepted Panels0159.integerPanels Panels0159.aligned
    Panels0159.weightRows Panels0159.weights_checked ⟨2, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0152, b0153, b0154, b0155, b0156, b0157, b0158, b0159]
theorem chain_checked : blockChainCheck (1149425822459585220641394231371/10^30) (1475846938003328726491487854557/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=64695690165981431565681002779045341257372026313215223323930309066788807622623795865138238063652866540915416381568341523215920962441597961051318258285226270215748391415229615769505442515140571150946435867347039287/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row02
namespace Row03
abbrev ζ : ℚ := 117647058823529411764705882352/10^30
def b0152 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0152.block Panels0152.accepted Panels0152.integerPanels Panels0152.aligned
    Panels0152.weightRows Panels0152.weights_checked ⟨3, by decide⟩
def b0153 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0153.block Panels0153.accepted Panels0153.integerPanels Panels0153.aligned
    Panels0153.weightRows Panels0153.weights_checked ⟨3, by decide⟩
def b0154 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0154.block Panels0154.accepted Panels0154.integerPanels Panels0154.aligned
    Panels0154.weightRows Panels0154.weights_checked ⟨3, by decide⟩
def b0155 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0155.block Panels0155.accepted Panels0155.integerPanels Panels0155.aligned
    Panels0155.weightRows Panels0155.weights_checked ⟨3, by decide⟩
def b0156 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0156.block Panels0156.accepted Panels0156.integerPanels Panels0156.aligned
    Panels0156.weightRows Panels0156.weights_checked ⟨3, by decide⟩
def b0157 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0157.block Panels0157.accepted Panels0157.integerPanels Panels0157.aligned
    Panels0157.weightRows Panels0157.weights_checked ⟨3, by decide⟩
def b0158 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0158.block Panels0158.accepted Panels0158.integerPanels Panels0158.aligned
    Panels0158.weightRows Panels0158.weights_checked ⟨3, by decide⟩
def b0159 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0159.block Panels0159.accepted Panels0159.integerPanels Panels0159.aligned
    Panels0159.weightRows Panels0159.weights_checked ⟨3, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0152, b0153, b0154, b0155, b0156, b0157, b0158, b0159]
theorem chain_checked : blockChainCheck (1149425822459585220641394231371/10^30) (1475846938003328726491487854557/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=75854274014977640723223866638657288461410697140926335317428542798988355288678930475982843035724961938955440367866462906629213719024572125745673550476782153577498175287998231210064662728612656620740898423644175959/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row03
namespace Row04
abbrev ζ : ℚ := 86956521739130434782608695652/10^30
def b0152 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0152.block Panels0152.accepted Panels0152.integerPanels Panels0152.aligned
    Panels0152.weightRows Panels0152.weights_checked ⟨4, by decide⟩
def b0153 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0153.block Panels0153.accepted Panels0153.integerPanels Panels0153.aligned
    Panels0153.weightRows Panels0153.weights_checked ⟨4, by decide⟩
def b0154 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0154.block Panels0154.accepted Panels0154.integerPanels Panels0154.aligned
    Panels0154.weightRows Panels0154.weights_checked ⟨4, by decide⟩
def b0155 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0155.block Panels0155.accepted Panels0155.integerPanels Panels0155.aligned
    Panels0155.weightRows Panels0155.weights_checked ⟨4, by decide⟩
def b0156 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0156.block Panels0156.accepted Panels0156.integerPanels Panels0156.aligned
    Panels0156.weightRows Panels0156.weights_checked ⟨4, by decide⟩
def b0157 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0157.block Panels0157.accepted Panels0157.integerPanels Panels0157.aligned
    Panels0157.weightRows Panels0157.weights_checked ⟨4, by decide⟩
def b0158 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0158.block Panels0158.accepted Panels0158.integerPanels Panels0158.aligned
    Panels0158.weightRows Panels0158.weights_checked ⟨4, by decide⟩
def b0159 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0159.block Panels0159.accepted Panels0159.integerPanels Panels0159.aligned
    Panels0159.weightRows Panels0159.weights_checked ⟨4, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0152, b0153, b0154, b0155, b0156, b0157, b0158, b0159]
theorem chain_checked : blockChainCheck (1149425822459585220641394231371/10^30) (1475846938003328726491487854557/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=86483221843170193257613498142660054415769948837809107617211335884882812385326210998191944734217328770811326369517226135182612324765422541133590965503999158355146538112731296243743344300460955837984112655664375759/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row04
namespace Row05
abbrev ζ : ℚ := 64516129032258064516129032258/10^30
def b0152 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0152.block Panels0152.accepted Panels0152.integerPanels Panels0152.aligned
    Panels0152.weightRows Panels0152.weights_checked ⟨5, by decide⟩
def b0153 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0153.block Panels0153.accepted Panels0153.integerPanels Panels0153.aligned
    Panels0153.weightRows Panels0153.weights_checked ⟨5, by decide⟩
def b0154 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0154.block Panels0154.accepted Panels0154.integerPanels Panels0154.aligned
    Panels0154.weightRows Panels0154.weights_checked ⟨5, by decide⟩
def b0155 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0155.block Panels0155.accepted Panels0155.integerPanels Panels0155.aligned
    Panels0155.weightRows Panels0155.weights_checked ⟨5, by decide⟩
def b0156 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0156.block Panels0156.accepted Panels0156.integerPanels Panels0156.aligned
    Panels0156.weightRows Panels0156.weights_checked ⟨5, by decide⟩
def b0157 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0157.block Panels0157.accepted Panels0157.integerPanels Panels0157.aligned
    Panels0157.weightRows Panels0157.weights_checked ⟨5, by decide⟩
def b0158 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0158.block Panels0158.accepted Panels0158.integerPanels Panels0158.aligned
    Panels0158.weightRows Panels0158.weights_checked ⟨5, by decide⟩
def b0159 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0159.block Panels0159.accepted Panels0159.integerPanels Panels0159.aligned
    Panels0159.weightRows Panels0159.weights_checked ⟨5, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0152, b0153, b0154, b0155, b0156, b0157, b0158, b0159]
theorem chain_checked : blockChainCheck (1149425822459585220641394231371/10^30) (1475846938003328726491487854557/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=94987956646405016452912875512389238898930262393951828455976196709150840959080185471059686171440696793947470047611514184015246594441890431502727134429556552148186888023525990537255059237848015770416574354428078511/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row05
namespace Row06
abbrev ζ : ℚ := 46511627906976744186046511627/10^30
def b0152 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0152.block Panels0152.accepted Panels0152.integerPanels Panels0152.aligned
    Panels0152.weightRows Panels0152.weights_checked ⟨6, by decide⟩
def b0153 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0153.block Panels0153.accepted Panels0153.integerPanels Panels0153.aligned
    Panels0153.weightRows Panels0153.weights_checked ⟨6, by decide⟩
def b0154 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0154.block Panels0154.accepted Panels0154.integerPanels Panels0154.aligned
    Panels0154.weightRows Panels0154.weights_checked ⟨6, by decide⟩
def b0155 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0155.block Panels0155.accepted Panels0155.integerPanels Panels0155.aligned
    Panels0155.weightRows Panels0155.weights_checked ⟨6, by decide⟩
def b0156 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0156.block Panels0156.accepted Panels0156.integerPanels Panels0156.aligned
    Panels0156.weightRows Panels0156.weights_checked ⟨6, by decide⟩
def b0157 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0157.block Panels0157.accepted Panels0157.integerPanels Panels0157.aligned
    Panels0157.weightRows Panels0157.weights_checked ⟨6, by decide⟩
def b0158 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0158.block Panels0158.accepted Panels0158.integerPanels Panels0158.aligned
    Panels0158.weightRows Panels0158.weights_checked ⟨6, by decide⟩
def b0159 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0159.block Panels0159.accepted Panels0159.integerPanels Panels0159.aligned
    Panels0159.weightRows Panels0159.weights_checked ⟨6, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0152, b0153, b0154, b0155, b0156, b0157, b0158, b0159]
theorem chain_checked : blockChainCheck (1149425822459585220641394231371/10^30) (1475846938003328726491487854557/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=102286951735044857929758067127509501618821573794210605255994491370447048156915279473236735687634401773956842940315241682187237763894055618690105167714969797308637102347533117623085344862738674630589775363624486609/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row06
namespace Row07
abbrev ζ : ℚ := 33898305084745762711864406779/10^30
def b0152 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0152.block Panels0152.accepted Panels0152.integerPanels Panels0152.aligned
    Panels0152.weightRows Panels0152.weights_checked ⟨7, by decide⟩
def b0153 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0153.block Panels0153.accepted Panels0153.integerPanels Panels0153.aligned
    Panels0153.weightRows Panels0153.weights_checked ⟨7, by decide⟩
def b0154 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0154.block Panels0154.accepted Panels0154.integerPanels Panels0154.aligned
    Panels0154.weightRows Panels0154.weights_checked ⟨7, by decide⟩
def b0155 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0155.block Panels0155.accepted Panels0155.integerPanels Panels0155.aligned
    Panels0155.weightRows Panels0155.weights_checked ⟨7, by decide⟩
def b0156 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0156.block Panels0156.accepted Panels0156.integerPanels Panels0156.aligned
    Panels0156.weightRows Panels0156.weights_checked ⟨7, by decide⟩
def b0157 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0157.block Panels0157.accepted Panels0157.integerPanels Panels0157.aligned
    Panels0157.weightRows Panels0157.weights_checked ⟨7, by decide⟩
def b0158 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0158.block Panels0158.accepted Panels0158.integerPanels Panels0158.aligned
    Panels0158.weightRows Panels0158.weights_checked ⟨7, by decide⟩
def b0159 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0159.block Panels0159.accepted Panels0159.integerPanels Panels0159.aligned
    Panels0159.weightRows Panels0159.weights_checked ⟨7, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0152, b0153, b0154, b0155, b0156, b0157, b0158, b0159]
theorem chain_checked : blockChainCheck (1149425822459585220641394231371/10^30) (1475846938003328726491487854557/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=107663875435922391553096996561488962395619950876345831564531271446154942286220340277431632750955225392861915680260732619857799559615226366905075149040859238927323933487006567604960212984808594727564343044411227633/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row07
namespace Row08
abbrev ζ : ℚ := 25316455696202531645569620253/10^30
def b0152 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0152.block Panels0152.accepted Panels0152.integerPanels Panels0152.aligned
    Panels0152.weightRows Panels0152.weights_checked ⟨8, by decide⟩
def b0153 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0153.block Panels0153.accepted Panels0153.integerPanels Panels0153.aligned
    Panels0153.weightRows Panels0153.weights_checked ⟨8, by decide⟩
def b0154 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0154.block Panels0154.accepted Panels0154.integerPanels Panels0154.aligned
    Panels0154.weightRows Panels0154.weights_checked ⟨8, by decide⟩
def b0155 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0155.block Panels0155.accepted Panels0155.integerPanels Panels0155.aligned
    Panels0155.weightRows Panels0155.weights_checked ⟨8, by decide⟩
def b0156 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0156.block Panels0156.accepted Panels0156.integerPanels Panels0156.aligned
    Panels0156.weightRows Panels0156.weights_checked ⟨8, by decide⟩
def b0157 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0157.block Panels0157.accepted Panels0157.integerPanels Panels0157.aligned
    Panels0157.weightRows Panels0157.weights_checked ⟨8, by decide⟩
def b0158 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0158.block Panels0158.accepted Panels0158.integerPanels Panels0158.aligned
    Panels0158.weightRows Panels0158.weights_checked ⟨8, by decide⟩
def b0159 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0159.block Panels0159.accepted Panels0159.integerPanels Panels0159.aligned
    Panels0159.weightRows Panels0159.weights_checked ⟨8, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0152, b0153, b0154, b0155, b0156, b0157, b0158, b0159]
theorem chain_checked : blockChainCheck (1149425822459585220641394231371/10^30) (1475846938003328726491487854557/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=111450389619671602269461815864664110952592293935949859742472731663297614776606083351550764229298645092531203562185644331501496816160356394090829232177551050434916070960759495760928656769322022559299709684758857081/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row08
namespace Row09
abbrev ζ : ℚ := 18691588785046728971962616822/10^30
def b0152 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0152.block Panels0152.accepted Panels0152.integerPanels Panels0152.aligned
    Panels0152.weightRows Panels0152.weights_checked ⟨9, by decide⟩
def b0153 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0153.block Panels0153.accepted Panels0153.integerPanels Panels0153.aligned
    Panels0153.weightRows Panels0153.weights_checked ⟨9, by decide⟩
def b0154 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0154.block Panels0154.accepted Panels0154.integerPanels Panels0154.aligned
    Panels0154.weightRows Panels0154.weights_checked ⟨9, by decide⟩
def b0155 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0155.block Panels0155.accepted Panels0155.integerPanels Panels0155.aligned
    Panels0155.weightRows Panels0155.weights_checked ⟨9, by decide⟩
def b0156 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0156.block Panels0156.accepted Panels0156.integerPanels Panels0156.aligned
    Panels0156.weightRows Panels0156.weights_checked ⟨9, by decide⟩
def b0157 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0157.block Panels0157.accepted Panels0157.integerPanels Panels0157.aligned
    Panels0157.weightRows Panels0157.weights_checked ⟨9, by decide⟩
def b0158 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0158.block Panels0158.accepted Panels0158.integerPanels Panels0158.aligned
    Panels0158.weightRows Panels0158.weights_checked ⟨9, by decide⟩
def b0159 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0159.block Panels0159.accepted Panels0159.integerPanels Panels0159.aligned
    Panels0159.weightRows Panels0159.weights_checked ⟨9, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0152, b0153, b0154, b0155, b0156, b0157, b0158, b0159]
theorem chain_checked : blockChainCheck (1149425822459585220641394231371/10^30) (1475846938003328726491487854557/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=114446045788163624347571583896753969741224925194040832976518922916017909089738575760970695291678993173961649692111201462783687970411799037809890658499640331778385369157536323491073183814310824053462167101936980279/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row09
namespace Row10
abbrev ζ : ℚ := 13793103448275862068965517241/10^30
def b0152 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0152.block Panels0152.accepted Panels0152.integerPanels Panels0152.aligned
    Panels0152.weightRows Panels0152.weights_checked ⟨10, by decide⟩
def b0153 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0153.block Panels0153.accepted Panels0153.integerPanels Panels0153.aligned
    Panels0153.weightRows Panels0153.weights_checked ⟨10, by decide⟩
def b0154 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0154.block Panels0154.accepted Panels0154.integerPanels Panels0154.aligned
    Panels0154.weightRows Panels0154.weights_checked ⟨10, by decide⟩
def b0155 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0155.block Panels0155.accepted Panels0155.integerPanels Panels0155.aligned
    Panels0155.weightRows Panels0155.weights_checked ⟨10, by decide⟩
def b0156 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0156.block Panels0156.accepted Panels0156.integerPanels Panels0156.aligned
    Panels0156.weightRows Panels0156.weights_checked ⟨10, by decide⟩
def b0157 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0157.block Panels0157.accepted Panels0157.integerPanels Panels0157.aligned
    Panels0157.weightRows Panels0157.weights_checked ⟨10, by decide⟩
def b0158 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0158.block Panels0158.accepted Panels0158.integerPanels Panels0158.aligned
    Panels0158.weightRows Panels0158.weights_checked ⟨10, by decide⟩
def b0159 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0159.block Panels0159.accepted Panels0159.integerPanels Panels0159.aligned
    Panels0159.weightRows Panels0159.weights_checked ⟨10, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0152, b0153, b0154, b0155, b0156, b0157, b0158, b0159]
theorem chain_checked : blockChainCheck (1149425822459585220641394231371/10^30) (1475846938003328726491487854557/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=116702410590556294971390749796480032490508019990817397053401668195702182747564513793205174136779723597789744622808533176197935903240318355675807110464738850793108533329669616947750532049141779560907748809557792257/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row10
namespace Row11
abbrev ζ : ℚ := 10152284263959390862944162436/10^30
def b0152 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0152.block Panels0152.accepted Panels0152.integerPanels Panels0152.aligned
    Panels0152.weightRows Panels0152.weights_checked ⟨11, by decide⟩
def b0153 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0153.block Panels0153.accepted Panels0153.integerPanels Panels0153.aligned
    Panels0153.weightRows Panels0153.weights_checked ⟨11, by decide⟩
def b0154 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0154.block Panels0154.accepted Panels0154.integerPanels Panels0154.aligned
    Panels0154.weightRows Panels0154.weights_checked ⟨11, by decide⟩
def b0155 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0155.block Panels0155.accepted Panels0155.integerPanels Panels0155.aligned
    Panels0155.weightRows Panels0155.weights_checked ⟨11, by decide⟩
def b0156 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0156.block Panels0156.accepted Panels0156.integerPanels Panels0156.aligned
    Panels0156.weightRows Panels0156.weights_checked ⟨11, by decide⟩
def b0157 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0157.block Panels0157.accepted Panels0157.integerPanels Panels0157.aligned
    Panels0157.weightRows Panels0157.weights_checked ⟨11, by decide⟩
def b0158 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0158.block Panels0158.accepted Panels0158.integerPanels Panels0158.aligned
    Panels0158.weightRows Panels0158.weights_checked ⟨11, by decide⟩
def b0159 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0159.block Panels0159.accepted Panels0159.integerPanels Panels0159.aligned
    Panels0159.weightRows Panels0159.weights_checked ⟨11, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0152, b0153, b0154, b0155, b0156, b0157, b0158, b0159]
theorem chain_checked : blockChainCheck (1149425822459585220641394231371/10^30) (1475846938003328726491487854557/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=118402517493210528682181998934831051336610921189456096751019384139551661915017072425181785542247625091376218160531410424474262713553895588483778136850153668664838069944409505382155422294163744361376667341271456527/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row11
namespace Row12
abbrev ζ : ℚ := 9950248756218905472636815920/10^30
def b0152 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0152.block Panels0152.accepted Panels0152.integerPanels Panels0152.aligned
    Panels0152.weightRows Panels0152.weights_checked ⟨12, by decide⟩
def b0153 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0153.block Panels0153.accepted Panels0153.integerPanels Panels0153.aligned
    Panels0153.weightRows Panels0153.weights_checked ⟨12, by decide⟩
def b0154 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0154.block Panels0154.accepted Panels0154.integerPanels Panels0154.aligned
    Panels0154.weightRows Panels0154.weights_checked ⟨12, by decide⟩
def b0155 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0155.block Panels0155.accepted Panels0155.integerPanels Panels0155.aligned
    Panels0155.weightRows Panels0155.weights_checked ⟨12, by decide⟩
def b0156 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0156.block Panels0156.accepted Panels0156.integerPanels Panels0156.aligned
    Panels0156.weightRows Panels0156.weights_checked ⟨12, by decide⟩
def b0157 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0157.block Panels0157.accepted Panels0157.integerPanels Panels0157.aligned
    Panels0157.weightRows Panels0157.weights_checked ⟨12, by decide⟩
def b0158 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0158.block Panels0158.accepted Panels0158.integerPanels Panels0158.aligned
    Panels0158.weightRows Panels0158.weights_checked ⟨12, by decide⟩
def b0159 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0159.block Panels0159.accepted Panels0159.integerPanels Panels0159.aligned
    Panels0159.weightRows Panels0159.weights_checked ⟨12, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0152, b0153, b0154, b0155, b0156, b0157, b0158, b0159]
theorem chain_checked : blockChainCheck (1149425822459585220641394231371/10^30) (1475846938003328726491487854557/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=118497439215746138916425686218545630577979964176209695191390944506173306857416503700692680710024598190180276223093301080046685061050415434960137601756965529584771799568531521211277172207616444967655159974165709015/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row12
#print axioms Row12.segment
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments019
