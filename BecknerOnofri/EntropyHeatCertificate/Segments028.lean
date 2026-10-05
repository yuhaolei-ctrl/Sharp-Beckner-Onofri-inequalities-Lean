module

public import BecknerOnofri.EntropyHeatCheckedWeights
public import BecknerOnofri.EntropyHeatSegments
public import BecknerOnofri.EntropyHeatCertificate.Panels0224
public import BecknerOnofri.EntropyHeatCertificate.Panels0225
public import BecknerOnofri.EntropyHeatCertificate.Panels0226
public import BecknerOnofri.EntropyHeatCertificate.Panels0227
public import BecknerOnofri.EntropyHeatCertificate.Panels0228
public import BecknerOnofri.EntropyHeatCertificate.Panels0229
public import BecknerOnofri.EntropyHeatCertificate.Panels0230
public import BecknerOnofri.EntropyHeatCertificate.Panels0231

@[expose] public section
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments028
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace Row00
abbrev ζ : ℚ := 285714285714285714285714285714/10^30
def b0224 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0224.block Panels0224.accepted Panels0224.integerPanels Panels0224.aligned
    Panels0224.weightRows Panels0224.weights_checked ⟨0, by decide⟩
def b0225 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0225.block Panels0225.accepted Panels0225.integerPanels Panels0225.aligned
    Panels0225.weightRows Panels0225.weights_checked ⟨0, by decide⟩
def b0226 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0226.block Panels0226.accepted Panels0226.integerPanels Panels0226.aligned
    Panels0226.weightRows Panels0226.weights_checked ⟨0, by decide⟩
def b0227 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0227.block Panels0227.accepted Panels0227.integerPanels Panels0227.aligned
    Panels0227.weightRows Panels0227.weights_checked ⟨0, by decide⟩
def b0228 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0228.block Panels0228.accepted Panels0228.integerPanels Panels0228.aligned
    Panels0228.weightRows Panels0228.weights_checked ⟨0, by decide⟩
def b0229 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0229.block Panels0229.accepted Panels0229.integerPanels Panels0229.aligned
    Panels0229.weightRows Panels0229.weights_checked ⟨0, by decide⟩
def b0230 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0230.block Panels0230.accepted Panels0230.integerPanels Panels0230.aligned
    Panels0230.weightRows Panels0230.weights_checked ⟨0, by decide⟩
def b0231 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0231.block Panels0231.accepted Panels0231.integerPanels Panels0231.aligned
    Panels0231.weightRows Panels0231.weights_checked ⟨0, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0224, b0225, b0226, b0227, b0228, b0229, b0230, b0231]
theorem chain_checked : blockChainCheck (10902454194666651963197333024984/10^30) (13998601149824155699700021888720/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=634161943990541466937422638484687419636223483828150939795100275292842187426358872446572483543083578865176355177323941413115955088910360760541071334333063529310141629217692259522807320634645746358081/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row00
namespace Row01
abbrev ζ : ℚ := 222222222222222222222222222222/10^30
def b0224 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0224.block Panels0224.accepted Panels0224.integerPanels Panels0224.aligned
    Panels0224.weightRows Panels0224.weights_checked ⟨1, by decide⟩
def b0225 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0225.block Panels0225.accepted Panels0225.integerPanels Panels0225.aligned
    Panels0225.weightRows Panels0225.weights_checked ⟨1, by decide⟩
def b0226 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0226.block Panels0226.accepted Panels0226.integerPanels Panels0226.aligned
    Panels0226.weightRows Panels0226.weights_checked ⟨1, by decide⟩
def b0227 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0227.block Panels0227.accepted Panels0227.integerPanels Panels0227.aligned
    Panels0227.weightRows Panels0227.weights_checked ⟨1, by decide⟩
def b0228 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0228.block Panels0228.accepted Panels0228.integerPanels Panels0228.aligned
    Panels0228.weightRows Panels0228.weights_checked ⟨1, by decide⟩
def b0229 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0229.block Panels0229.accepted Panels0229.integerPanels Panels0229.aligned
    Panels0229.weightRows Panels0229.weights_checked ⟨1, by decide⟩
def b0230 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0230.block Panels0230.accepted Panels0230.integerPanels Panels0230.aligned
    Panels0230.weightRows Panels0230.weights_checked ⟨1, by decide⟩
def b0231 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0231.block Panels0231.accepted Panels0231.integerPanels Panels0231.aligned
    Panels0231.weightRows Panels0231.weights_checked ⟨1, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0224, b0225, b0226, b0227, b0228, b0229, b0230, b0231]
theorem chain_checked : blockChainCheck (10902454194666651963197333024984/10^30) (13998601149824155699700021888720/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=652863357633322901704880767027599068650658138141646069600979775481710558151720203587343315480807624456332987586344732380103769231085484555958495109723147292451604607993795895775005404603543878461577/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row01
namespace Row02
abbrev ζ : ℚ := 153846153846153846153846153846/10^30
def b0224 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0224.block Panels0224.accepted Panels0224.integerPanels Panels0224.aligned
    Panels0224.weightRows Panels0224.weights_checked ⟨2, by decide⟩
def b0225 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0225.block Panels0225.accepted Panels0225.integerPanels Panels0225.aligned
    Panels0225.weightRows Panels0225.weights_checked ⟨2, by decide⟩
def b0226 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0226.block Panels0226.accepted Panels0226.integerPanels Panels0226.aligned
    Panels0226.weightRows Panels0226.weights_checked ⟨2, by decide⟩
def b0227 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0227.block Panels0227.accepted Panels0227.integerPanels Panels0227.aligned
    Panels0227.weightRows Panels0227.weights_checked ⟨2, by decide⟩
def b0228 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0228.block Panels0228.accepted Panels0228.integerPanels Panels0228.aligned
    Panels0228.weightRows Panels0228.weights_checked ⟨2, by decide⟩
def b0229 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0229.block Panels0229.accepted Panels0229.integerPanels Panels0229.aligned
    Panels0229.weightRows Panels0229.weights_checked ⟨2, by decide⟩
def b0230 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0230.block Panels0230.accepted Panels0230.integerPanels Panels0230.aligned
    Panels0230.weightRows Panels0230.weights_checked ⟨2, by decide⟩
def b0231 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0231.block Panels0231.accepted Panels0231.integerPanels Panels0231.aligned
    Panels0231.weightRows Panels0231.weights_checked ⟨2, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0224, b0225, b0226, b0227, b0228, b0229, b0230, b0231]
theorem chain_checked : blockChainCheck (10902454194666651963197333024984/10^30) (13998601149824155699700021888720/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=673494392675527678332434403906352104978973550883296415454222992754559440222803037561259012998823202461356947084803880888536002715994159309225569115694934173667604511639097976394192856020232212350105/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row02
namespace Row03
abbrev ζ : ℚ := 117647058823529411764705882352/10^30
def b0224 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0224.block Panels0224.accepted Panels0224.integerPanels Panels0224.aligned
    Panels0224.weightRows Panels0224.weights_checked ⟨3, by decide⟩
def b0225 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0225.block Panels0225.accepted Panels0225.integerPanels Panels0225.aligned
    Panels0225.weightRows Panels0225.weights_checked ⟨3, by decide⟩
def b0226 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0226.block Panels0226.accepted Panels0226.integerPanels Panels0226.aligned
    Panels0226.weightRows Panels0226.weights_checked ⟨3, by decide⟩
def b0227 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0227.block Panels0227.accepted Panels0227.integerPanels Panels0227.aligned
    Panels0227.weightRows Panels0227.weights_checked ⟨3, by decide⟩
def b0228 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0228.block Panels0228.accepted Panels0228.integerPanels Panels0228.aligned
    Panels0228.weightRows Panels0228.weights_checked ⟨3, by decide⟩
def b0229 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0229.block Panels0229.accepted Panels0229.integerPanels Panels0229.aligned
    Panels0229.weightRows Panels0229.weights_checked ⟨3, by decide⟩
def b0230 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0230.block Panels0230.accepted Panels0230.integerPanels Panels0230.aligned
    Panels0230.weightRows Panels0230.weights_checked ⟨3, by decide⟩
def b0231 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0231.block Panels0231.accepted Panels0231.integerPanels Panels0231.aligned
    Panels0231.weightRows Panels0231.weights_checked ⟨3, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0224, b0225, b0226, b0227, b0228, b0229, b0230, b0231]
theorem chain_checked : blockChainCheck (10902454194666651963197333024984/10^30) (13998601149824155699700021888720/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=684626048571783978922925234207621503124104483251961363753934798146363864798288351405032205749060620406031399501460512983041973223833754040715871666677379952228593939197104484446578906719910684666457/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row03
namespace Row04
abbrev ζ : ℚ := 86956521739130434782608695652/10^30
def b0224 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0224.block Panels0224.accepted Panels0224.integerPanels Panels0224.aligned
    Panels0224.weightRows Panels0224.weights_checked ⟨4, by decide⟩
def b0225 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0225.block Panels0225.accepted Panels0225.integerPanels Panels0225.aligned
    Panels0225.weightRows Panels0225.weights_checked ⟨4, by decide⟩
def b0226 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0226.block Panels0226.accepted Panels0226.integerPanels Panels0226.aligned
    Panels0226.weightRows Panels0226.weights_checked ⟨4, by decide⟩
def b0227 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0227.block Panels0227.accepted Panels0227.integerPanels Panels0227.aligned
    Panels0227.weightRows Panels0227.weights_checked ⟨4, by decide⟩
def b0228 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0228.block Panels0228.accepted Panels0228.integerPanels Panels0228.aligned
    Panels0228.weightRows Panels0228.weights_checked ⟨4, by decide⟩
def b0229 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0229.block Panels0229.accepted Panels0229.integerPanels Panels0229.aligned
    Panels0229.weightRows Panels0229.weights_checked ⟨4, by decide⟩
def b0230 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0230.block Panels0230.accepted Panels0230.integerPanels Panels0230.aligned
    Panels0230.weightRows Panels0230.weights_checked ⟨4, by decide⟩
def b0231 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0231.block Panels0231.accepted Panels0231.integerPanels Panels0231.aligned
    Panels0231.weightRows Panels0231.weights_checked ⟨4, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0224, b0225, b0226, b0227, b0228, b0229, b0230, b0231]
theorem chain_checked : blockChainCheck (10902454194666651963197333024984/10^30) (13998601149824155699700021888720/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=694178683993076787001440399089736660863913067233219348053968622608532547022084951969217035129949353692693704720196483800522150739667495549824694066568756974791066313091956422540737101735495531932257/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row04
namespace Row05
abbrev ζ : ℚ := 64516129032258064516129032258/10^30
def b0224 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0224.block Panels0224.accepted Panels0224.integerPanels Panels0224.aligned
    Panels0224.weightRows Panels0224.weights_checked ⟨5, by decide⟩
def b0225 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0225.block Panels0225.accepted Panels0225.integerPanels Panels0225.aligned
    Panels0225.weightRows Panels0225.weights_checked ⟨5, by decide⟩
def b0226 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0226.block Panels0226.accepted Panels0226.integerPanels Panels0226.aligned
    Panels0226.weightRows Panels0226.weights_checked ⟨5, by decide⟩
def b0227 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0227.block Panels0227.accepted Panels0227.integerPanels Panels0227.aligned
    Panels0227.weightRows Panels0227.weights_checked ⟨5, by decide⟩
def b0228 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0228.block Panels0228.accepted Panels0228.integerPanels Panels0228.aligned
    Panels0228.weightRows Panels0228.weights_checked ⟨5, by decide⟩
def b0229 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0229.block Panels0229.accepted Panels0229.integerPanels Panels0229.aligned
    Panels0229.weightRows Panels0229.weights_checked ⟨5, by decide⟩
def b0230 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0230.block Panels0230.accepted Panels0230.integerPanels Panels0230.aligned
    Panels0230.weightRows Panels0230.weights_checked ⟨5, by decide⟩
def b0231 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0231.block Panels0231.accepted Panels0231.integerPanels Panels0231.aligned
    Panels0231.weightRows Panels0231.weights_checked ⟨5, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0224, b0225, b0226, b0227, b0228, b0229, b0230, b0231]
theorem chain_checked : blockChainCheck (10902454194666651963197333024984/10^30) (13998601149824155699700021888720/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=701230695722824095860782961266003146565079597314387094493379664375552786718932125511712813274955395297337724657194891626343788879139096062994533058089606822263035765104461554060718935158616662623009/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row05
namespace Row06
abbrev ζ : ℚ := 46511627906976744186046511627/10^30
def b0224 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0224.block Panels0224.accepted Panels0224.integerPanels Panels0224.aligned
    Panels0224.weightRows Panels0224.weights_checked ⟨6, by decide⟩
def b0225 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0225.block Panels0225.accepted Panels0225.integerPanels Panels0225.aligned
    Panels0225.weightRows Panels0225.weights_checked ⟨6, by decide⟩
def b0226 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0226.block Panels0226.accepted Panels0226.integerPanels Panels0226.aligned
    Panels0226.weightRows Panels0226.weights_checked ⟨6, by decide⟩
def b0227 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0227.block Panels0227.accepted Panels0227.integerPanels Panels0227.aligned
    Panels0227.weightRows Panels0227.weights_checked ⟨6, by decide⟩
def b0228 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0228.block Panels0228.accepted Panels0228.integerPanels Panels0228.aligned
    Panels0228.weightRows Panels0228.weights_checked ⟨6, by decide⟩
def b0229 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0229.block Panels0229.accepted Panels0229.integerPanels Panels0229.aligned
    Panels0229.weightRows Panels0229.weights_checked ⟨6, by decide⟩
def b0230 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0230.block Panels0230.accepted Panels0230.integerPanels Panels0230.aligned
    Panels0230.weightRows Panels0230.weights_checked ⟨6, by decide⟩
def b0231 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0231.block Panels0231.accepted Panels0231.integerPanels Panels0231.aligned
    Panels0231.weightRows Panels0231.weights_checked ⟨6, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0224, b0225, b0226, b0227, b0228, b0229, b0230, b0231]
theorem chain_checked : blockChainCheck (10902454194666651963197333024984/10^30) (13998601149824155699700021888720/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=706930066752295800441213198612195475851464045326981751219295946429102975766297122861187671704078538540145376303748586241409322335036256477616749434945259104586421428729736765792083286133314869812607/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row06
namespace Row07
abbrev ζ : ℚ := 33898305084745762711864406779/10^30
def b0224 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0224.block Panels0224.accepted Panels0224.integerPanels Panels0224.aligned
    Panels0224.weightRows Panels0224.weights_checked ⟨7, by decide⟩
def b0225 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0225.block Panels0225.accepted Panels0225.integerPanels Panels0225.aligned
    Panels0225.weightRows Panels0225.weights_checked ⟨7, by decide⟩
def b0226 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0226.block Panels0226.accepted Panels0226.integerPanels Panels0226.aligned
    Panels0226.weightRows Panels0226.weights_checked ⟨7, by decide⟩
def b0227 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0227.block Panels0227.accepted Panels0227.integerPanels Panels0227.aligned
    Panels0227.weightRows Panels0227.weights_checked ⟨7, by decide⟩
def b0228 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0228.block Panels0228.accepted Panels0228.integerPanels Panels0228.aligned
    Panels0228.weightRows Panels0228.weights_checked ⟨7, by decide⟩
def b0229 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0229.block Panels0229.accepted Panels0229.integerPanels Panels0229.aligned
    Panels0229.weightRows Panels0229.weights_checked ⟨7, by decide⟩
def b0230 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0230.block Panels0230.accepted Panels0230.integerPanels Panels0230.aligned
    Panels0230.weightRows Panels0230.weights_checked ⟨7, by decide⟩
def b0231 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0231.block Panels0231.accepted Panels0231.integerPanels Panels0231.aligned
    Panels0231.weightRows Panels0231.weights_checked ⟨7, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0224, b0225, b0226, b0227, b0228, b0229, b0230, b0231]
theorem chain_checked : blockChainCheck (10902454194666651963197333024984/10^30) (13998601149824155699700021888720/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=710944887437507563348911670263526648028265392940580307598766698799323099979479718463895403241285469876070162990857131175982695256627032406359054965596846281010738711643607884248916668226709371101471/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row07
namespace Row08
abbrev ζ : ℚ := 25316455696202531645569620253/10^30
def b0224 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0224.block Panels0224.accepted Panels0224.integerPanels Panels0224.aligned
    Panels0224.weightRows Panels0224.weights_checked ⟨8, by decide⟩
def b0225 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0225.block Panels0225.accepted Panels0225.integerPanels Panels0225.aligned
    Panels0225.weightRows Panels0225.weights_checked ⟨8, by decide⟩
def b0226 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0226.block Panels0226.accepted Panels0226.integerPanels Panels0226.aligned
    Panels0226.weightRows Panels0226.weights_checked ⟨8, by decide⟩
def b0227 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0227.block Panels0227.accepted Panels0227.integerPanels Panels0227.aligned
    Panels0227.weightRows Panels0227.weights_checked ⟨8, by decide⟩
def b0228 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0228.block Panels0228.accepted Panels0228.integerPanels Panels0228.aligned
    Panels0228.weightRows Panels0228.weights_checked ⟨8, by decide⟩
def b0229 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0229.block Panels0229.accepted Panels0229.integerPanels Panels0229.aligned
    Panels0229.weightRows Panels0229.weights_checked ⟨8, by decide⟩
def b0230 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0230.block Panels0230.accepted Panels0230.integerPanels Panels0230.aligned
    Panels0230.weightRows Panels0230.weights_checked ⟨8, by decide⟩
def b0231 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0231.block Panels0231.accepted Panels0231.integerPanels Panels0231.aligned
    Panels0231.weightRows Panels0231.weights_checked ⟨8, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0224, b0225, b0226, b0227, b0228, b0229, b0230, b0231]
theorem chain_checked : blockChainCheck (10902454194666651963197333024984/10^30) (13998601149824155699700021888720/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=713686907903220753961902848465904868066654638726645491750787167098383101964794549781379223703149082677492901423952979915480851116845298110384340206390298035288646731477800430765389840128887965520479/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row08
namespace Row09
abbrev ζ : ℚ := 18691588785046728971962616822/10^30
def b0224 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0224.block Panels0224.accepted Panels0224.integerPanels Panels0224.aligned
    Panels0224.weightRows Panels0224.weights_checked ⟨9, by decide⟩
def b0225 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0225.block Panels0225.accepted Panels0225.integerPanels Panels0225.aligned
    Panels0225.weightRows Panels0225.weights_checked ⟨9, by decide⟩
def b0226 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0226.block Panels0226.accepted Panels0226.integerPanels Panels0226.aligned
    Panels0226.weightRows Panels0226.weights_checked ⟨9, by decide⟩
def b0227 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0227.block Panels0227.accepted Panels0227.integerPanels Panels0227.aligned
    Panels0227.weightRows Panels0227.weights_checked ⟨9, by decide⟩
def b0228 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0228.block Panels0228.accepted Panels0228.integerPanels Panels0228.aligned
    Panels0228.weightRows Panels0228.weights_checked ⟨9, by decide⟩
def b0229 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0229.block Panels0229.accepted Panels0229.integerPanels Panels0229.aligned
    Panels0229.weightRows Panels0229.weights_checked ⟨9, by decide⟩
def b0230 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0230.block Panels0230.accepted Panels0230.integerPanels Panels0230.aligned
    Panels0230.weightRows Panels0230.weights_checked ⟨9, by decide⟩
def b0231 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0231.block Panels0231.accepted Panels0231.integerPanels Panels0231.aligned
    Panels0231.weightRows Panels0231.weights_checked ⟨9, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0224, b0225, b0226, b0227, b0228, b0229, b0230, b0231]
theorem chain_checked : blockChainCheck (10902454194666651963197333024984/10^30) (13998601149824155699700021888720/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=715809429556404074513500719307376060084390504328638477798123797536671612196993288945404017240145058079880809016530467736810985391812626358909038193741039139887463796262057066135037575306103516641177/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row09
namespace Row10
abbrev ζ : ℚ := 13793103448275862068965517241/10^30
def b0224 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0224.block Panels0224.accepted Panels0224.integerPanels Panels0224.aligned
    Panels0224.weightRows Panels0224.weights_checked ⟨10, by decide⟩
def b0225 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0225.block Panels0225.accepted Panels0225.integerPanels Panels0225.aligned
    Panels0225.weightRows Panels0225.weights_checked ⟨10, by decide⟩
def b0226 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0226.block Panels0226.accepted Panels0226.integerPanels Panels0226.aligned
    Panels0226.weightRows Panels0226.weights_checked ⟨10, by decide⟩
def b0227 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0227.block Panels0227.accepted Panels0227.integerPanels Panels0227.aligned
    Panels0227.weightRows Panels0227.weights_checked ⟨10, by decide⟩
def b0228 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0228.block Panels0228.accepted Panels0228.integerPanels Panels0228.aligned
    Panels0228.weightRows Panels0228.weights_checked ⟨10, by decide⟩
def b0229 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0229.block Panels0229.accepted Panels0229.integerPanels Panels0229.aligned
    Panels0229.weightRows Panels0229.weights_checked ⟨10, by decide⟩
def b0230 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0230.block Panels0230.accepted Panels0230.integerPanels Panels0230.aligned
    Panels0230.weightRows Panels0230.weights_checked ⟨10, by decide⟩
def b0231 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0231.block Panels0231.accepted Panels0231.integerPanels Panels0231.aligned
    Panels0231.weightRows Panels0231.weights_checked ⟨10, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0224, b0225, b0226, b0227, b0228, b0229, b0230, b0231]
theorem chain_checked : blockChainCheck (10902454194666651963197333024984/10^30) (13998601149824155699700021888720/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=717382087772576058618031408600164316334134827364815764555080815585314407589718345914209021643351198753526262212763544299466275019922130586807335670932244795285536169188405457613171880318403436509575/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row10
namespace Row11
abbrev ζ : ℚ := 10152284263959390862944162436/10^30
def b0224 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0224.block Panels0224.accepted Panels0224.integerPanels Panels0224.aligned
    Panels0224.weightRows Panels0224.weights_checked ⟨11, by decide⟩
def b0225 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0225.block Panels0225.accepted Panels0225.integerPanels Panels0225.aligned
    Panels0225.weightRows Panels0225.weights_checked ⟨11, by decide⟩
def b0226 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0226.block Panels0226.accepted Panels0226.integerPanels Panels0226.aligned
    Panels0226.weightRows Panels0226.weights_checked ⟨11, by decide⟩
def b0227 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0227.block Panels0227.accepted Panels0227.integerPanels Panels0227.aligned
    Panels0227.weightRows Panels0227.weights_checked ⟨11, by decide⟩
def b0228 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0228.block Panels0228.accepted Panels0228.integerPanels Panels0228.aligned
    Panels0228.weightRows Panels0228.weights_checked ⟨11, by decide⟩
def b0229 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0229.block Panels0229.accepted Panels0229.integerPanels Panels0229.aligned
    Panels0229.weightRows Panels0229.weights_checked ⟨11, by decide⟩
def b0230 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0230.block Panels0230.accepted Panels0230.integerPanels Panels0230.aligned
    Panels0230.weightRows Panels0230.weights_checked ⟨11, by decide⟩
def b0231 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0231.block Panels0231.accepted Panels0231.integerPanels Panels0231.aligned
    Panels0231.weightRows Panels0231.weights_checked ⟨11, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0224, b0225, b0226, b0227, b0228, b0229, b0230, b0231]
theorem chain_checked : blockChainCheck (10902454194666651963197333024984/10^30) (13998601149824155699700021888720/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=718552763164584792892184493092052037733283942468512947515524872021770181045047727255586374251766734795476912225374013289683930949227464246667111125885073270539307093312439461375941649233604583661345/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row11
namespace Row12
abbrev ζ : ℚ := 9950248756218905472636815920/10^30
def b0224 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0224.block Panels0224.accepted Panels0224.integerPanels Panels0224.aligned
    Panels0224.weightRows Panels0224.weights_checked ⟨12, by decide⟩
def b0225 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0225.block Panels0225.accepted Panels0225.integerPanels Panels0225.aligned
    Panels0225.weightRows Panels0225.weights_checked ⟨12, by decide⟩
def b0226 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0226.block Panels0226.accepted Panels0226.integerPanels Panels0226.aligned
    Panels0226.weightRows Panels0226.weights_checked ⟨12, by decide⟩
def b0227 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0227.block Panels0227.accepted Panels0227.integerPanels Panels0227.aligned
    Panels0227.weightRows Panels0227.weights_checked ⟨12, by decide⟩
def b0228 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0228.block Panels0228.accepted Panels0228.integerPanels Panels0228.aligned
    Panels0228.weightRows Panels0228.weights_checked ⟨12, by decide⟩
def b0229 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0229.block Panels0229.accepted Panels0229.integerPanels Panels0229.aligned
    Panels0229.weightRows Panels0229.weights_checked ⟨12, by decide⟩
def b0230 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0230.block Panels0230.accepted Panels0230.integerPanels Panels0230.aligned
    Panels0230.weightRows Panels0230.weights_checked ⟨12, by decide⟩
def b0231 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0231.block Panels0231.accepted Panels0231.integerPanels Panels0231.aligned
    Panels0231.weightRows Panels0231.weights_checked ⟨12, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0224, b0225, b0226, b0227, b0228, b0229, b0230, b0231]
theorem chain_checked : blockChainCheck (10902454194666651963197333024984/10^30) (13998601149824155699700021888720/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=718617770771171625392751794018983568195572824720685241118738309942159318173652037530708844858869359525979997604339206760752324816180654764173161663149097187018028288673524619062249673495905671759833/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row12
#print axioms Row12.segment
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments028
