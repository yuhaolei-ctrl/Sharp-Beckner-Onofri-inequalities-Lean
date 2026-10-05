module

public import BecknerOnofri.EntropyHeatCheckedWeights
public import BecknerOnofri.EntropyHeatSegments
public import BecknerOnofri.EntropyHeatCertificate.Panels0072
public import BecknerOnofri.EntropyHeatCertificate.Panels0073
public import BecknerOnofri.EntropyHeatCertificate.Panels0074
public import BecknerOnofri.EntropyHeatCertificate.Panels0075
public import BecknerOnofri.EntropyHeatCertificate.Panels0076
public import BecknerOnofri.EntropyHeatCertificate.Panels0077
public import BecknerOnofri.EntropyHeatCertificate.Panels0078
public import BecknerOnofri.EntropyHeatCertificate.Panels0079

@[expose] public section
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments009
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace Row00
abbrev ζ : ℚ := 285714285714285714285714285714/10^30
def b0072 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0072.block Panels0072.accepted Panels0072.integerPanels Panels0072.aligned
    Panels0072.weightRows Panels0072.weights_checked ⟨0, by decide⟩
def b0073 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0073.block Panels0073.accepted Panels0073.integerPanels Panels0073.aligned
    Panels0073.weightRows Panels0073.weights_checked ⟨0, by decide⟩
def b0074 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0074.block Panels0074.accepted Panels0074.integerPanels Panels0074.aligned
    Panels0074.weightRows Panels0074.weights_checked ⟨0, by decide⟩
def b0075 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0075.block Panels0075.accepted Panels0075.integerPanels Panels0075.aligned
    Panels0075.weightRows Panels0075.weights_checked ⟨0, by decide⟩
def b0076 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0076.block Panels0076.accepted Panels0076.integerPanels Panels0076.aligned
    Panels0076.weightRows Panels0076.weights_checked ⟨0, by decide⟩
def b0077 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0077.block Panels0077.accepted Panels0077.integerPanels Panels0077.aligned
    Panels0077.weightRows Panels0077.weights_checked ⟨0, by decide⟩
def b0078 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0078.block Panels0078.accepted Panels0078.integerPanels Panels0078.aligned
    Panels0078.weightRows Panels0078.weights_checked ⟨0, by decide⟩
def b0079 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0079.block Panels0079.accepted Panels0079.integerPanels Panels0079.aligned
    Panels0079.weightRows Panels0079.weights_checked ⟨0, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0072, b0073, b0074, b0075, b0076, b0077, b0078, b0079]
theorem chain_checked : blockChainCheck (94379410285111952461414366608/10^30) (121181863986477373198151782158/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row00
namespace Row01
abbrev ζ : ℚ := 222222222222222222222222222222/10^30
def b0072 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0072.block Panels0072.accepted Panels0072.integerPanels Panels0072.aligned
    Panels0072.weightRows Panels0072.weights_checked ⟨1, by decide⟩
def b0073 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0073.block Panels0073.accepted Panels0073.integerPanels Panels0073.aligned
    Panels0073.weightRows Panels0073.weights_checked ⟨1, by decide⟩
def b0074 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0074.block Panels0074.accepted Panels0074.integerPanels Panels0074.aligned
    Panels0074.weightRows Panels0074.weights_checked ⟨1, by decide⟩
def b0075 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0075.block Panels0075.accepted Panels0075.integerPanels Panels0075.aligned
    Panels0075.weightRows Panels0075.weights_checked ⟨1, by decide⟩
def b0076 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0076.block Panels0076.accepted Panels0076.integerPanels Panels0076.aligned
    Panels0076.weightRows Panels0076.weights_checked ⟨1, by decide⟩
def b0077 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0077.block Panels0077.accepted Panels0077.integerPanels Panels0077.aligned
    Panels0077.weightRows Panels0077.weights_checked ⟨1, by decide⟩
def b0078 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0078.block Panels0078.accepted Panels0078.integerPanels Panels0078.aligned
    Panels0078.weightRows Panels0078.weights_checked ⟨1, by decide⟩
def b0079 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0079.block Panels0079.accepted Panels0079.integerPanels Panels0079.aligned
    Panels0079.weightRows Panels0079.weights_checked ⟨1, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0072, b0073, b0074, b0075, b0076, b0077, b0078, b0079]
theorem chain_checked : blockChainCheck (94379410285111952461414366608/10^30) (121181863986477373198151782158/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row01
namespace Row02
abbrev ζ : ℚ := 153846153846153846153846153846/10^30
def b0072 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0072.block Panels0072.accepted Panels0072.integerPanels Panels0072.aligned
    Panels0072.weightRows Panels0072.weights_checked ⟨2, by decide⟩
def b0073 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0073.block Panels0073.accepted Panels0073.integerPanels Panels0073.aligned
    Panels0073.weightRows Panels0073.weights_checked ⟨2, by decide⟩
def b0074 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0074.block Panels0074.accepted Panels0074.integerPanels Panels0074.aligned
    Panels0074.weightRows Panels0074.weights_checked ⟨2, by decide⟩
def b0075 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0075.block Panels0075.accepted Panels0075.integerPanels Panels0075.aligned
    Panels0075.weightRows Panels0075.weights_checked ⟨2, by decide⟩
def b0076 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0076.block Panels0076.accepted Panels0076.integerPanels Panels0076.aligned
    Panels0076.weightRows Panels0076.weights_checked ⟨2, by decide⟩
def b0077 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0077.block Panels0077.accepted Panels0077.integerPanels Panels0077.aligned
    Panels0077.weightRows Panels0077.weights_checked ⟨2, by decide⟩
def b0078 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0078.block Panels0078.accepted Panels0078.integerPanels Panels0078.aligned
    Panels0078.weightRows Panels0078.weights_checked ⟨2, by decide⟩
def b0079 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0079.block Panels0079.accepted Panels0079.integerPanels Panels0079.aligned
    Panels0079.weightRows Panels0079.weights_checked ⟨2, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0072, b0073, b0074, b0075, b0076, b0077, b0078, b0079]
theorem chain_checked : blockChainCheck (94379410285111952461414366608/10^30) (121181863986477373198151782158/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row02
namespace Row03
abbrev ζ : ℚ := 117647058823529411764705882352/10^30
def b0072 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0072.block Panels0072.accepted Panels0072.integerPanels Panels0072.aligned
    Panels0072.weightRows Panels0072.weights_checked ⟨3, by decide⟩
def b0073 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0073.block Panels0073.accepted Panels0073.integerPanels Panels0073.aligned
    Panels0073.weightRows Panels0073.weights_checked ⟨3, by decide⟩
def b0074 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0074.block Panels0074.accepted Panels0074.integerPanels Panels0074.aligned
    Panels0074.weightRows Panels0074.weights_checked ⟨3, by decide⟩
def b0075 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0075.block Panels0075.accepted Panels0075.integerPanels Panels0075.aligned
    Panels0075.weightRows Panels0075.weights_checked ⟨3, by decide⟩
def b0076 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0076.block Panels0076.accepted Panels0076.integerPanels Panels0076.aligned
    Panels0076.weightRows Panels0076.weights_checked ⟨3, by decide⟩
def b0077 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0077.block Panels0077.accepted Panels0077.integerPanels Panels0077.aligned
    Panels0077.weightRows Panels0077.weights_checked ⟨3, by decide⟩
def b0078 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0078.block Panels0078.accepted Panels0078.integerPanels Panels0078.aligned
    Panels0078.weightRows Panels0078.weights_checked ⟨3, by decide⟩
def b0079 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0079.block Panels0079.accepted Panels0079.integerPanels Panels0079.aligned
    Panels0079.weightRows Panels0079.weights_checked ⟨3, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0072, b0073, b0074, b0075, b0076, b0077, b0078, b0079]
theorem chain_checked : blockChainCheck (94379410285111952461414366608/10^30) (121181863986477373198151782158/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=607437472387996320114934713095623609259064945310189478181517310536579385854486268975428957181148964590946459303584278293710660209387018842363268275066849710420575866941594817729091405552791144693097406576/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row03
namespace Row04
abbrev ζ : ℚ := 86956521739130434782608695652/10^30
def b0072 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0072.block Panels0072.accepted Panels0072.integerPanels Panels0072.aligned
    Panels0072.weightRows Panels0072.weights_checked ⟨4, by decide⟩
def b0073 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0073.block Panels0073.accepted Panels0073.integerPanels Panels0073.aligned
    Panels0073.weightRows Panels0073.weights_checked ⟨4, by decide⟩
def b0074 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0074.block Panels0074.accepted Panels0074.integerPanels Panels0074.aligned
    Panels0074.weightRows Panels0074.weights_checked ⟨4, by decide⟩
def b0075 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0075.block Panels0075.accepted Panels0075.integerPanels Panels0075.aligned
    Panels0075.weightRows Panels0075.weights_checked ⟨4, by decide⟩
def b0076 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0076.block Panels0076.accepted Panels0076.integerPanels Panels0076.aligned
    Panels0076.weightRows Panels0076.weights_checked ⟨4, by decide⟩
def b0077 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0077.block Panels0077.accepted Panels0077.integerPanels Panels0077.aligned
    Panels0077.weightRows Panels0077.weights_checked ⟨4, by decide⟩
def b0078 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0078.block Panels0078.accepted Panels0078.integerPanels Panels0078.aligned
    Panels0078.weightRows Panels0078.weights_checked ⟨4, by decide⟩
def b0079 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0079.block Panels0079.accepted Panels0079.integerPanels Panels0079.aligned
    Panels0079.weightRows Panels0079.weights_checked ⟨4, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0072, b0073, b0074, b0075, b0076, b0077, b0078, b0079]
theorem chain_checked : blockChainCheck (94379410285111952461414366608/10^30) (121181863986477373198151782158/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=644965962533492581195647646779743667951229576299704276550020843342172133125923213686894609183642507678399605002009777857136148472714445429735425021498913304188044220297912484624900298092832656704534147254539713/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row04
namespace Row05
abbrev ζ : ℚ := 64516129032258064516129032258/10^30
def b0072 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0072.block Panels0072.accepted Panels0072.integerPanels Panels0072.aligned
    Panels0072.weightRows Panels0072.weights_checked ⟨5, by decide⟩
def b0073 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0073.block Panels0073.accepted Panels0073.integerPanels Panels0073.aligned
    Panels0073.weightRows Panels0073.weights_checked ⟨5, by decide⟩
def b0074 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0074.block Panels0074.accepted Panels0074.integerPanels Panels0074.aligned
    Panels0074.weightRows Panels0074.weights_checked ⟨5, by decide⟩
def b0075 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0075.block Panels0075.accepted Panels0075.integerPanels Panels0075.aligned
    Panels0075.weightRows Panels0075.weights_checked ⟨5, by decide⟩
def b0076 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0076.block Panels0076.accepted Panels0076.integerPanels Panels0076.aligned
    Panels0076.weightRows Panels0076.weights_checked ⟨5, by decide⟩
def b0077 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0077.block Panels0077.accepted Panels0077.integerPanels Panels0077.aligned
    Panels0077.weightRows Panels0077.weights_checked ⟨5, by decide⟩
def b0078 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0078.block Panels0078.accepted Panels0078.integerPanels Panels0078.aligned
    Panels0078.weightRows Panels0078.weights_checked ⟨5, by decide⟩
def b0079 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0079.block Panels0079.accepted Panels0079.integerPanels Panels0079.aligned
    Panels0079.weightRows Panels0079.weights_checked ⟨5, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0072, b0073, b0074, b0075, b0076, b0077, b0078, b0079]
theorem chain_checked : blockChainCheck (94379410285111952461414366608/10^30) (121181863986477373198151782158/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=15592913889140628513618056978510585105485352707376417664756640178872672370174287093098380699367359689640788068180051751874641740792736011459155097267130836204833564253268501376428761005378114557692614791335049161/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row05
namespace Row06
abbrev ζ : ℚ := 46511627906976744186046511627/10^30
def b0072 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0072.block Panels0072.accepted Panels0072.integerPanels Panels0072.aligned
    Panels0072.weightRows Panels0072.weights_checked ⟨6, by decide⟩
def b0073 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0073.block Panels0073.accepted Panels0073.integerPanels Panels0073.aligned
    Panels0073.weightRows Panels0073.weights_checked ⟨6, by decide⟩
def b0074 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0074.block Panels0074.accepted Panels0074.integerPanels Panels0074.aligned
    Panels0074.weightRows Panels0074.weights_checked ⟨6, by decide⟩
def b0075 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0075.block Panels0075.accepted Panels0075.integerPanels Panels0075.aligned
    Panels0075.weightRows Panels0075.weights_checked ⟨6, by decide⟩
def b0076 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0076.block Panels0076.accepted Panels0076.integerPanels Panels0076.aligned
    Panels0076.weightRows Panels0076.weights_checked ⟨6, by decide⟩
def b0077 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0077.block Panels0077.accepted Panels0077.integerPanels Panels0077.aligned
    Panels0077.weightRows Panels0077.weights_checked ⟨6, by decide⟩
def b0078 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0078.block Panels0078.accepted Panels0078.integerPanels Panels0078.aligned
    Panels0078.weightRows Panels0078.weights_checked ⟨6, by decide⟩
def b0079 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0079.block Panels0079.accepted Panels0079.integerPanels Panels0079.aligned
    Panels0079.weightRows Panels0079.weights_checked ⟨6, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0072, b0073, b0074, b0075, b0076, b0077, b0078, b0079]
theorem chain_checked : blockChainCheck (94379410285111952461414366608/10^30) (121181863986477373198151782158/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=84831625070524968518523407142714652184093517791033197163304620435791817242232242304990179946599076821662977007996025494178480467072059163840583206119616874155983343654990904259147073311943572359367693801803011863/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row06
namespace Row07
abbrev ζ : ℚ := 33898305084745762711864406779/10^30
def b0072 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0072.block Panels0072.accepted Panels0072.integerPanels Panels0072.aligned
    Panels0072.weightRows Panels0072.weights_checked ⟨7, by decide⟩
def b0073 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0073.block Panels0073.accepted Panels0073.integerPanels Panels0073.aligned
    Panels0073.weightRows Panels0073.weights_checked ⟨7, by decide⟩
def b0074 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0074.block Panels0074.accepted Panels0074.integerPanels Panels0074.aligned
    Panels0074.weightRows Panels0074.weights_checked ⟨7, by decide⟩
def b0075 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0075.block Panels0075.accepted Panels0075.integerPanels Panels0075.aligned
    Panels0075.weightRows Panels0075.weights_checked ⟨7, by decide⟩
def b0076 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0076.block Panels0076.accepted Panels0076.integerPanels Panels0076.aligned
    Panels0076.weightRows Panels0076.weights_checked ⟨7, by decide⟩
def b0077 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0077.block Panels0077.accepted Panels0077.integerPanels Panels0077.aligned
    Panels0077.weightRows Panels0077.weights_checked ⟨7, by decide⟩
def b0078 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0078.block Panels0078.accepted Panels0078.integerPanels Panels0078.aligned
    Panels0078.weightRows Panels0078.weights_checked ⟨7, by decide⟩
def b0079 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0079.block Panels0079.accepted Panels0079.integerPanels Panels0079.aligned
    Panels0079.weightRows Panels0079.weights_checked ⟨7, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0072, b0073, b0074, b0075, b0076, b0077, b0078, b0079]
theorem chain_checked : blockChainCheck (94379410285111952461414366608/10^30) (121181863986477373198151782158/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=215531997347298245469960462840420927432390450126239315205106421353929664928235292004138462496236337224505820576752530609448540104094120471271961845908600935172866168075035053817112784058528412959168737588725031799/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row07
namespace Row08
abbrev ζ : ℚ := 25316455696202531645569620253/10^30
def b0072 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0072.block Panels0072.accepted Panels0072.integerPanels Panels0072.aligned
    Panels0072.weightRows Panels0072.weights_checked ⟨8, by decide⟩
def b0073 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0073.block Panels0073.accepted Panels0073.integerPanels Panels0073.aligned
    Panels0073.weightRows Panels0073.weights_checked ⟨8, by decide⟩
def b0074 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0074.block Panels0074.accepted Panels0074.integerPanels Panels0074.aligned
    Panels0074.weightRows Panels0074.weights_checked ⟨8, by decide⟩
def b0075 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0075.block Panels0075.accepted Panels0075.integerPanels Panels0075.aligned
    Panels0075.weightRows Panels0075.weights_checked ⟨8, by decide⟩
def b0076 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0076.block Panels0076.accepted Panels0076.integerPanels Panels0076.aligned
    Panels0076.weightRows Panels0076.weights_checked ⟨8, by decide⟩
def b0077 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0077.block Panels0077.accepted Panels0077.integerPanels Panels0077.aligned
    Panels0077.weightRows Panels0077.weights_checked ⟨8, by decide⟩
def b0078 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0078.block Panels0078.accepted Panels0078.integerPanels Panels0078.aligned
    Panels0078.weightRows Panels0078.weights_checked ⟨8, by decide⟩
def b0079 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0079.block Panels0079.accepted Panels0079.integerPanels Panels0079.aligned
    Panels0079.weightRows Panels0079.weights_checked ⟨8, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0072, b0073, b0074, b0075, b0076, b0077, b0078, b0079]
theorem chain_checked : blockChainCheck (94379410285111952461414366608/10^30) (121181863986477373198151782158/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=374033070144405438454659686425121556504002354055280807223792899426367951219287096801914889434577555604885290500171786999467233489927651214478689409219455180686687452070414906398155405801428934019577106126164980991/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row08
namespace Row09
abbrev ζ : ℚ := 18691588785046728971962616822/10^30
def b0072 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0072.block Panels0072.accepted Panels0072.integerPanels Panels0072.aligned
    Panels0072.weightRows Panels0072.weights_checked ⟨9, by decide⟩
def b0073 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0073.block Panels0073.accepted Panels0073.integerPanels Panels0073.aligned
    Panels0073.weightRows Panels0073.weights_checked ⟨9, by decide⟩
def b0074 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0074.block Panels0074.accepted Panels0074.integerPanels Panels0074.aligned
    Panels0074.weightRows Panels0074.weights_checked ⟨9, by decide⟩
def b0075 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0075.block Panels0075.accepted Panels0075.integerPanels Panels0075.aligned
    Panels0075.weightRows Panels0075.weights_checked ⟨9, by decide⟩
def b0076 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0076.block Panels0076.accepted Panels0076.integerPanels Panels0076.aligned
    Panels0076.weightRows Panels0076.weights_checked ⟨9, by decide⟩
def b0077 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0077.block Panels0077.accepted Panels0077.integerPanels Panels0077.aligned
    Panels0077.weightRows Panels0077.weights_checked ⟨9, by decide⟩
def b0078 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0078.block Panels0078.accepted Panels0078.integerPanels Panels0078.aligned
    Panels0078.weightRows Panels0078.weights_checked ⟨9, by decide⟩
def b0079 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0079.block Panels0079.accepted Panels0079.integerPanels Panels0079.aligned
    Panels0079.weightRows Panels0079.weights_checked ⟨9, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0072, b0073, b0074, b0075, b0076, b0077, b0078, b0079]
theorem chain_checked : blockChainCheck (94379410285111952461414366608/10^30) (121181863986477373198151782158/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=551767369286657511609670419810564812803575472259273014091966356477139599996154056724343583124904250732247192485293237393831995511084611672972836615902256657184377517110618628903279839784266945988691663582884959793/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row09
namespace Row10
abbrev ζ : ℚ := 13793103448275862068965517241/10^30
def b0072 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0072.block Panels0072.accepted Panels0072.integerPanels Panels0072.aligned
    Panels0072.weightRows Panels0072.weights_checked ⟨10, by decide⟩
def b0073 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0073.block Panels0073.accepted Panels0073.integerPanels Panels0073.aligned
    Panels0073.weightRows Panels0073.weights_checked ⟨10, by decide⟩
def b0074 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0074.block Panels0074.accepted Panels0074.integerPanels Panels0074.aligned
    Panels0074.weightRows Panels0074.weights_checked ⟨10, by decide⟩
def b0075 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0075.block Panels0075.accepted Panels0075.integerPanels Panels0075.aligned
    Panels0075.weightRows Panels0075.weights_checked ⟨10, by decide⟩
def b0076 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0076.block Panels0076.accepted Panels0076.integerPanels Panels0076.aligned
    Panels0076.weightRows Panels0076.weights_checked ⟨10, by decide⟩
def b0077 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0077.block Panels0077.accepted Panels0077.integerPanels Panels0077.aligned
    Panels0077.weightRows Panels0077.weights_checked ⟨10, by decide⟩
def b0078 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0078.block Panels0078.accepted Panels0078.integerPanels Panels0078.aligned
    Panels0078.weightRows Panels0078.weights_checked ⟨10, by decide⟩
def b0079 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0079.block Panels0079.accepted Panels0079.integerPanels Panels0079.aligned
    Panels0079.weightRows Panels0079.weights_checked ⟨10, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0072, b0073, b0074, b0075, b0076, b0077, b0078, b0079]
theorem chain_checked : blockChainCheck (94379410285111952461414366608/10^30) (121181863986477373198151782158/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=722603753761124068290562488842094499602871939104196996171079800832188107248535274931567333150412881946166064987686651522479619491664204849931961762647289126462709529572714780700987161670588742387672086345274201175/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row10
namespace Row11
abbrev ζ : ℚ := 10152284263959390862944162436/10^30
def b0072 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0072.block Panels0072.accepted Panels0072.integerPanels Panels0072.aligned
    Panels0072.weightRows Panels0072.weights_checked ⟨11, by decide⟩
def b0073 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0073.block Panels0073.accepted Panels0073.integerPanels Panels0073.aligned
    Panels0073.weightRows Panels0073.weights_checked ⟨11, by decide⟩
def b0074 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0074.block Panels0074.accepted Panels0074.integerPanels Panels0074.aligned
    Panels0074.weightRows Panels0074.weights_checked ⟨11, by decide⟩
def b0075 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0075.block Panels0075.accepted Panels0075.integerPanels Panels0075.aligned
    Panels0075.weightRows Panels0075.weights_checked ⟨11, by decide⟩
def b0076 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0076.block Panels0076.accepted Panels0076.integerPanels Panels0076.aligned
    Panels0076.weightRows Panels0076.weights_checked ⟨11, by decide⟩
def b0077 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0077.block Panels0077.accepted Panels0077.integerPanels Panels0077.aligned
    Panels0077.weightRows Panels0077.weights_checked ⟨11, by decide⟩
def b0078 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0078.block Panels0078.accepted Panels0078.integerPanels Panels0078.aligned
    Panels0078.weightRows Panels0078.weights_checked ⟨11, by decide⟩
def b0079 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0079.block Panels0079.accepted Panels0079.integerPanels Panels0079.aligned
    Panels0079.weightRows Panels0079.weights_checked ⟨11, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0072, b0073, b0074, b0075, b0076, b0077, b0078, b0079]
theorem chain_checked : blockChainCheck (94379410285111952461414366608/10^30) (121181863986477373198151782158/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=875292576546520228166447519132474088055356866519471856860815007427051744952307738822145584508196336442500825522552265080092318928400274167617604983909698030985339258387023014697628080127714993487714478400702869505/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row11
namespace Row12
abbrev ζ : ℚ := 9950248756218905472636815920/10^30
def b0072 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0072.block Panels0072.accepted Panels0072.integerPanels Panels0072.aligned
    Panels0072.weightRows Panels0072.weights_checked ⟨12, by decide⟩
def b0073 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0073.block Panels0073.accepted Panels0073.integerPanels Panels0073.aligned
    Panels0073.weightRows Panels0073.weights_checked ⟨12, by decide⟩
def b0074 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0074.block Panels0074.accepted Panels0074.integerPanels Panels0074.aligned
    Panels0074.weightRows Panels0074.weights_checked ⟨12, by decide⟩
def b0075 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0075.block Panels0075.accepted Panels0075.integerPanels Panels0075.aligned
    Panels0075.weightRows Panels0075.weights_checked ⟨12, by decide⟩
def b0076 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0076.block Panels0076.accepted Panels0076.integerPanels Panels0076.aligned
    Panels0076.weightRows Panels0076.weights_checked ⟨12, by decide⟩
def b0077 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0077.block Panels0077.accepted Panels0077.integerPanels Panels0077.aligned
    Panels0077.weightRows Panels0077.weights_checked ⟨12, by decide⟩
def b0078 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0078.block Panels0078.accepted Panels0078.integerPanels Panels0078.aligned
    Panels0078.weightRows Panels0078.weights_checked ⟨12, by decide⟩
def b0079 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0079.block Panels0079.accepted Panels0079.integerPanels Panels0079.aligned
    Panels0079.weightRows Panels0079.weights_checked ⟨12, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0072, b0073, b0074, b0075, b0076, b0077, b0078, b0079]
theorem chain_checked : blockChainCheck (94379410285111952461414366608/10^30) (121181863986477373198151782158/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=884470415222448990053055889484318505183362510585517649552484044731106210223325961466031070595428045169653498578127053687964108395049516447928036905077384945024528025648782829635510226759858697984134420873085386057/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row12
#print axioms Row12.segment
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments009
