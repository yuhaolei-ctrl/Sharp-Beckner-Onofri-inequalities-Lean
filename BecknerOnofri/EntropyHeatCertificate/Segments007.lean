module

public import BecknerOnofri.EntropyHeatCheckedWeights
public import BecknerOnofri.EntropyHeatSegments
public import BecknerOnofri.EntropyHeatCertificate.Panels0056
public import BecknerOnofri.EntropyHeatCertificate.Panels0057
public import BecknerOnofri.EntropyHeatCertificate.Panels0058
public import BecknerOnofri.EntropyHeatCertificate.Panels0059
public import BecknerOnofri.EntropyHeatCertificate.Panels0060
public import BecknerOnofri.EntropyHeatCertificate.Panels0061
public import BecknerOnofri.EntropyHeatCertificate.Panels0062
public import BecknerOnofri.EntropyHeatCertificate.Panels0063

@[expose] public section
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments007
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace Row00
abbrev ζ : ℚ := 285714285714285714285714285714/10^30
def b0056 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0056.block Panels0056.accepted Panels0056.integerPanels Panels0056.aligned
    Panels0056.weightRows Panels0056.weights_checked ⟨0, by decide⟩
def b0057 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0057.block Panels0057.accepted Panels0057.integerPanels Panels0057.aligned
    Panels0057.weightRows Panels0057.weights_checked ⟨0, by decide⟩
def b0058 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0058.block Panels0058.accepted Panels0058.integerPanels Panels0058.aligned
    Panels0058.weightRows Panels0058.weights_checked ⟨0, by decide⟩
def b0059 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0059.block Panels0059.accepted Panels0059.integerPanels Panels0059.aligned
    Panels0059.weightRows Panels0059.weights_checked ⟨0, by decide⟩
def b0060 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0060.block Panels0060.accepted Panels0060.integerPanels Panels0060.aligned
    Panels0060.weightRows Panels0060.weights_checked ⟨0, by decide⟩
def b0061 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0061.block Panels0061.accepted Panels0061.integerPanels Panels0061.aligned
    Panels0061.weightRows Panels0061.weights_checked ⟨0, by decide⟩
def b0062 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0062.block Panels0062.accepted Panels0062.integerPanels Panels0062.aligned
    Panels0062.weightRows Panels0062.weights_checked ⟨0, by decide⟩
def b0063 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0063.block Panels0063.accepted Panels0063.integerPanels Panels0063.aligned
    Panels0063.weightRows Panels0063.weights_checked ⟨0, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0056, b0057, b0058, b0059, b0060, b0061, b0062, b0063]
theorem chain_checked : blockChainCheck (57247499418396570304717986552/10^30) (73505001431232948341390251911/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row00
namespace Row01
abbrev ζ : ℚ := 222222222222222222222222222222/10^30
def b0056 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0056.block Panels0056.accepted Panels0056.integerPanels Panels0056.aligned
    Panels0056.weightRows Panels0056.weights_checked ⟨1, by decide⟩
def b0057 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0057.block Panels0057.accepted Panels0057.integerPanels Panels0057.aligned
    Panels0057.weightRows Panels0057.weights_checked ⟨1, by decide⟩
def b0058 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0058.block Panels0058.accepted Panels0058.integerPanels Panels0058.aligned
    Panels0058.weightRows Panels0058.weights_checked ⟨1, by decide⟩
def b0059 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0059.block Panels0059.accepted Panels0059.integerPanels Panels0059.aligned
    Panels0059.weightRows Panels0059.weights_checked ⟨1, by decide⟩
def b0060 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0060.block Panels0060.accepted Panels0060.integerPanels Panels0060.aligned
    Panels0060.weightRows Panels0060.weights_checked ⟨1, by decide⟩
def b0061 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0061.block Panels0061.accepted Panels0061.integerPanels Panels0061.aligned
    Panels0061.weightRows Panels0061.weights_checked ⟨1, by decide⟩
def b0062 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0062.block Panels0062.accepted Panels0062.integerPanels Panels0062.aligned
    Panels0062.weightRows Panels0062.weights_checked ⟨1, by decide⟩
def b0063 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0063.block Panels0063.accepted Panels0063.integerPanels Panels0063.aligned
    Panels0063.weightRows Panels0063.weights_checked ⟨1, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0056, b0057, b0058, b0059, b0060, b0061, b0062, b0063]
theorem chain_checked : blockChainCheck (57247499418396570304717986552/10^30) (73505001431232948341390251911/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row01
namespace Row02
abbrev ζ : ℚ := 153846153846153846153846153846/10^30
def b0056 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0056.block Panels0056.accepted Panels0056.integerPanels Panels0056.aligned
    Panels0056.weightRows Panels0056.weights_checked ⟨2, by decide⟩
def b0057 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0057.block Panels0057.accepted Panels0057.integerPanels Panels0057.aligned
    Panels0057.weightRows Panels0057.weights_checked ⟨2, by decide⟩
def b0058 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0058.block Panels0058.accepted Panels0058.integerPanels Panels0058.aligned
    Panels0058.weightRows Panels0058.weights_checked ⟨2, by decide⟩
def b0059 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0059.block Panels0059.accepted Panels0059.integerPanels Panels0059.aligned
    Panels0059.weightRows Panels0059.weights_checked ⟨2, by decide⟩
def b0060 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0060.block Panels0060.accepted Panels0060.integerPanels Panels0060.aligned
    Panels0060.weightRows Panels0060.weights_checked ⟨2, by decide⟩
def b0061 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0061.block Panels0061.accepted Panels0061.integerPanels Panels0061.aligned
    Panels0061.weightRows Panels0061.weights_checked ⟨2, by decide⟩
def b0062 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0062.block Panels0062.accepted Panels0062.integerPanels Panels0062.aligned
    Panels0062.weightRows Panels0062.weights_checked ⟨2, by decide⟩
def b0063 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0063.block Panels0063.accepted Panels0063.integerPanels Panels0063.aligned
    Panels0063.weightRows Panels0063.weights_checked ⟨2, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0056, b0057, b0058, b0059, b0060, b0061, b0062, b0063]
theorem chain_checked : blockChainCheck (57247499418396570304717986552/10^30) (73505001431232948341390251911/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row02
namespace Row03
abbrev ζ : ℚ := 117647058823529411764705882352/10^30
def b0056 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0056.block Panels0056.accepted Panels0056.integerPanels Panels0056.aligned
    Panels0056.weightRows Panels0056.weights_checked ⟨3, by decide⟩
def b0057 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0057.block Panels0057.accepted Panels0057.integerPanels Panels0057.aligned
    Panels0057.weightRows Panels0057.weights_checked ⟨3, by decide⟩
def b0058 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0058.block Panels0058.accepted Panels0058.integerPanels Panels0058.aligned
    Panels0058.weightRows Panels0058.weights_checked ⟨3, by decide⟩
def b0059 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0059.block Panels0059.accepted Panels0059.integerPanels Panels0059.aligned
    Panels0059.weightRows Panels0059.weights_checked ⟨3, by decide⟩
def b0060 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0060.block Panels0060.accepted Panels0060.integerPanels Panels0060.aligned
    Panels0060.weightRows Panels0060.weights_checked ⟨3, by decide⟩
def b0061 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0061.block Panels0061.accepted Panels0061.integerPanels Panels0061.aligned
    Panels0061.weightRows Panels0061.weights_checked ⟨3, by decide⟩
def b0062 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0062.block Panels0062.accepted Panels0062.integerPanels Panels0062.aligned
    Panels0062.weightRows Panels0062.weights_checked ⟨3, by decide⟩
def b0063 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0063.block Panels0063.accepted Panels0063.integerPanels Panels0063.aligned
    Panels0063.weightRows Panels0063.weights_checked ⟨3, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0056, b0057, b0058, b0059, b0060, b0061, b0062, b0063]
theorem chain_checked : blockChainCheck (57247499418396570304717986552/10^30) (73505001431232948341390251911/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row03
namespace Row04
abbrev ζ : ℚ := 86956521739130434782608695652/10^30
def b0056 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0056.block Panels0056.accepted Panels0056.integerPanels Panels0056.aligned
    Panels0056.weightRows Panels0056.weights_checked ⟨4, by decide⟩
def b0057 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0057.block Panels0057.accepted Panels0057.integerPanels Panels0057.aligned
    Panels0057.weightRows Panels0057.weights_checked ⟨4, by decide⟩
def b0058 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0058.block Panels0058.accepted Panels0058.integerPanels Panels0058.aligned
    Panels0058.weightRows Panels0058.weights_checked ⟨4, by decide⟩
def b0059 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0059.block Panels0059.accepted Panels0059.integerPanels Panels0059.aligned
    Panels0059.weightRows Panels0059.weights_checked ⟨4, by decide⟩
def b0060 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0060.block Panels0060.accepted Panels0060.integerPanels Panels0060.aligned
    Panels0060.weightRows Panels0060.weights_checked ⟨4, by decide⟩
def b0061 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0061.block Panels0061.accepted Panels0061.integerPanels Panels0061.aligned
    Panels0061.weightRows Panels0061.weights_checked ⟨4, by decide⟩
def b0062 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0062.block Panels0062.accepted Panels0062.integerPanels Panels0062.aligned
    Panels0062.weightRows Panels0062.weights_checked ⟨4, by decide⟩
def b0063 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0063.block Panels0063.accepted Panels0063.integerPanels Panels0063.aligned
    Panels0063.weightRows Panels0063.weights_checked ⟨4, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0056, b0057, b0058, b0059, b0060, b0061, b0062, b0063]
theorem chain_checked : blockChainCheck (57247499418396570304717986552/10^30) (73505001431232948341390251911/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row04
namespace Row05
abbrev ζ : ℚ := 64516129032258064516129032258/10^30
def b0056 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0056.block Panels0056.accepted Panels0056.integerPanels Panels0056.aligned
    Panels0056.weightRows Panels0056.weights_checked ⟨5, by decide⟩
def b0057 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0057.block Panels0057.accepted Panels0057.integerPanels Panels0057.aligned
    Panels0057.weightRows Panels0057.weights_checked ⟨5, by decide⟩
def b0058 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0058.block Panels0058.accepted Panels0058.integerPanels Panels0058.aligned
    Panels0058.weightRows Panels0058.weights_checked ⟨5, by decide⟩
def b0059 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0059.block Panels0059.accepted Panels0059.integerPanels Panels0059.aligned
    Panels0059.weightRows Panels0059.weights_checked ⟨5, by decide⟩
def b0060 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0060.block Panels0060.accepted Panels0060.integerPanels Panels0060.aligned
    Panels0060.weightRows Panels0060.weights_checked ⟨5, by decide⟩
def b0061 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0061.block Panels0061.accepted Panels0061.integerPanels Panels0061.aligned
    Panels0061.weightRows Panels0061.weights_checked ⟨5, by decide⟩
def b0062 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0062.block Panels0062.accepted Panels0062.integerPanels Panels0062.aligned
    Panels0062.weightRows Panels0062.weights_checked ⟨5, by decide⟩
def b0063 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0063.block Panels0063.accepted Panels0063.integerPanels Panels0063.aligned
    Panels0063.weightRows Panels0063.weights_checked ⟨5, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0056, b0057, b0058, b0059, b0060, b0061, b0062, b0063]
theorem chain_checked : blockChainCheck (57247499418396570304717986552/10^30) (73505001431232948341390251911/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=3595336369421245859441654422142959815825486468694474533203493693641754800510172384455341111275646248566870756393801934312772635232685006500575435819500753842882852417263029860051735348351684919576059669515558/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row05
namespace Row06
abbrev ζ : ℚ := 46511627906976744186046511627/10^30
def b0056 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0056.block Panels0056.accepted Panels0056.integerPanels Panels0056.aligned
    Panels0056.weightRows Panels0056.weights_checked ⟨6, by decide⟩
def b0057 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0057.block Panels0057.accepted Panels0057.integerPanels Panels0057.aligned
    Panels0057.weightRows Panels0057.weights_checked ⟨6, by decide⟩
def b0058 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0058.block Panels0058.accepted Panels0058.integerPanels Panels0058.aligned
    Panels0058.weightRows Panels0058.weights_checked ⟨6, by decide⟩
def b0059 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0059.block Panels0059.accepted Panels0059.integerPanels Panels0059.aligned
    Panels0059.weightRows Panels0059.weights_checked ⟨6, by decide⟩
def b0060 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0060.block Panels0060.accepted Panels0060.integerPanels Panels0060.aligned
    Panels0060.weightRows Panels0060.weights_checked ⟨6, by decide⟩
def b0061 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0061.block Panels0061.accepted Panels0061.integerPanels Panels0061.aligned
    Panels0061.weightRows Panels0061.weights_checked ⟨6, by decide⟩
def b0062 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0062.block Panels0062.accepted Panels0062.integerPanels Panels0062.aligned
    Panels0062.weightRows Panels0062.weights_checked ⟨6, by decide⟩
def b0063 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0063.block Panels0063.accepted Panels0063.integerPanels Panels0063.aligned
    Panels0063.weightRows Panels0063.weights_checked ⟨6, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0056, b0057, b0058, b0059, b0060, b0061, b0062, b0063]
theorem chain_checked : blockChainCheck (57247499418396570304717986552/10^30) (73505001431232948341390251911/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=3407769567378572723545350618111821482726819549936946081636057390563728341142268917454569515944505860743691803177330063952664985238181430311488839512040397189565038638157908693843435270390333520950726250032164441/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row06
namespace Row07
abbrev ζ : ℚ := 33898305084745762711864406779/10^30
def b0056 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0056.block Panels0056.accepted Panels0056.integerPanels Panels0056.aligned
    Panels0056.weightRows Panels0056.weights_checked ⟨7, by decide⟩
def b0057 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0057.block Panels0057.accepted Panels0057.integerPanels Panels0057.aligned
    Panels0057.weightRows Panels0057.weights_checked ⟨7, by decide⟩
def b0058 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0058.block Panels0058.accepted Panels0058.integerPanels Panels0058.aligned
    Panels0058.weightRows Panels0058.weights_checked ⟨7, by decide⟩
def b0059 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0059.block Panels0059.accepted Panels0059.integerPanels Panels0059.aligned
    Panels0059.weightRows Panels0059.weights_checked ⟨7, by decide⟩
def b0060 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0060.block Panels0060.accepted Panels0060.integerPanels Panels0060.aligned
    Panels0060.weightRows Panels0060.weights_checked ⟨7, by decide⟩
def b0061 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0061.block Panels0061.accepted Panels0061.integerPanels Panels0061.aligned
    Panels0061.weightRows Panels0061.weights_checked ⟨7, by decide⟩
def b0062 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0062.block Panels0062.accepted Panels0062.integerPanels Panels0062.aligned
    Panels0062.weightRows Panels0062.weights_checked ⟨7, by decide⟩
def b0063 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0063.block Panels0063.accepted Panels0063.integerPanels Panels0063.aligned
    Panels0063.weightRows Panels0063.weights_checked ⟨7, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0056, b0057, b0058, b0059, b0060, b0061, b0062, b0063]
theorem chain_checked : blockChainCheck (57247499418396570304717986552/10^30) (73505001431232948341390251911/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=37506729820944551241694044464720981831953465666211124296212298753160748161637436796502360555778921554391555351019275909701924360110844180861785478959018803226687802468716873925054646722782044283224417017557728057/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row07
namespace Row08
abbrev ζ : ℚ := 25316455696202531645569620253/10^30
def b0056 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0056.block Panels0056.accepted Panels0056.integerPanels Panels0056.aligned
    Panels0056.weightRows Panels0056.weights_checked ⟨8, by decide⟩
def b0057 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0057.block Panels0057.accepted Panels0057.integerPanels Panels0057.aligned
    Panels0057.weightRows Panels0057.weights_checked ⟨8, by decide⟩
def b0058 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0058.block Panels0058.accepted Panels0058.integerPanels Panels0058.aligned
    Panels0058.weightRows Panels0058.weights_checked ⟨8, by decide⟩
def b0059 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0059.block Panels0059.accepted Panels0059.integerPanels Panels0059.aligned
    Panels0059.weightRows Panels0059.weights_checked ⟨8, by decide⟩
def b0060 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0060.block Panels0060.accepted Panels0060.integerPanels Panels0060.aligned
    Panels0060.weightRows Panels0060.weights_checked ⟨8, by decide⟩
def b0061 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0061.block Panels0061.accepted Panels0061.integerPanels Panels0061.aligned
    Panels0061.weightRows Panels0061.weights_checked ⟨8, by decide⟩
def b0062 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0062.block Panels0062.accepted Panels0062.integerPanels Panels0062.aligned
    Panels0062.weightRows Panels0062.weights_checked ⟨8, by decide⟩
def b0063 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0063.block Panels0063.accepted Panels0063.integerPanels Panels0063.aligned
    Panels0063.weightRows Panels0063.weights_checked ⟨8, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0056, b0057, b0058, b0059, b0060, b0061, b0062, b0063]
theorem chain_checked : blockChainCheck (57247499418396570304717986552/10^30) (73505001431232948341390251911/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=123174210700569167631193681325472738025005858242990276210357707879762470545611178246026215031445656403526692918911747977887844850332501057037134349454568038248664850482516439597237043820933670385495410908620027049/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row08
namespace Row09
abbrev ζ : ℚ := 18691588785046728971962616822/10^30
def b0056 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0056.block Panels0056.accepted Panels0056.integerPanels Panels0056.aligned
    Panels0056.weightRows Panels0056.weights_checked ⟨9, by decide⟩
def b0057 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0057.block Panels0057.accepted Panels0057.integerPanels Panels0057.aligned
    Panels0057.weightRows Panels0057.weights_checked ⟨9, by decide⟩
def b0058 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0058.block Panels0058.accepted Panels0058.integerPanels Panels0058.aligned
    Panels0058.weightRows Panels0058.weights_checked ⟨9, by decide⟩
def b0059 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0059.block Panels0059.accepted Panels0059.integerPanels Panels0059.aligned
    Panels0059.weightRows Panels0059.weights_checked ⟨9, by decide⟩
def b0060 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0060.block Panels0060.accepted Panels0060.integerPanels Panels0060.aligned
    Panels0060.weightRows Panels0060.weights_checked ⟨9, by decide⟩
def b0061 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0061.block Panels0061.accepted Panels0061.integerPanels Panels0061.aligned
    Panels0061.weightRows Panels0061.weights_checked ⟨9, by decide⟩
def b0062 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0062.block Panels0062.accepted Panels0062.integerPanels Panels0062.aligned
    Panels0062.weightRows Panels0062.weights_checked ⟨9, by decide⟩
def b0063 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0063.block Panels0063.accepted Panels0063.integerPanels Panels0063.aligned
    Panels0063.weightRows Panels0063.weights_checked ⟨9, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0056, b0057, b0058, b0059, b0060, b0061, b0062, b0063]
theorem chain_checked : blockChainCheck (57247499418396570304717986552/10^30) (73505001431232948341390251911/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=264617758724596234370227081140629556925830457938474725796964554658756327179364219837426558328639827326184784089905300936706584090083161827609484999682430269727641360748912951924509307132832815596853763805893258871/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row09
namespace Row10
abbrev ζ : ℚ := 13793103448275862068965517241/10^30
def b0056 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0056.block Panels0056.accepted Panels0056.integerPanels Panels0056.aligned
    Panels0056.weightRows Panels0056.weights_checked ⟨10, by decide⟩
def b0057 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0057.block Panels0057.accepted Panels0057.integerPanels Panels0057.aligned
    Panels0057.weightRows Panels0057.weights_checked ⟨10, by decide⟩
def b0058 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0058.block Panels0058.accepted Panels0058.integerPanels Panels0058.aligned
    Panels0058.weightRows Panels0058.weights_checked ⟨10, by decide⟩
def b0059 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0059.block Panels0059.accepted Panels0059.integerPanels Panels0059.aligned
    Panels0059.weightRows Panels0059.weights_checked ⟨10, by decide⟩
def b0060 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0060.block Panels0060.accepted Panels0060.integerPanels Panels0060.aligned
    Panels0060.weightRows Panels0060.weights_checked ⟨10, by decide⟩
def b0061 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0061.block Panels0061.accepted Panels0061.integerPanels Panels0061.aligned
    Panels0061.weightRows Panels0061.weights_checked ⟨10, by decide⟩
def b0062 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0062.block Panels0062.accepted Panels0062.integerPanels Panels0062.aligned
    Panels0062.weightRows Panels0062.weights_checked ⟨10, by decide⟩
def b0063 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0063.block Panels0063.accepted Panels0063.integerPanels Panels0063.aligned
    Panels0063.weightRows Panels0063.weights_checked ⟨10, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0056, b0057, b0058, b0059, b0060, b0061, b0062, b0063]
theorem chain_checked : blockChainCheck (57247499418396570304717986552/10^30) (73505001431232948341390251911/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=436778725893031615393317726705579195933170795227528746031591086998189291134107637558969153144087110208795193295050856345458075654489456808196126316256499352806918122052521098251073218551148515925562800279212775073/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row10
namespace Row11
abbrev ζ : ℚ := 10152284263959390862944162436/10^30
def b0056 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0056.block Panels0056.accepted Panels0056.integerPanels Panels0056.aligned
    Panels0056.weightRows Panels0056.weights_checked ⟨11, by decide⟩
def b0057 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0057.block Panels0057.accepted Panels0057.integerPanels Panels0057.aligned
    Panels0057.weightRows Panels0057.weights_checked ⟨11, by decide⟩
def b0058 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0058.block Panels0058.accepted Panels0058.integerPanels Panels0058.aligned
    Panels0058.weightRows Panels0058.weights_checked ⟨11, by decide⟩
def b0059 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0059.block Panels0059.accepted Panels0059.integerPanels Panels0059.aligned
    Panels0059.weightRows Panels0059.weights_checked ⟨11, by decide⟩
def b0060 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0060.block Panels0060.accepted Panels0060.integerPanels Panels0060.aligned
    Panels0060.weightRows Panels0060.weights_checked ⟨11, by decide⟩
def b0061 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0061.block Panels0061.accepted Panels0061.integerPanels Panels0061.aligned
    Panels0061.weightRows Panels0061.weights_checked ⟨11, by decide⟩
def b0062 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0062.block Panels0062.accepted Panels0062.integerPanels Panels0062.aligned
    Panels0062.weightRows Panels0062.weights_checked ⟨11, by decide⟩
def b0063 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0063.block Panels0063.accepted Panels0063.integerPanels Panels0063.aligned
    Panels0063.weightRows Panels0063.weights_checked ⟨11, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0056, b0057, b0058, b0059, b0060, b0061, b0062, b0063]
theorem chain_checked : blockChainCheck (57247499418396570304717986552/10^30) (73505001431232948341390251911/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=615727246129055967533651557797266381952090047799762200350348923872797699650503622311330099530252249268570363239389902805230796526909374033107588784556373200726591465509486859716739583635125891936152867173548296903/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row11
namespace Row12
abbrev ζ : ℚ := 9950248756218905472636815920/10^30
def b0056 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0056.block Panels0056.accepted Panels0056.integerPanels Panels0056.aligned
    Panels0056.weightRows Panels0056.weights_checked ⟨12, by decide⟩
def b0057 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0057.block Panels0057.accepted Panels0057.integerPanels Panels0057.aligned
    Panels0057.weightRows Panels0057.weights_checked ⟨12, by decide⟩
def b0058 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0058.block Panels0058.accepted Panels0058.integerPanels Panels0058.aligned
    Panels0058.weightRows Panels0058.weights_checked ⟨12, by decide⟩
def b0059 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0059.block Panels0059.accepted Panels0059.integerPanels Panels0059.aligned
    Panels0059.weightRows Panels0059.weights_checked ⟨12, by decide⟩
def b0060 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0060.block Panels0060.accepted Panels0060.integerPanels Panels0060.aligned
    Panels0060.weightRows Panels0060.weights_checked ⟨12, by decide⟩
def b0061 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0061.block Panels0061.accepted Panels0061.integerPanels Panels0061.aligned
    Panels0061.weightRows Panels0061.weights_checked ⟨12, by decide⟩
def b0062 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0062.block Panels0062.accepted Panels0062.integerPanels Panels0062.aligned
    Panels0062.weightRows Panels0062.weights_checked ⟨12, by decide⟩
def b0063 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0063.block Panels0063.accepted Panels0063.integerPanels Panels0063.aligned
    Panels0063.weightRows Panels0063.weights_checked ⟨12, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0056, b0057, b0058, b0059, b0060, b0061, b0062, b0063]
theorem chain_checked : blockChainCheck (57247499418396570304717986552/10^30) (73505001431232948341390251911/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=627162349699516738682042776102390388003813423860627855259312046154340556163921709382853951422666303932453379685075920818963294437820739056945662357862490737809185716897500402361659376785571220749695353579306433535/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row12
#print axioms Row12.segment
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments007
