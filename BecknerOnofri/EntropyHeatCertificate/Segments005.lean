module

public import BecknerOnofri.EntropyHeatCheckedWeights
public import BecknerOnofri.EntropyHeatSegments
public import BecknerOnofri.EntropyHeatCertificate.Panels0040
public import BecknerOnofri.EntropyHeatCertificate.Panels0041
public import BecknerOnofri.EntropyHeatCertificate.Panels0042
public import BecknerOnofri.EntropyHeatCertificate.Panels0043
public import BecknerOnofri.EntropyHeatCertificate.Panels0044
public import BecknerOnofri.EntropyHeatCertificate.Panels0045
public import BecknerOnofri.EntropyHeatCertificate.Panels0046
public import BecknerOnofri.EntropyHeatCertificate.Panels0047

@[expose] public section
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments005
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace Row00
abbrev ζ : ℚ := 285714285714285714285714285714/10^30
def b0040 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0040.block Panels0040.accepted Panels0040.integerPanels Panels0040.aligned
    Panels0040.weightRows Panels0040.weights_checked ⟨0, by decide⟩
def b0041 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0041.block Panels0041.accepted Panels0041.integerPanels Panels0041.aligned
    Panels0041.weightRows Panels0041.weights_checked ⟨0, by decide⟩
def b0042 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0042.block Panels0042.accepted Panels0042.integerPanels Panels0042.aligned
    Panels0042.weightRows Panels0042.weights_checked ⟨0, by decide⟩
def b0043 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0043.block Panels0043.accepted Panels0043.integerPanels Panels0043.aligned
    Panels0043.weightRows Panels0043.weights_checked ⟨0, by decide⟩
def b0044 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0044.block Panels0044.accepted Panels0044.integerPanels Panels0044.aligned
    Panels0044.weightRows Panels0044.weights_checked ⟨0, by decide⟩
def b0045 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0045.block Panels0045.accepted Panels0045.integerPanels Panels0045.aligned
    Panels0045.weightRows Panels0045.weights_checked ⟨0, by decide⟩
def b0046 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0046.block Panels0046.accepted Panels0046.integerPanels Panels0046.aligned
    Panels0046.weightRows Panels0046.weights_checked ⟨0, by decide⟩
def b0047 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0047.block Panels0047.accepted Panels0047.integerPanels Panels0047.aligned
    Panels0047.weightRows Panels0047.weights_checked ⟨0, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0040, b0041, b0042, b0043, b0044, b0045, b0046, b0047]
theorem chain_checked : blockChainCheck (34724482593808868107651770989/10^30) (44585757783099246165036576418/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row00
namespace Row01
abbrev ζ : ℚ := 222222222222222222222222222222/10^30
def b0040 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0040.block Panels0040.accepted Panels0040.integerPanels Panels0040.aligned
    Panels0040.weightRows Panels0040.weights_checked ⟨1, by decide⟩
def b0041 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0041.block Panels0041.accepted Panels0041.integerPanels Panels0041.aligned
    Panels0041.weightRows Panels0041.weights_checked ⟨1, by decide⟩
def b0042 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0042.block Panels0042.accepted Panels0042.integerPanels Panels0042.aligned
    Panels0042.weightRows Panels0042.weights_checked ⟨1, by decide⟩
def b0043 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0043.block Panels0043.accepted Panels0043.integerPanels Panels0043.aligned
    Panels0043.weightRows Panels0043.weights_checked ⟨1, by decide⟩
def b0044 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0044.block Panels0044.accepted Panels0044.integerPanels Panels0044.aligned
    Panels0044.weightRows Panels0044.weights_checked ⟨1, by decide⟩
def b0045 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0045.block Panels0045.accepted Panels0045.integerPanels Panels0045.aligned
    Panels0045.weightRows Panels0045.weights_checked ⟨1, by decide⟩
def b0046 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0046.block Panels0046.accepted Panels0046.integerPanels Panels0046.aligned
    Panels0046.weightRows Panels0046.weights_checked ⟨1, by decide⟩
def b0047 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0047.block Panels0047.accepted Panels0047.integerPanels Panels0047.aligned
    Panels0047.weightRows Panels0047.weights_checked ⟨1, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0040, b0041, b0042, b0043, b0044, b0045, b0046, b0047]
theorem chain_checked : blockChainCheck (34724482593808868107651770989/10^30) (44585757783099246165036576418/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row01
namespace Row02
abbrev ζ : ℚ := 153846153846153846153846153846/10^30
def b0040 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0040.block Panels0040.accepted Panels0040.integerPanels Panels0040.aligned
    Panels0040.weightRows Panels0040.weights_checked ⟨2, by decide⟩
def b0041 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0041.block Panels0041.accepted Panels0041.integerPanels Panels0041.aligned
    Panels0041.weightRows Panels0041.weights_checked ⟨2, by decide⟩
def b0042 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0042.block Panels0042.accepted Panels0042.integerPanels Panels0042.aligned
    Panels0042.weightRows Panels0042.weights_checked ⟨2, by decide⟩
def b0043 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0043.block Panels0043.accepted Panels0043.integerPanels Panels0043.aligned
    Panels0043.weightRows Panels0043.weights_checked ⟨2, by decide⟩
def b0044 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0044.block Panels0044.accepted Panels0044.integerPanels Panels0044.aligned
    Panels0044.weightRows Panels0044.weights_checked ⟨2, by decide⟩
def b0045 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0045.block Panels0045.accepted Panels0045.integerPanels Panels0045.aligned
    Panels0045.weightRows Panels0045.weights_checked ⟨2, by decide⟩
def b0046 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0046.block Panels0046.accepted Panels0046.integerPanels Panels0046.aligned
    Panels0046.weightRows Panels0046.weights_checked ⟨2, by decide⟩
def b0047 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0047.block Panels0047.accepted Panels0047.integerPanels Panels0047.aligned
    Panels0047.weightRows Panels0047.weights_checked ⟨2, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0040, b0041, b0042, b0043, b0044, b0045, b0046, b0047]
theorem chain_checked : blockChainCheck (34724482593808868107651770989/10^30) (44585757783099246165036576418/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row02
namespace Row03
abbrev ζ : ℚ := 117647058823529411764705882352/10^30
def b0040 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0040.block Panels0040.accepted Panels0040.integerPanels Panels0040.aligned
    Panels0040.weightRows Panels0040.weights_checked ⟨3, by decide⟩
def b0041 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0041.block Panels0041.accepted Panels0041.integerPanels Panels0041.aligned
    Panels0041.weightRows Panels0041.weights_checked ⟨3, by decide⟩
def b0042 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0042.block Panels0042.accepted Panels0042.integerPanels Panels0042.aligned
    Panels0042.weightRows Panels0042.weights_checked ⟨3, by decide⟩
def b0043 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0043.block Panels0043.accepted Panels0043.integerPanels Panels0043.aligned
    Panels0043.weightRows Panels0043.weights_checked ⟨3, by decide⟩
def b0044 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0044.block Panels0044.accepted Panels0044.integerPanels Panels0044.aligned
    Panels0044.weightRows Panels0044.weights_checked ⟨3, by decide⟩
def b0045 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0045.block Panels0045.accepted Panels0045.integerPanels Panels0045.aligned
    Panels0045.weightRows Panels0045.weights_checked ⟨3, by decide⟩
def b0046 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0046.block Panels0046.accepted Panels0046.integerPanels Panels0046.aligned
    Panels0046.weightRows Panels0046.weights_checked ⟨3, by decide⟩
def b0047 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0047.block Panels0047.accepted Panels0047.integerPanels Panels0047.aligned
    Panels0047.weightRows Panels0047.weights_checked ⟨3, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0040, b0041, b0042, b0043, b0044, b0045, b0046, b0047]
theorem chain_checked : blockChainCheck (34724482593808868107651770989/10^30) (44585757783099246165036576418/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row03
namespace Row04
abbrev ζ : ℚ := 86956521739130434782608695652/10^30
def b0040 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0040.block Panels0040.accepted Panels0040.integerPanels Panels0040.aligned
    Panels0040.weightRows Panels0040.weights_checked ⟨4, by decide⟩
def b0041 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0041.block Panels0041.accepted Panels0041.integerPanels Panels0041.aligned
    Panels0041.weightRows Panels0041.weights_checked ⟨4, by decide⟩
def b0042 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0042.block Panels0042.accepted Panels0042.integerPanels Panels0042.aligned
    Panels0042.weightRows Panels0042.weights_checked ⟨4, by decide⟩
def b0043 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0043.block Panels0043.accepted Panels0043.integerPanels Panels0043.aligned
    Panels0043.weightRows Panels0043.weights_checked ⟨4, by decide⟩
def b0044 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0044.block Panels0044.accepted Panels0044.integerPanels Panels0044.aligned
    Panels0044.weightRows Panels0044.weights_checked ⟨4, by decide⟩
def b0045 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0045.block Panels0045.accepted Panels0045.integerPanels Panels0045.aligned
    Panels0045.weightRows Panels0045.weights_checked ⟨4, by decide⟩
def b0046 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0046.block Panels0046.accepted Panels0046.integerPanels Panels0046.aligned
    Panels0046.weightRows Panels0046.weights_checked ⟨4, by decide⟩
def b0047 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0047.block Panels0047.accepted Panels0047.integerPanels Panels0047.aligned
    Panels0047.weightRows Panels0047.weights_checked ⟨4, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0040, b0041, b0042, b0043, b0044, b0045, b0046, b0047]
theorem chain_checked : blockChainCheck (34724482593808868107651770989/10^30) (44585757783099246165036576418/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row04
namespace Row05
abbrev ζ : ℚ := 64516129032258064516129032258/10^30
def b0040 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0040.block Panels0040.accepted Panels0040.integerPanels Panels0040.aligned
    Panels0040.weightRows Panels0040.weights_checked ⟨5, by decide⟩
def b0041 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0041.block Panels0041.accepted Panels0041.integerPanels Panels0041.aligned
    Panels0041.weightRows Panels0041.weights_checked ⟨5, by decide⟩
def b0042 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0042.block Panels0042.accepted Panels0042.integerPanels Panels0042.aligned
    Panels0042.weightRows Panels0042.weights_checked ⟨5, by decide⟩
def b0043 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0043.block Panels0043.accepted Panels0043.integerPanels Panels0043.aligned
    Panels0043.weightRows Panels0043.weights_checked ⟨5, by decide⟩
def b0044 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0044.block Panels0044.accepted Panels0044.integerPanels Panels0044.aligned
    Panels0044.weightRows Panels0044.weights_checked ⟨5, by decide⟩
def b0045 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0045.block Panels0045.accepted Panels0045.integerPanels Panels0045.aligned
    Panels0045.weightRows Panels0045.weights_checked ⟨5, by decide⟩
def b0046 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0046.block Panels0046.accepted Panels0046.integerPanels Panels0046.aligned
    Panels0046.weightRows Panels0046.weights_checked ⟨5, by decide⟩
def b0047 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0047.block Panels0047.accepted Panels0047.integerPanels Panels0047.aligned
    Panels0047.weightRows Panels0047.weights_checked ⟨5, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0040, b0041, b0042, b0043, b0044, b0045, b0046, b0047]
theorem chain_checked : blockChainCheck (34724482593808868107651770989/10^30) (44585757783099246165036576418/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row05
namespace Row06
abbrev ζ : ℚ := 46511627906976744186046511627/10^30
def b0040 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0040.block Panels0040.accepted Panels0040.integerPanels Panels0040.aligned
    Panels0040.weightRows Panels0040.weights_checked ⟨6, by decide⟩
def b0041 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0041.block Panels0041.accepted Panels0041.integerPanels Panels0041.aligned
    Panels0041.weightRows Panels0041.weights_checked ⟨6, by decide⟩
def b0042 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0042.block Panels0042.accepted Panels0042.integerPanels Panels0042.aligned
    Panels0042.weightRows Panels0042.weights_checked ⟨6, by decide⟩
def b0043 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0043.block Panels0043.accepted Panels0043.integerPanels Panels0043.aligned
    Panels0043.weightRows Panels0043.weights_checked ⟨6, by decide⟩
def b0044 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0044.block Panels0044.accepted Panels0044.integerPanels Panels0044.aligned
    Panels0044.weightRows Panels0044.weights_checked ⟨6, by decide⟩
def b0045 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0045.block Panels0045.accepted Panels0045.integerPanels Panels0045.aligned
    Panels0045.weightRows Panels0045.weights_checked ⟨6, by decide⟩
def b0046 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0046.block Panels0046.accepted Panels0046.integerPanels Panels0046.aligned
    Panels0046.weightRows Panels0046.weights_checked ⟨6, by decide⟩
def b0047 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0047.block Panels0047.accepted Panels0047.integerPanels Panels0047.aligned
    Panels0047.weightRows Panels0047.weights_checked ⟨6, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0040, b0041, b0042, b0043, b0044, b0045, b0046, b0047]
theorem chain_checked : blockChainCheck (34724482593808868107651770989/10^30) (44585757783099246165036576418/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row06
namespace Row07
abbrev ζ : ℚ := 33898305084745762711864406779/10^30
def b0040 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0040.block Panels0040.accepted Panels0040.integerPanels Panels0040.aligned
    Panels0040.weightRows Panels0040.weights_checked ⟨7, by decide⟩
def b0041 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0041.block Panels0041.accepted Panels0041.integerPanels Panels0041.aligned
    Panels0041.weightRows Panels0041.weights_checked ⟨7, by decide⟩
def b0042 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0042.block Panels0042.accepted Panels0042.integerPanels Panels0042.aligned
    Panels0042.weightRows Panels0042.weights_checked ⟨7, by decide⟩
def b0043 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0043.block Panels0043.accepted Panels0043.integerPanels Panels0043.aligned
    Panels0043.weightRows Panels0043.weights_checked ⟨7, by decide⟩
def b0044 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0044.block Panels0044.accepted Panels0044.integerPanels Panels0044.aligned
    Panels0044.weightRows Panels0044.weights_checked ⟨7, by decide⟩
def b0045 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0045.block Panels0045.accepted Panels0045.integerPanels Panels0045.aligned
    Panels0045.weightRows Panels0045.weights_checked ⟨7, by decide⟩
def b0046 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0046.block Panels0046.accepted Panels0046.integerPanels Panels0046.aligned
    Panels0046.weightRows Panels0046.weights_checked ⟨7, by decide⟩
def b0047 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0047.block Panels0047.accepted Panels0047.integerPanels Panels0047.aligned
    Panels0047.weightRows Panels0047.weights_checked ⟨7, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0040, b0041, b0042, b0043, b0044, b0045, b0046, b0047]
theorem chain_checked : blockChainCheck (34724482593808868107651770989/10^30) (44585757783099246165036576418/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=230011185084041342538214053075502000325360539496872257433347008696016218150527907308115261670544990209860021596931233301773971601951510366792036031629695822871549391273264473594191908274368452063324093739028602/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row07
namespace Row08
abbrev ζ : ℚ := 25316455696202531645569620253/10^30
def b0040 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0040.block Panels0040.accepted Panels0040.integerPanels Panels0040.aligned
    Panels0040.weightRows Panels0040.weights_checked ⟨8, by decide⟩
def b0041 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0041.block Panels0041.accepted Panels0041.integerPanels Panels0041.aligned
    Panels0041.weightRows Panels0041.weights_checked ⟨8, by decide⟩
def b0042 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0042.block Panels0042.accepted Panels0042.integerPanels Panels0042.aligned
    Panels0042.weightRows Panels0042.weights_checked ⟨8, by decide⟩
def b0043 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0043.block Panels0043.accepted Panels0043.integerPanels Panels0043.aligned
    Panels0043.weightRows Panels0043.weights_checked ⟨8, by decide⟩
def b0044 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0044.block Panels0044.accepted Panels0044.integerPanels Panels0044.aligned
    Panels0044.weightRows Panels0044.weights_checked ⟨8, by decide⟩
def b0045 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0045.block Panels0045.accepted Panels0045.integerPanels Panels0045.aligned
    Panels0045.weightRows Panels0045.weights_checked ⟨8, by decide⟩
def b0046 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0046.block Panels0046.accepted Panels0046.integerPanels Panels0046.aligned
    Panels0046.weightRows Panels0046.weights_checked ⟨8, by decide⟩
def b0047 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0047.block Panels0047.accepted Panels0047.integerPanels Panels0047.aligned
    Panels0047.weightRows Panels0047.weights_checked ⟨8, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0040, b0041, b0042, b0043, b0044, b0045, b0046, b0047]
theorem chain_checked : blockChainCheck (34724482593808868107651770989/10^30) (44585757783099246165036576418/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=9528087129128406885076870473165977350541035147627163300360035629758793655279837958342079497812907680314789387030350041368470411822066945348190197415498945611445792501721401818714786135091177035084076291284627090/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row08
namespace Row09
abbrev ζ : ℚ := 18691588785046728971962616822/10^30
def b0040 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0040.block Panels0040.accepted Panels0040.integerPanels Panels0040.aligned
    Panels0040.weightRows Panels0040.weights_checked ⟨9, by decide⟩
def b0041 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0041.block Panels0041.accepted Panels0041.integerPanels Panels0041.aligned
    Panels0041.weightRows Panels0041.weights_checked ⟨9, by decide⟩
def b0042 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0042.block Panels0042.accepted Panels0042.integerPanels Panels0042.aligned
    Panels0042.weightRows Panels0042.weights_checked ⟨9, by decide⟩
def b0043 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0043.block Panels0043.accepted Panels0043.integerPanels Panels0043.aligned
    Panels0043.weightRows Panels0043.weights_checked ⟨9, by decide⟩
def b0044 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0044.block Panels0044.accepted Panels0044.integerPanels Panels0044.aligned
    Panels0044.weightRows Panels0044.weights_checked ⟨9, by decide⟩
def b0045 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0045.block Panels0045.accepted Panels0045.integerPanels Panels0045.aligned
    Panels0045.weightRows Panels0045.weights_checked ⟨9, by decide⟩
def b0046 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0046.block Panels0046.accepted Panels0046.integerPanels Panels0046.aligned
    Panels0046.weightRows Panels0046.weights_checked ⟨9, by decide⟩
def b0047 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0047.block Panels0047.accepted Panels0047.integerPanels Panels0047.aligned
    Panels0047.weightRows Panels0047.weights_checked ⟨9, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0040, b0041, b0042, b0043, b0044, b0045, b0046, b0047]
theorem chain_checked : blockChainCheck (34724482593808868107651770989/10^30) (44585757783099246165036576418/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=59295212900176480289579268867387345278123810821550042742843080873296622852737077159843374710083309333255437908228765371404341869559726480821432720366898632662681212538144862444895399701664787569189722467691527838/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row09
namespace Row10
abbrev ζ : ℚ := 13793103448275862068965517241/10^30
def b0040 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0040.block Panels0040.accepted Panels0040.integerPanels Panels0040.aligned
    Panels0040.weightRows Panels0040.weights_checked ⟨10, by decide⟩
def b0041 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0041.block Panels0041.accepted Panels0041.integerPanels Panels0041.aligned
    Panels0041.weightRows Panels0041.weights_checked ⟨10, by decide⟩
def b0042 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0042.block Panels0042.accepted Panels0042.integerPanels Panels0042.aligned
    Panels0042.weightRows Panels0042.weights_checked ⟨10, by decide⟩
def b0043 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0043.block Panels0043.accepted Panels0043.integerPanels Panels0043.aligned
    Panels0043.weightRows Panels0043.weights_checked ⟨10, by decide⟩
def b0044 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0044.block Panels0044.accepted Panels0044.integerPanels Panels0044.aligned
    Panels0044.weightRows Panels0044.weights_checked ⟨10, by decide⟩
def b0045 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0045.block Panels0045.accepted Panels0045.integerPanels Panels0045.aligned
    Panels0045.weightRows Panels0045.weights_checked ⟨10, by decide⟩
def b0046 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0046.block Panels0046.accepted Panels0046.integerPanels Panels0046.aligned
    Panels0046.weightRows Panels0046.weights_checked ⟨10, by decide⟩
def b0047 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0047.block Panels0047.accepted Panels0047.integerPanels Panels0047.aligned
    Panels0047.weightRows Panels0047.weights_checked ⟨10, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0040, b0041, b0042, b0043, b0044, b0045, b0046, b0047]
theorem chain_checked : blockChainCheck (34724482593808868107651770989/10^30) (44585757783099246165036576418/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=168077365426449577282845572933104398172523901924391445905351361836193725461940602295505775540318064177037779255236783229043808386521845341799449933800182713363916811149613510439848688821517006957317109220075860306/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row10
namespace Row11
abbrev ζ : ℚ := 10152284263959390862944162436/10^30
def b0040 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0040.block Panels0040.accepted Panels0040.integerPanels Panels0040.aligned
    Panels0040.weightRows Panels0040.weights_checked ⟨11, by decide⟩
def b0041 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0041.block Panels0041.accepted Panels0041.integerPanels Panels0041.aligned
    Panels0041.weightRows Panels0041.weights_checked ⟨11, by decide⟩
def b0042 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0042.block Panels0042.accepted Panels0042.integerPanels Panels0042.aligned
    Panels0042.weightRows Panels0042.weights_checked ⟨11, by decide⟩
def b0043 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0043.block Panels0043.accepted Panels0043.integerPanels Panels0043.aligned
    Panels0043.weightRows Panels0043.weights_checked ⟨11, by decide⟩
def b0044 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0044.block Panels0044.accepted Panels0044.integerPanels Panels0044.aligned
    Panels0044.weightRows Panels0044.weights_checked ⟨11, by decide⟩
def b0045 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0045.block Panels0045.accepted Panels0045.integerPanels Panels0045.aligned
    Panels0045.weightRows Panels0045.weights_checked ⟨11, by decide⟩
def b0046 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0046.block Panels0046.accepted Panels0046.integerPanels Panels0046.aligned
    Panels0046.weightRows Panels0046.weights_checked ⟨11, by decide⟩
def b0047 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0047.block Panels0047.accepted Panels0047.integerPanels Panels0047.aligned
    Panels0047.weightRows Panels0047.weights_checked ⟨11, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0040, b0041, b0042, b0043, b0044, b0045, b0046, b0047]
theorem chain_checked : blockChainCheck (34724482593808868107651770989/10^30) (44585757783099246165036576418/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=325083575947373130030694651326335753545597181923767485723138004133204420209591872109609470328068924651183177760191583714883522763537851116737988258817881800739852606949563657276420150057555659670925848539021816126/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row11
namespace Row12
abbrev ζ : ℚ := 9950248756218905472636815920/10^30
def b0040 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0040.block Panels0040.accepted Panels0040.integerPanels Panels0040.aligned
    Panels0040.weightRows Panels0040.weights_checked ⟨12, by decide⟩
def b0041 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0041.block Panels0041.accepted Panels0041.integerPanels Panels0041.aligned
    Panels0041.weightRows Panels0041.weights_checked ⟨12, by decide⟩
def b0042 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0042.block Panels0042.accepted Panels0042.integerPanels Panels0042.aligned
    Panels0042.weightRows Panels0042.weights_checked ⟨12, by decide⟩
def b0043 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0043.block Panels0043.accepted Panels0043.integerPanels Panels0043.aligned
    Panels0043.weightRows Panels0043.weights_checked ⟨12, by decide⟩
def b0044 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0044.block Panels0044.accepted Panels0044.integerPanels Panels0044.aligned
    Panels0044.weightRows Panels0044.weights_checked ⟨12, by decide⟩
def b0045 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0045.block Panels0045.accepted Panels0045.integerPanels Panels0045.aligned
    Panels0045.weightRows Panels0045.weights_checked ⟨12, by decide⟩
def b0046 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0046.block Panels0046.accepted Panels0046.integerPanels Panels0046.aligned
    Panels0046.weightRows Panels0046.weights_checked ⟨12, by decide⟩
def b0047 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0047.block Panels0047.accepted Panels0047.integerPanels Panels0047.aligned
    Panels0047.weightRows Panels0047.weights_checked ⟨12, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0040, b0041, b0042, b0043, b0044, b0045, b0046, b0047]
theorem chain_checked : blockChainCheck (34724482593808868107651770989/10^30) (44585757783099246165036576418/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=336417964348312571089171540219937464655511725962874969771146671606423488341650384487243868330514451343661444817788553025333094861376760915498920911420587882726747356130477502433345211215110643121543007514991436014/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row12
#print axioms Row12.segment
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments005
