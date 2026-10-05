module

public import BecknerOnofri.EntropyHeatCheckedWeights
public import BecknerOnofri.EntropyHeatSegments
public import BecknerOnofri.EntropyHeatCertificate.Panels0048
public import BecknerOnofri.EntropyHeatCertificate.Panels0049
public import BecknerOnofri.EntropyHeatCertificate.Panels0050
public import BecknerOnofri.EntropyHeatCertificate.Panels0051
public import BecknerOnofri.EntropyHeatCertificate.Panels0052
public import BecknerOnofri.EntropyHeatCertificate.Panels0053
public import BecknerOnofri.EntropyHeatCertificate.Panels0054
public import BecknerOnofri.EntropyHeatCertificate.Panels0055

@[expose] public section
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments006
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace Row00
abbrev ζ : ℚ := 285714285714285714285714285714/10^30
def b0048 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0048.block Panels0048.accepted Panels0048.integerPanels Panels0048.aligned
    Panels0048.weightRows Panels0048.weights_checked ⟨0, by decide⟩
def b0049 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0049.block Panels0049.accepted Panels0049.integerPanels Panels0049.aligned
    Panels0049.weightRows Panels0049.weights_checked ⟨0, by decide⟩
def b0050 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0050.block Panels0050.accepted Panels0050.integerPanels Panels0050.aligned
    Panels0050.weightRows Panels0050.weights_checked ⟨0, by decide⟩
def b0051 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0051.block Panels0051.accepted Panels0051.integerPanels Panels0051.aligned
    Panels0051.weightRows Panels0051.weights_checked ⟨0, by decide⟩
def b0052 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0052.block Panels0052.accepted Panels0052.integerPanels Panels0052.aligned
    Panels0052.weightRows Panels0052.weights_checked ⟨0, by decide⟩
def b0053 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0053.block Panels0053.accepted Panels0053.integerPanels Panels0053.aligned
    Panels0053.weightRows Panels0053.weights_checked ⟨0, by decide⟩
def b0054 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0054.block Panels0054.accepted Panels0054.integerPanels Panels0054.aligned
    Panels0054.weightRows Panels0054.weights_checked ⟨0, by decide⟩
def b0055 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0055.block Panels0055.accepted Panels0055.integerPanels Panels0055.aligned
    Panels0055.weightRows Panels0055.weights_checked ⟨0, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0048, b0049, b0050, b0051, b0052, b0053, b0054, b0055]
theorem chain_checked : blockChainCheck (44585757783099246165036576418/10^30) (57247499418396570304717986552/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row00
namespace Row01
abbrev ζ : ℚ := 222222222222222222222222222222/10^30
def b0048 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0048.block Panels0048.accepted Panels0048.integerPanels Panels0048.aligned
    Panels0048.weightRows Panels0048.weights_checked ⟨1, by decide⟩
def b0049 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0049.block Panels0049.accepted Panels0049.integerPanels Panels0049.aligned
    Panels0049.weightRows Panels0049.weights_checked ⟨1, by decide⟩
def b0050 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0050.block Panels0050.accepted Panels0050.integerPanels Panels0050.aligned
    Panels0050.weightRows Panels0050.weights_checked ⟨1, by decide⟩
def b0051 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0051.block Panels0051.accepted Panels0051.integerPanels Panels0051.aligned
    Panels0051.weightRows Panels0051.weights_checked ⟨1, by decide⟩
def b0052 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0052.block Panels0052.accepted Panels0052.integerPanels Panels0052.aligned
    Panels0052.weightRows Panels0052.weights_checked ⟨1, by decide⟩
def b0053 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0053.block Panels0053.accepted Panels0053.integerPanels Panels0053.aligned
    Panels0053.weightRows Panels0053.weights_checked ⟨1, by decide⟩
def b0054 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0054.block Panels0054.accepted Panels0054.integerPanels Panels0054.aligned
    Panels0054.weightRows Panels0054.weights_checked ⟨1, by decide⟩
def b0055 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0055.block Panels0055.accepted Panels0055.integerPanels Panels0055.aligned
    Panels0055.weightRows Panels0055.weights_checked ⟨1, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0048, b0049, b0050, b0051, b0052, b0053, b0054, b0055]
theorem chain_checked : blockChainCheck (44585757783099246165036576418/10^30) (57247499418396570304717986552/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row01
namespace Row02
abbrev ζ : ℚ := 153846153846153846153846153846/10^30
def b0048 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0048.block Panels0048.accepted Panels0048.integerPanels Panels0048.aligned
    Panels0048.weightRows Panels0048.weights_checked ⟨2, by decide⟩
def b0049 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0049.block Panels0049.accepted Panels0049.integerPanels Panels0049.aligned
    Panels0049.weightRows Panels0049.weights_checked ⟨2, by decide⟩
def b0050 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0050.block Panels0050.accepted Panels0050.integerPanels Panels0050.aligned
    Panels0050.weightRows Panels0050.weights_checked ⟨2, by decide⟩
def b0051 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0051.block Panels0051.accepted Panels0051.integerPanels Panels0051.aligned
    Panels0051.weightRows Panels0051.weights_checked ⟨2, by decide⟩
def b0052 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0052.block Panels0052.accepted Panels0052.integerPanels Panels0052.aligned
    Panels0052.weightRows Panels0052.weights_checked ⟨2, by decide⟩
def b0053 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0053.block Panels0053.accepted Panels0053.integerPanels Panels0053.aligned
    Panels0053.weightRows Panels0053.weights_checked ⟨2, by decide⟩
def b0054 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0054.block Panels0054.accepted Panels0054.integerPanels Panels0054.aligned
    Panels0054.weightRows Panels0054.weights_checked ⟨2, by decide⟩
def b0055 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0055.block Panels0055.accepted Panels0055.integerPanels Panels0055.aligned
    Panels0055.weightRows Panels0055.weights_checked ⟨2, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0048, b0049, b0050, b0051, b0052, b0053, b0054, b0055]
theorem chain_checked : blockChainCheck (44585757783099246165036576418/10^30) (57247499418396570304717986552/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row02
namespace Row03
abbrev ζ : ℚ := 117647058823529411764705882352/10^30
def b0048 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0048.block Panels0048.accepted Panels0048.integerPanels Panels0048.aligned
    Panels0048.weightRows Panels0048.weights_checked ⟨3, by decide⟩
def b0049 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0049.block Panels0049.accepted Panels0049.integerPanels Panels0049.aligned
    Panels0049.weightRows Panels0049.weights_checked ⟨3, by decide⟩
def b0050 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0050.block Panels0050.accepted Panels0050.integerPanels Panels0050.aligned
    Panels0050.weightRows Panels0050.weights_checked ⟨3, by decide⟩
def b0051 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0051.block Panels0051.accepted Panels0051.integerPanels Panels0051.aligned
    Panels0051.weightRows Panels0051.weights_checked ⟨3, by decide⟩
def b0052 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0052.block Panels0052.accepted Panels0052.integerPanels Panels0052.aligned
    Panels0052.weightRows Panels0052.weights_checked ⟨3, by decide⟩
def b0053 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0053.block Panels0053.accepted Panels0053.integerPanels Panels0053.aligned
    Panels0053.weightRows Panels0053.weights_checked ⟨3, by decide⟩
def b0054 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0054.block Panels0054.accepted Panels0054.integerPanels Panels0054.aligned
    Panels0054.weightRows Panels0054.weights_checked ⟨3, by decide⟩
def b0055 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0055.block Panels0055.accepted Panels0055.integerPanels Panels0055.aligned
    Panels0055.weightRows Panels0055.weights_checked ⟨3, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0048, b0049, b0050, b0051, b0052, b0053, b0054, b0055]
theorem chain_checked : blockChainCheck (44585757783099246165036576418/10^30) (57247499418396570304717986552/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row03
namespace Row04
abbrev ζ : ℚ := 86956521739130434782608695652/10^30
def b0048 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0048.block Panels0048.accepted Panels0048.integerPanels Panels0048.aligned
    Panels0048.weightRows Panels0048.weights_checked ⟨4, by decide⟩
def b0049 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0049.block Panels0049.accepted Panels0049.integerPanels Panels0049.aligned
    Panels0049.weightRows Panels0049.weights_checked ⟨4, by decide⟩
def b0050 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0050.block Panels0050.accepted Panels0050.integerPanels Panels0050.aligned
    Panels0050.weightRows Panels0050.weights_checked ⟨4, by decide⟩
def b0051 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0051.block Panels0051.accepted Panels0051.integerPanels Panels0051.aligned
    Panels0051.weightRows Panels0051.weights_checked ⟨4, by decide⟩
def b0052 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0052.block Panels0052.accepted Panels0052.integerPanels Panels0052.aligned
    Panels0052.weightRows Panels0052.weights_checked ⟨4, by decide⟩
def b0053 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0053.block Panels0053.accepted Panels0053.integerPanels Panels0053.aligned
    Panels0053.weightRows Panels0053.weights_checked ⟨4, by decide⟩
def b0054 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0054.block Panels0054.accepted Panels0054.integerPanels Panels0054.aligned
    Panels0054.weightRows Panels0054.weights_checked ⟨4, by decide⟩
def b0055 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0055.block Panels0055.accepted Panels0055.integerPanels Panels0055.aligned
    Panels0055.weightRows Panels0055.weights_checked ⟨4, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0048, b0049, b0050, b0051, b0052, b0053, b0054, b0055]
theorem chain_checked : blockChainCheck (44585757783099246165036576418/10^30) (57247499418396570304717986552/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row04
namespace Row05
abbrev ζ : ℚ := 64516129032258064516129032258/10^30
def b0048 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0048.block Panels0048.accepted Panels0048.integerPanels Panels0048.aligned
    Panels0048.weightRows Panels0048.weights_checked ⟨5, by decide⟩
def b0049 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0049.block Panels0049.accepted Panels0049.integerPanels Panels0049.aligned
    Panels0049.weightRows Panels0049.weights_checked ⟨5, by decide⟩
def b0050 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0050.block Panels0050.accepted Panels0050.integerPanels Panels0050.aligned
    Panels0050.weightRows Panels0050.weights_checked ⟨5, by decide⟩
def b0051 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0051.block Panels0051.accepted Panels0051.integerPanels Panels0051.aligned
    Panels0051.weightRows Panels0051.weights_checked ⟨5, by decide⟩
def b0052 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0052.block Panels0052.accepted Panels0052.integerPanels Panels0052.aligned
    Panels0052.weightRows Panels0052.weights_checked ⟨5, by decide⟩
def b0053 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0053.block Panels0053.accepted Panels0053.integerPanels Panels0053.aligned
    Panels0053.weightRows Panels0053.weights_checked ⟨5, by decide⟩
def b0054 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0054.block Panels0054.accepted Panels0054.integerPanels Panels0054.aligned
    Panels0054.weightRows Panels0054.weights_checked ⟨5, by decide⟩
def b0055 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0055.block Panels0055.accepted Panels0055.integerPanels Panels0055.aligned
    Panels0055.weightRows Panels0055.weights_checked ⟨5, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0048, b0049, b0050, b0051, b0052, b0053, b0054, b0055]
theorem chain_checked : blockChainCheck (44585757783099246165036576418/10^30) (57247499418396570304717986552/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row05
namespace Row06
abbrev ζ : ℚ := 46511627906976744186046511627/10^30
def b0048 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0048.block Panels0048.accepted Panels0048.integerPanels Panels0048.aligned
    Panels0048.weightRows Panels0048.weights_checked ⟨6, by decide⟩
def b0049 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0049.block Panels0049.accepted Panels0049.integerPanels Panels0049.aligned
    Panels0049.weightRows Panels0049.weights_checked ⟨6, by decide⟩
def b0050 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0050.block Panels0050.accepted Panels0050.integerPanels Panels0050.aligned
    Panels0050.weightRows Panels0050.weights_checked ⟨6, by decide⟩
def b0051 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0051.block Panels0051.accepted Panels0051.integerPanels Panels0051.aligned
    Panels0051.weightRows Panels0051.weights_checked ⟨6, by decide⟩
def b0052 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0052.block Panels0052.accepted Panels0052.integerPanels Panels0052.aligned
    Panels0052.weightRows Panels0052.weights_checked ⟨6, by decide⟩
def b0053 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0053.block Panels0053.accepted Panels0053.integerPanels Panels0053.aligned
    Panels0053.weightRows Panels0053.weights_checked ⟨6, by decide⟩
def b0054 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0054.block Panels0054.accepted Panels0054.integerPanels Panels0054.aligned
    Panels0054.weightRows Panels0054.weights_checked ⟨6, by decide⟩
def b0055 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0055.block Panels0055.accepted Panels0055.integerPanels Panels0055.aligned
    Panels0055.weightRows Panels0055.weights_checked ⟨6, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0048, b0049, b0050, b0051, b0052, b0053, b0054, b0055]
theorem chain_checked : blockChainCheck (44585757783099246165036576418/10^30) (57247499418396570304717986552/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=49902731906572207583435930399480991415773748134997923401136781717202340090386792779219720005827033597639088953175793328196098428423312388551873970584709427500605180112058838428196997721730033908820442224344980/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row06
namespace Row07
abbrev ζ : ℚ := 33898305084745762711864406779/10^30
def b0048 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0048.block Panels0048.accepted Panels0048.integerPanels Panels0048.aligned
    Panels0048.weightRows Panels0048.weights_checked ⟨7, by decide⟩
def b0049 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0049.block Panels0049.accepted Panels0049.integerPanels Panels0049.aligned
    Panels0049.weightRows Panels0049.weights_checked ⟨7, by decide⟩
def b0050 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0050.block Panels0050.accepted Panels0050.integerPanels Panels0050.aligned
    Panels0050.weightRows Panels0050.weights_checked ⟨7, by decide⟩
def b0051 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0051.block Panels0051.accepted Panels0051.integerPanels Panels0051.aligned
    Panels0051.weightRows Panels0051.weights_checked ⟨7, by decide⟩
def b0052 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0052.block Panels0052.accepted Panels0052.integerPanels Panels0052.aligned
    Panels0052.weightRows Panels0052.weights_checked ⟨7, by decide⟩
def b0053 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0053.block Panels0053.accepted Panels0053.integerPanels Panels0053.aligned
    Panels0053.weightRows Panels0053.weights_checked ⟨7, by decide⟩
def b0054 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0054.block Panels0054.accepted Panels0054.integerPanels Panels0054.aligned
    Panels0054.weightRows Panels0054.weights_checked ⟨7, by decide⟩
def b0055 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0055.block Panels0055.accepted Panels0055.integerPanels Panels0055.aligned
    Panels0055.weightRows Panels0055.weights_checked ⟨7, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0048, b0049, b0050, b0051, b0052, b0053, b0054, b0055]
theorem chain_checked : blockChainCheck (44585757783099246165036576418/10^30) (57247499418396570304717986552/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=6617474217566297922443215323616215660001930210261243460734310828452375685985334698393210212634685927867771767948390280481353107235167692212201230724595779746696214966162297816893508045255181508300634127872953890/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row07
namespace Row08
abbrev ζ : ℚ := 25316455696202531645569620253/10^30
def b0048 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0048.block Panels0048.accepted Panels0048.integerPanels Panels0048.aligned
    Panels0048.weightRows Panels0048.weights_checked ⟨8, by decide⟩
def b0049 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0049.block Panels0049.accepted Panels0049.integerPanels Panels0049.aligned
    Panels0049.weightRows Panels0049.weights_checked ⟨8, by decide⟩
def b0050 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0050.block Panels0050.accepted Panels0050.integerPanels Panels0050.aligned
    Panels0050.weightRows Panels0050.weights_checked ⟨8, by decide⟩
def b0051 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0051.block Panels0051.accepted Panels0051.integerPanels Panels0051.aligned
    Panels0051.weightRows Panels0051.weights_checked ⟨8, by decide⟩
def b0052 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0052.block Panels0052.accepted Panels0052.integerPanels Panels0052.aligned
    Panels0052.weightRows Panels0052.weights_checked ⟨8, by decide⟩
def b0053 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0053.block Panels0053.accepted Panels0053.integerPanels Panels0053.aligned
    Panels0053.weightRows Panels0053.weights_checked ⟨8, by decide⟩
def b0054 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0054.block Panels0054.accepted Panels0054.integerPanels Panels0054.aligned
    Panels0054.weightRows Panels0054.weights_checked ⟨8, by decide⟩
def b0055 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0055.block Panels0055.accepted Panels0055.integerPanels Panels0055.aligned
    Panels0055.weightRows Panels0055.weights_checked ⟨8, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0048, b0049, b0050, b0051, b0052, b0053, b0054, b0055]
theorem chain_checked : blockChainCheck (44585757783099246165036576418/10^30) (57247499418396570304717986552/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=46347397668550219616617383983380087925663880676693433237461866312950066882150355505376636965136211387004298076753543776486062328854521656913792135909627726247769192487021072202997781488151837507007725763154897978/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row08
namespace Row09
abbrev ζ : ℚ := 18691588785046728971962616822/10^30
def b0048 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0048.block Panels0048.accepted Panels0048.integerPanels Panels0048.aligned
    Panels0048.weightRows Panels0048.weights_checked ⟨9, by decide⟩
def b0049 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0049.block Panels0049.accepted Panels0049.integerPanels Panels0049.aligned
    Panels0049.weightRows Panels0049.weights_checked ⟨9, by decide⟩
def b0050 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0050.block Panels0050.accepted Panels0050.integerPanels Panels0050.aligned
    Panels0050.weightRows Panels0050.weights_checked ⟨9, by decide⟩
def b0051 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0051.block Panels0051.accepted Panels0051.integerPanels Panels0051.aligned
    Panels0051.weightRows Panels0051.weights_checked ⟨9, by decide⟩
def b0052 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0052.block Panels0052.accepted Panels0052.integerPanels Panels0052.aligned
    Panels0052.weightRows Panels0052.weights_checked ⟨9, by decide⟩
def b0053 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0053.block Panels0053.accepted Panels0053.integerPanels Panels0053.aligned
    Panels0053.weightRows Panels0053.weights_checked ⟨9, by decide⟩
def b0054 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0054.block Panels0054.accepted Panels0054.integerPanels Panels0054.aligned
    Panels0054.weightRows Panels0054.weights_checked ⟨9, by decide⟩
def b0055 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0055.block Panels0055.accepted Panels0055.integerPanels Panels0055.aligned
    Panels0055.weightRows Panels0055.weights_checked ⟨9, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0048, b0049, b0050, b0051, b0052, b0053, b0054, b0055]
theorem chain_checked : blockChainCheck (44585757783099246165036576418/10^30) (57247499418396570304717986552/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=144707987369691450044723525389355479055486999089266135762228531084032537628265529705016010367403227380771379557860179362542365036785517945746367245616115246686279852655489848590005380162870478673527624521828920806/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row09
namespace Row10
abbrev ζ : ℚ := 13793103448275862068965517241/10^30
def b0048 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0048.block Panels0048.accepted Panels0048.integerPanels Panels0048.aligned
    Panels0048.weightRows Panels0048.weights_checked ⟨10, by decide⟩
def b0049 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0049.block Panels0049.accepted Panels0049.integerPanels Panels0049.aligned
    Panels0049.weightRows Panels0049.weights_checked ⟨10, by decide⟩
def b0050 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0050.block Panels0050.accepted Panels0050.integerPanels Panels0050.aligned
    Panels0050.weightRows Panels0050.weights_checked ⟨10, by decide⟩
def b0051 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0051.block Panels0051.accepted Panels0051.integerPanels Panels0051.aligned
    Panels0051.weightRows Panels0051.weights_checked ⟨10, by decide⟩
def b0052 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0052.block Panels0052.accepted Panels0052.integerPanels Panels0052.aligned
    Panels0052.weightRows Panels0052.weights_checked ⟨10, by decide⟩
def b0053 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0053.block Panels0053.accepted Panels0053.integerPanels Panels0053.aligned
    Panels0053.weightRows Panels0053.weights_checked ⟨10, by decide⟩
def b0054 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0054.block Panels0054.accepted Panels0054.integerPanels Panels0054.aligned
    Panels0054.weightRows Panels0054.weights_checked ⟨10, by decide⟩
def b0055 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0055.block Panels0055.accepted Panels0055.integerPanels Panels0055.aligned
    Panels0055.weightRows Panels0055.weights_checked ⟨10, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0048, b0049, b0050, b0051, b0052, b0053, b0054, b0055]
theorem chain_checked : blockChainCheck (44585757783099246165036576418/10^30) (57247499418396570304717986552/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=293729320330341211339612419348125692172525468912653669015116157085801772668139321801382822346856370412677481856244679714920277486914795400980240223033276519120792634491920687535664540708668262450250048003613108474/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row10
namespace Row11
abbrev ζ : ℚ := 10152284263959390862944162436/10^30
def b0048 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0048.block Panels0048.accepted Panels0048.integerPanels Panels0048.aligned
    Panels0048.weightRows Panels0048.weights_checked ⟨11, by decide⟩
def b0049 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0049.block Panels0049.accepted Panels0049.integerPanels Panels0049.aligned
    Panels0049.weightRows Panels0049.weights_checked ⟨11, by decide⟩
def b0050 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0050.block Panels0050.accepted Panels0050.integerPanels Panels0050.aligned
    Panels0050.weightRows Panels0050.weights_checked ⟨11, by decide⟩
def b0051 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0051.block Panels0051.accepted Panels0051.integerPanels Panels0051.aligned
    Panels0051.weightRows Panels0051.weights_checked ⟨11, by decide⟩
def b0052 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0052.block Panels0052.accepted Panels0052.integerPanels Panels0052.aligned
    Panels0052.weightRows Panels0052.weights_checked ⟨11, by decide⟩
def b0053 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0053.block Panels0053.accepted Panels0053.integerPanels Panels0053.aligned
    Panels0053.weightRows Panels0053.weights_checked ⟨11, by decide⟩
def b0054 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0054.block Panels0054.accepted Panels0054.integerPanels Panels0054.aligned
    Panels0054.weightRows Panels0054.weights_checked ⟨11, by decide⟩
def b0055 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0055.block Panels0055.accepted Panels0055.integerPanels Panels0055.aligned
    Panels0055.weightRows Panels0055.weights_checked ⟨11, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0048, b0049, b0050, b0051, b0052, b0053, b0054, b0055]
theorem chain_checked : blockChainCheck (44585757783099246165036576418/10^30) (57247499418396570304717986552/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=470038702946211540142005948069984072227991819504786396498035602629313459941721176198155954469563768474007222356774217109247723190001925883112280874459863993253975713609349931222138716426451425972104822966675011094/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row11
namespace Row12
abbrev ζ : ℚ := 9950248756218905472636815920/10^30
def b0048 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0048.block Panels0048.accepted Panels0048.integerPanels Panels0048.aligned
    Panels0048.weightRows Panels0048.weights_checked ⟨12, by decide⟩
def b0049 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0049.block Panels0049.accepted Panels0049.integerPanels Panels0049.aligned
    Panels0049.weightRows Panels0049.weights_checked ⟨12, by decide⟩
def b0050 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0050.block Panels0050.accepted Panels0050.integerPanels Panels0050.aligned
    Panels0050.weightRows Panels0050.weights_checked ⟨12, by decide⟩
def b0051 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0051.block Panels0051.accepted Panels0051.integerPanels Panels0051.aligned
    Panels0051.weightRows Panels0051.weights_checked ⟨12, by decide⟩
def b0052 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0052.block Panels0052.accepted Panels0052.integerPanels Panels0052.aligned
    Panels0052.weightRows Panels0052.weights_checked ⟨12, by decide⟩
def b0053 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0053.block Panels0053.accepted Panels0053.integerPanels Panels0053.aligned
    Panels0053.weightRows Panels0053.weights_checked ⟨12, by decide⟩
def b0054 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0054.block Panels0054.accepted Panels0054.integerPanels Panels0054.aligned
    Panels0054.weightRows Panels0054.weights_checked ⟨12, by decide⟩
def b0055 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0055.block Panels0055.accepted Panels0055.integerPanels Panels0055.aligned
    Panels0055.weightRows Panels0055.weights_checked ⟨12, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0048, b0049, b0050, b0051, b0052, b0053, b0054, b0055]
theorem chain_checked : blockChainCheck (44585757783099246165036576418/10^30) (57247499418396570304717986552/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=481880400895101480224860913653147140197924598086315115326675907788322226081849564086794628243140288827358983821428367551084977203494948520437986441900388503105834984600887111237171499539031426892845019601573298022/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row12
#print axioms Row12.segment
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments006
