module

public import BecknerOnofri.EntropyHeatCheckedWeights
public import BecknerOnofri.EntropyHeatSegments
public import BecknerOnofri.EntropyHeatCertificate.Panels0000
public import BecknerOnofri.EntropyHeatCertificate.Panels0001
public import BecknerOnofri.EntropyHeatCertificate.Panels0002
public import BecknerOnofri.EntropyHeatCertificate.Panels0003
public import BecknerOnofri.EntropyHeatCertificate.Panels0004
public import BecknerOnofri.EntropyHeatCertificate.Panels0005
public import BecknerOnofri.EntropyHeatCertificate.Panels0006
public import BecknerOnofri.EntropyHeatCertificate.Panels0007

@[expose] public section
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments000
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace Row00
abbrev ζ : ℚ := 285714285714285714285714285714/10^30
def b0000 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0000.block Panels0000.accepted Panels0000.integerPanels Panels0000.aligned
    Panels0000.weightRows Panels0000.weights_checked ⟨0, by decide⟩
def b0001 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0001.block Panels0001.accepted Panels0001.integerPanels Panels0001.aligned
    Panels0001.weightRows Panels0001.weights_checked ⟨0, by decide⟩
def b0002 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0002.block Panels0002.accepted Panels0002.integerPanels Panels0002.aligned
    Panels0002.weightRows Panels0002.weights_checked ⟨0, by decide⟩
def b0003 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0003.block Panels0003.accepted Panels0003.integerPanels Panels0003.aligned
    Panels0003.weightRows Panels0003.weights_checked ⟨0, by decide⟩
def b0004 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0004.block Panels0004.accepted Panels0004.integerPanels Panels0004.aligned
    Panels0004.weightRows Panels0004.weights_checked ⟨0, by decide⟩
def b0005 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0005.block Panels0005.accepted Panels0005.integerPanels Panels0005.aligned
    Panels0005.weightRows Panels0005.weights_checked ⟨0, by decide⟩
def b0006 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0006.block Panels0006.accepted Panels0006.integerPanels Panels0006.aligned
    Panels0006.weightRows Panels0006.weights_checked ⟨0, by decide⟩
def b0007 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0007.block Panels0007.accepted Panels0007.integerPanels Panels0007.aligned
    Panels0007.weightRows Panels0007.weights_checked ⟨0, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0000, b0001, b0002, b0003, b0004, b0005, b0006, b0007]
theorem chain_checked : blockChainCheck (9950248756218905472636815920/10^30) (12775982470807454187659253149/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row00
namespace Row01
abbrev ζ : ℚ := 222222222222222222222222222222/10^30
def b0000 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0000.block Panels0000.accepted Panels0000.integerPanels Panels0000.aligned
    Panels0000.weightRows Panels0000.weights_checked ⟨1, by decide⟩
def b0001 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0001.block Panels0001.accepted Panels0001.integerPanels Panels0001.aligned
    Panels0001.weightRows Panels0001.weights_checked ⟨1, by decide⟩
def b0002 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0002.block Panels0002.accepted Panels0002.integerPanels Panels0002.aligned
    Panels0002.weightRows Panels0002.weights_checked ⟨1, by decide⟩
def b0003 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0003.block Panels0003.accepted Panels0003.integerPanels Panels0003.aligned
    Panels0003.weightRows Panels0003.weights_checked ⟨1, by decide⟩
def b0004 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0004.block Panels0004.accepted Panels0004.integerPanels Panels0004.aligned
    Panels0004.weightRows Panels0004.weights_checked ⟨1, by decide⟩
def b0005 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0005.block Panels0005.accepted Panels0005.integerPanels Panels0005.aligned
    Panels0005.weightRows Panels0005.weights_checked ⟨1, by decide⟩
def b0006 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0006.block Panels0006.accepted Panels0006.integerPanels Panels0006.aligned
    Panels0006.weightRows Panels0006.weights_checked ⟨1, by decide⟩
def b0007 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0007.block Panels0007.accepted Panels0007.integerPanels Panels0007.aligned
    Panels0007.weightRows Panels0007.weights_checked ⟨1, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0000, b0001, b0002, b0003, b0004, b0005, b0006, b0007]
theorem chain_checked : blockChainCheck (9950248756218905472636815920/10^30) (12775982470807454187659253149/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row01
namespace Row02
abbrev ζ : ℚ := 153846153846153846153846153846/10^30
def b0000 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0000.block Panels0000.accepted Panels0000.integerPanels Panels0000.aligned
    Panels0000.weightRows Panels0000.weights_checked ⟨2, by decide⟩
def b0001 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0001.block Panels0001.accepted Panels0001.integerPanels Panels0001.aligned
    Panels0001.weightRows Panels0001.weights_checked ⟨2, by decide⟩
def b0002 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0002.block Panels0002.accepted Panels0002.integerPanels Panels0002.aligned
    Panels0002.weightRows Panels0002.weights_checked ⟨2, by decide⟩
def b0003 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0003.block Panels0003.accepted Panels0003.integerPanels Panels0003.aligned
    Panels0003.weightRows Panels0003.weights_checked ⟨2, by decide⟩
def b0004 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0004.block Panels0004.accepted Panels0004.integerPanels Panels0004.aligned
    Panels0004.weightRows Panels0004.weights_checked ⟨2, by decide⟩
def b0005 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0005.block Panels0005.accepted Panels0005.integerPanels Panels0005.aligned
    Panels0005.weightRows Panels0005.weights_checked ⟨2, by decide⟩
def b0006 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0006.block Panels0006.accepted Panels0006.integerPanels Panels0006.aligned
    Panels0006.weightRows Panels0006.weights_checked ⟨2, by decide⟩
def b0007 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0007.block Panels0007.accepted Panels0007.integerPanels Panels0007.aligned
    Panels0007.weightRows Panels0007.weights_checked ⟨2, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0000, b0001, b0002, b0003, b0004, b0005, b0006, b0007]
theorem chain_checked : blockChainCheck (9950248756218905472636815920/10^30) (12775982470807454187659253149/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row02
namespace Row03
abbrev ζ : ℚ := 117647058823529411764705882352/10^30
def b0000 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0000.block Panels0000.accepted Panels0000.integerPanels Panels0000.aligned
    Panels0000.weightRows Panels0000.weights_checked ⟨3, by decide⟩
def b0001 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0001.block Panels0001.accepted Panels0001.integerPanels Panels0001.aligned
    Panels0001.weightRows Panels0001.weights_checked ⟨3, by decide⟩
def b0002 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0002.block Panels0002.accepted Panels0002.integerPanels Panels0002.aligned
    Panels0002.weightRows Panels0002.weights_checked ⟨3, by decide⟩
def b0003 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0003.block Panels0003.accepted Panels0003.integerPanels Panels0003.aligned
    Panels0003.weightRows Panels0003.weights_checked ⟨3, by decide⟩
def b0004 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0004.block Panels0004.accepted Panels0004.integerPanels Panels0004.aligned
    Panels0004.weightRows Panels0004.weights_checked ⟨3, by decide⟩
def b0005 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0005.block Panels0005.accepted Panels0005.integerPanels Panels0005.aligned
    Panels0005.weightRows Panels0005.weights_checked ⟨3, by decide⟩
def b0006 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0006.block Panels0006.accepted Panels0006.integerPanels Panels0006.aligned
    Panels0006.weightRows Panels0006.weights_checked ⟨3, by decide⟩
def b0007 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0007.block Panels0007.accepted Panels0007.integerPanels Panels0007.aligned
    Panels0007.weightRows Panels0007.weights_checked ⟨3, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0000, b0001, b0002, b0003, b0004, b0005, b0006, b0007]
theorem chain_checked : blockChainCheck (9950248756218905472636815920/10^30) (12775982470807454187659253149/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row03
namespace Row04
abbrev ζ : ℚ := 86956521739130434782608695652/10^30
def b0000 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0000.block Panels0000.accepted Panels0000.integerPanels Panels0000.aligned
    Panels0000.weightRows Panels0000.weights_checked ⟨4, by decide⟩
def b0001 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0001.block Panels0001.accepted Panels0001.integerPanels Panels0001.aligned
    Panels0001.weightRows Panels0001.weights_checked ⟨4, by decide⟩
def b0002 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0002.block Panels0002.accepted Panels0002.integerPanels Panels0002.aligned
    Panels0002.weightRows Panels0002.weights_checked ⟨4, by decide⟩
def b0003 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0003.block Panels0003.accepted Panels0003.integerPanels Panels0003.aligned
    Panels0003.weightRows Panels0003.weights_checked ⟨4, by decide⟩
def b0004 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0004.block Panels0004.accepted Panels0004.integerPanels Panels0004.aligned
    Panels0004.weightRows Panels0004.weights_checked ⟨4, by decide⟩
def b0005 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0005.block Panels0005.accepted Panels0005.integerPanels Panels0005.aligned
    Panels0005.weightRows Panels0005.weights_checked ⟨4, by decide⟩
def b0006 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0006.block Panels0006.accepted Panels0006.integerPanels Panels0006.aligned
    Panels0006.weightRows Panels0006.weights_checked ⟨4, by decide⟩
def b0007 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0007.block Panels0007.accepted Panels0007.integerPanels Panels0007.aligned
    Panels0007.weightRows Panels0007.weights_checked ⟨4, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0000, b0001, b0002, b0003, b0004, b0005, b0006, b0007]
theorem chain_checked : blockChainCheck (9950248756218905472636815920/10^30) (12775982470807454187659253149/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row04
namespace Row05
abbrev ζ : ℚ := 64516129032258064516129032258/10^30
def b0000 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0000.block Panels0000.accepted Panels0000.integerPanels Panels0000.aligned
    Panels0000.weightRows Panels0000.weights_checked ⟨5, by decide⟩
def b0001 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0001.block Panels0001.accepted Panels0001.integerPanels Panels0001.aligned
    Panels0001.weightRows Panels0001.weights_checked ⟨5, by decide⟩
def b0002 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0002.block Panels0002.accepted Panels0002.integerPanels Panels0002.aligned
    Panels0002.weightRows Panels0002.weights_checked ⟨5, by decide⟩
def b0003 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0003.block Panels0003.accepted Panels0003.integerPanels Panels0003.aligned
    Panels0003.weightRows Panels0003.weights_checked ⟨5, by decide⟩
def b0004 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0004.block Panels0004.accepted Panels0004.integerPanels Panels0004.aligned
    Panels0004.weightRows Panels0004.weights_checked ⟨5, by decide⟩
def b0005 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0005.block Panels0005.accepted Panels0005.integerPanels Panels0005.aligned
    Panels0005.weightRows Panels0005.weights_checked ⟨5, by decide⟩
def b0006 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0006.block Panels0006.accepted Panels0006.integerPanels Panels0006.aligned
    Panels0006.weightRows Panels0006.weights_checked ⟨5, by decide⟩
def b0007 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0007.block Panels0007.accepted Panels0007.integerPanels Panels0007.aligned
    Panels0007.weightRows Panels0007.weights_checked ⟨5, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0000, b0001, b0002, b0003, b0004, b0005, b0006, b0007]
theorem chain_checked : blockChainCheck (9950248756218905472636815920/10^30) (12775982470807454187659253149/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row05
namespace Row06
abbrev ζ : ℚ := 46511627906976744186046511627/10^30
def b0000 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0000.block Panels0000.accepted Panels0000.integerPanels Panels0000.aligned
    Panels0000.weightRows Panels0000.weights_checked ⟨6, by decide⟩
def b0001 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0001.block Panels0001.accepted Panels0001.integerPanels Panels0001.aligned
    Panels0001.weightRows Panels0001.weights_checked ⟨6, by decide⟩
def b0002 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0002.block Panels0002.accepted Panels0002.integerPanels Panels0002.aligned
    Panels0002.weightRows Panels0002.weights_checked ⟨6, by decide⟩
def b0003 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0003.block Panels0003.accepted Panels0003.integerPanels Panels0003.aligned
    Panels0003.weightRows Panels0003.weights_checked ⟨6, by decide⟩
def b0004 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0004.block Panels0004.accepted Panels0004.integerPanels Panels0004.aligned
    Panels0004.weightRows Panels0004.weights_checked ⟨6, by decide⟩
def b0005 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0005.block Panels0005.accepted Panels0005.integerPanels Panels0005.aligned
    Panels0005.weightRows Panels0005.weights_checked ⟨6, by decide⟩
def b0006 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0006.block Panels0006.accepted Panels0006.integerPanels Panels0006.aligned
    Panels0006.weightRows Panels0006.weights_checked ⟨6, by decide⟩
def b0007 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0007.block Panels0007.accepted Panels0007.integerPanels Panels0007.aligned
    Panels0007.weightRows Panels0007.weights_checked ⟨6, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0000, b0001, b0002, b0003, b0004, b0005, b0006, b0007]
theorem chain_checked : blockChainCheck (9950248756218905472636815920/10^30) (12775982470807454187659253149/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row06
namespace Row07
abbrev ζ : ℚ := 33898305084745762711864406779/10^30
def b0000 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0000.block Panels0000.accepted Panels0000.integerPanels Panels0000.aligned
    Panels0000.weightRows Panels0000.weights_checked ⟨7, by decide⟩
def b0001 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0001.block Panels0001.accepted Panels0001.integerPanels Panels0001.aligned
    Panels0001.weightRows Panels0001.weights_checked ⟨7, by decide⟩
def b0002 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0002.block Panels0002.accepted Panels0002.integerPanels Panels0002.aligned
    Panels0002.weightRows Panels0002.weights_checked ⟨7, by decide⟩
def b0003 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0003.block Panels0003.accepted Panels0003.integerPanels Panels0003.aligned
    Panels0003.weightRows Panels0003.weights_checked ⟨7, by decide⟩
def b0004 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0004.block Panels0004.accepted Panels0004.integerPanels Panels0004.aligned
    Panels0004.weightRows Panels0004.weights_checked ⟨7, by decide⟩
def b0005 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0005.block Panels0005.accepted Panels0005.integerPanels Panels0005.aligned
    Panels0005.weightRows Panels0005.weights_checked ⟨7, by decide⟩
def b0006 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0006.block Panels0006.accepted Panels0006.integerPanels Panels0006.aligned
    Panels0006.weightRows Panels0006.weights_checked ⟨7, by decide⟩
def b0007 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0007.block Panels0007.accepted Panels0007.integerPanels Panels0007.aligned
    Panels0007.weightRows Panels0007.weights_checked ⟨7, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0000, b0001, b0002, b0003, b0004, b0005, b0006, b0007]
theorem chain_checked : blockChainCheck (9950248756218905472636815920/10^30) (12775982470807454187659253149/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row07
namespace Row08
abbrev ζ : ℚ := 25316455696202531645569620253/10^30
def b0000 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0000.block Panels0000.accepted Panels0000.integerPanels Panels0000.aligned
    Panels0000.weightRows Panels0000.weights_checked ⟨8, by decide⟩
def b0001 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0001.block Panels0001.accepted Panels0001.integerPanels Panels0001.aligned
    Panels0001.weightRows Panels0001.weights_checked ⟨8, by decide⟩
def b0002 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0002.block Panels0002.accepted Panels0002.integerPanels Panels0002.aligned
    Panels0002.weightRows Panels0002.weights_checked ⟨8, by decide⟩
def b0003 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0003.block Panels0003.accepted Panels0003.integerPanels Panels0003.aligned
    Panels0003.weightRows Panels0003.weights_checked ⟨8, by decide⟩
def b0004 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0004.block Panels0004.accepted Panels0004.integerPanels Panels0004.aligned
    Panels0004.weightRows Panels0004.weights_checked ⟨8, by decide⟩
def b0005 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0005.block Panels0005.accepted Panels0005.integerPanels Panels0005.aligned
    Panels0005.weightRows Panels0005.weights_checked ⟨8, by decide⟩
def b0006 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0006.block Panels0006.accepted Panels0006.integerPanels Panels0006.aligned
    Panels0006.weightRows Panels0006.weights_checked ⟨8, by decide⟩
def b0007 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0007.block Panels0007.accepted Panels0007.integerPanels Panels0007.aligned
    Panels0007.weightRows Panels0007.weights_checked ⟨8, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0000, b0001, b0002, b0003, b0004, b0005, b0006, b0007]
theorem chain_checked : blockChainCheck (9950248756218905472636815920/10^30) (12775982470807454187659253149/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row08
namespace Row09
abbrev ζ : ℚ := 18691588785046728971962616822/10^30
def b0000 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0000.block Panels0000.accepted Panels0000.integerPanels Panels0000.aligned
    Panels0000.weightRows Panels0000.weights_checked ⟨9, by decide⟩
def b0001 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0001.block Panels0001.accepted Panels0001.integerPanels Panels0001.aligned
    Panels0001.weightRows Panels0001.weights_checked ⟨9, by decide⟩
def b0002 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0002.block Panels0002.accepted Panels0002.integerPanels Panels0002.aligned
    Panels0002.weightRows Panels0002.weights_checked ⟨9, by decide⟩
def b0003 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0003.block Panels0003.accepted Panels0003.integerPanels Panels0003.aligned
    Panels0003.weightRows Panels0003.weights_checked ⟨9, by decide⟩
def b0004 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0004.block Panels0004.accepted Panels0004.integerPanels Panels0004.aligned
    Panels0004.weightRows Panels0004.weights_checked ⟨9, by decide⟩
def b0005 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0005.block Panels0005.accepted Panels0005.integerPanels Panels0005.aligned
    Panels0005.weightRows Panels0005.weights_checked ⟨9, by decide⟩
def b0006 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0006.block Panels0006.accepted Panels0006.integerPanels Panels0006.aligned
    Panels0006.weightRows Panels0006.weights_checked ⟨9, by decide⟩
def b0007 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0007.block Panels0007.accepted Panels0007.integerPanels Panels0007.aligned
    Panels0007.weightRows Panels0007.weights_checked ⟨9, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0000, b0001, b0002, b0003, b0004, b0005, b0006, b0007]
theorem chain_checked : blockChainCheck (9950248756218905472636815920/10^30) (12775982470807454187659253149/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row09
namespace Row10
abbrev ζ : ℚ := 13793103448275862068965517241/10^30
def b0000 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0000.block Panels0000.accepted Panels0000.integerPanels Panels0000.aligned
    Panels0000.weightRows Panels0000.weights_checked ⟨10, by decide⟩
def b0001 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0001.block Panels0001.accepted Panels0001.integerPanels Panels0001.aligned
    Panels0001.weightRows Panels0001.weights_checked ⟨10, by decide⟩
def b0002 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0002.block Panels0002.accepted Panels0002.integerPanels Panels0002.aligned
    Panels0002.weightRows Panels0002.weights_checked ⟨10, by decide⟩
def b0003 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0003.block Panels0003.accepted Panels0003.integerPanels Panels0003.aligned
    Panels0003.weightRows Panels0003.weights_checked ⟨10, by decide⟩
def b0004 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0004.block Panels0004.accepted Panels0004.integerPanels Panels0004.aligned
    Panels0004.weightRows Panels0004.weights_checked ⟨10, by decide⟩
def b0005 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0005.block Panels0005.accepted Panels0005.integerPanels Panels0005.aligned
    Panels0005.weightRows Panels0005.weights_checked ⟨10, by decide⟩
def b0006 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0006.block Panels0006.accepted Panels0006.integerPanels Panels0006.aligned
    Panels0006.weightRows Panels0006.weights_checked ⟨10, by decide⟩
def b0007 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0007.block Panels0007.accepted Panels0007.integerPanels Panels0007.aligned
    Panels0007.weightRows Panels0007.weights_checked ⟨10, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0000, b0001, b0002, b0003, b0004, b0005, b0006, b0007]
theorem chain_checked : blockChainCheck (9950248756218905472636815920/10^30) (12775982470807454187659253149/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row10
namespace Row11
abbrev ζ : ℚ := 10152284263959390862944162436/10^30
def b0000 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0000.block Panels0000.accepted Panels0000.integerPanels Panels0000.aligned
    Panels0000.weightRows Panels0000.weights_checked ⟨11, by decide⟩
def b0001 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0001.block Panels0001.accepted Panels0001.integerPanels Panels0001.aligned
    Panels0001.weightRows Panels0001.weights_checked ⟨11, by decide⟩
def b0002 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0002.block Panels0002.accepted Panels0002.integerPanels Panels0002.aligned
    Panels0002.weightRows Panels0002.weights_checked ⟨11, by decide⟩
def b0003 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0003.block Panels0003.accepted Panels0003.integerPanels Panels0003.aligned
    Panels0003.weightRows Panels0003.weights_checked ⟨11, by decide⟩
def b0004 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0004.block Panels0004.accepted Panels0004.integerPanels Panels0004.aligned
    Panels0004.weightRows Panels0004.weights_checked ⟨11, by decide⟩
def b0005 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0005.block Panels0005.accepted Panels0005.integerPanels Panels0005.aligned
    Panels0005.weightRows Panels0005.weights_checked ⟨11, by decide⟩
def b0006 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0006.block Panels0006.accepted Panels0006.integerPanels Panels0006.aligned
    Panels0006.weightRows Panels0006.weights_checked ⟨11, by decide⟩
def b0007 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0007.block Panels0007.accepted Panels0007.integerPanels Panels0007.aligned
    Panels0007.weightRows Panels0007.weights_checked ⟨11, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0000, b0001, b0002, b0003, b0004, b0005, b0006, b0007]
theorem chain_checked : blockChainCheck (9950248756218905472636815920/10^30) (12775982470807454187659253149/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=87663489590400680935173936970687873618906730266378262143476671472073214147771228892832140702607419345466149819828275955936387497854518817188783906794389962579048982278964932351370864064125335913838020553123377/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row11
namespace Row12
abbrev ζ : ℚ := 9950248756218905472636815920/10^30
def b0000 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0000.block Panels0000.accepted Panels0000.integerPanels Panels0000.aligned
    Panels0000.weightRows Panels0000.weights_checked ⟨12, by decide⟩
def b0001 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0001.block Panels0001.accepted Panels0001.integerPanels Panels0001.aligned
    Panels0001.weightRows Panels0001.weights_checked ⟨12, by decide⟩
def b0002 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0002.block Panels0002.accepted Panels0002.integerPanels Panels0002.aligned
    Panels0002.weightRows Panels0002.weights_checked ⟨12, by decide⟩
def b0003 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0003.block Panels0003.accepted Panels0003.integerPanels Panels0003.aligned
    Panels0003.weightRows Panels0003.weights_checked ⟨12, by decide⟩
def b0004 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0004.block Panels0004.accepted Panels0004.integerPanels Panels0004.aligned
    Panels0004.weightRows Panels0004.weights_checked ⟨12, by decide⟩
def b0005 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0005.block Panels0005.accepted Panels0005.integerPanels Panels0005.aligned
    Panels0005.weightRows Panels0005.weights_checked ⟨12, by decide⟩
def b0006 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0006.block Panels0006.accepted Panels0006.integerPanels Panels0006.aligned
    Panels0006.weightRows Panels0006.weights_checked ⟨12, by decide⟩
def b0007 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0007.block Panels0007.accepted Panels0007.integerPanels Panels0007.aligned
    Panels0007.weightRows Panels0007.weights_checked ⟨12, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0000, b0001, b0002, b0003, b0004, b0005, b0006, b0007]
theorem chain_checked : blockChainCheck (9950248756218905472636815920/10^30) (12775982470807454187659253149/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=139124698745800086350225110804887717120139436390573459610037643269913677204817927868553854411719519857291304958248097434654908339288647656087867201053968911275712609344098256847892034700285464046210371211609202/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row12
#print axioms Row12.segment
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments000
