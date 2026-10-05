module

public import BecknerOnofri.EntropyHeatCheckedWeights
public import BecknerOnofri.EntropyHeatSegments
public import BecknerOnofri.EntropyHeatCertificate.Panels0008
public import BecknerOnofri.EntropyHeatCertificate.Panels0009
public import BecknerOnofri.EntropyHeatCertificate.Panels0010
public import BecknerOnofri.EntropyHeatCertificate.Panels0011
public import BecknerOnofri.EntropyHeatCertificate.Panels0012
public import BecknerOnofri.EntropyHeatCertificate.Panels0013
public import BecknerOnofri.EntropyHeatCertificate.Panels0014
public import BecknerOnofri.EntropyHeatCertificate.Panels0015

@[expose] public section
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments001
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace Row00
abbrev ζ : ℚ := 285714285714285714285714285714/10^30
def b0008 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0008.block Panels0008.accepted Panels0008.integerPanels Panels0008.aligned
    Panels0008.weightRows Panels0008.weights_checked ⟨0, by decide⟩
def b0009 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0009.block Panels0009.accepted Panels0009.integerPanels Panels0009.aligned
    Panels0009.weightRows Panels0009.weights_checked ⟨0, by decide⟩
def b0010 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0010.block Panels0010.accepted Panels0010.integerPanels Panels0010.aligned
    Panels0010.weightRows Panels0010.weights_checked ⟨0, by decide⟩
def b0011 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0011.block Panels0011.accepted Panels0011.integerPanels Panels0011.aligned
    Panels0011.weightRows Panels0011.weights_checked ⟨0, by decide⟩
def b0012 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0012.block Panels0012.accepted Panels0012.integerPanels Panels0012.aligned
    Panels0012.weightRows Panels0012.weights_checked ⟨0, by decide⟩
def b0013 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0013.block Panels0013.accepted Panels0013.integerPanels Panels0013.aligned
    Panels0013.weightRows Panels0013.weights_checked ⟨0, by decide⟩
def b0014 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0014.block Panels0014.accepted Panels0014.integerPanels Panels0014.aligned
    Panels0014.weightRows Panels0014.weights_checked ⟨0, by decide⟩
def b0015 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0015.block Panels0015.accepted Panels0015.integerPanels Panels0015.aligned
    Panels0015.weightRows Panels0015.weights_checked ⟨0, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0008, b0009, b0010, b0011, b0012, b0013, b0014, b0015]
theorem chain_checked : blockChainCheck (12775982470807454187659253149/10^30) (16404185673485123870434928473/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row00
namespace Row01
abbrev ζ : ℚ := 222222222222222222222222222222/10^30
def b0008 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0008.block Panels0008.accepted Panels0008.integerPanels Panels0008.aligned
    Panels0008.weightRows Panels0008.weights_checked ⟨1, by decide⟩
def b0009 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0009.block Panels0009.accepted Panels0009.integerPanels Panels0009.aligned
    Panels0009.weightRows Panels0009.weights_checked ⟨1, by decide⟩
def b0010 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0010.block Panels0010.accepted Panels0010.integerPanels Panels0010.aligned
    Panels0010.weightRows Panels0010.weights_checked ⟨1, by decide⟩
def b0011 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0011.block Panels0011.accepted Panels0011.integerPanels Panels0011.aligned
    Panels0011.weightRows Panels0011.weights_checked ⟨1, by decide⟩
def b0012 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0012.block Panels0012.accepted Panels0012.integerPanels Panels0012.aligned
    Panels0012.weightRows Panels0012.weights_checked ⟨1, by decide⟩
def b0013 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0013.block Panels0013.accepted Panels0013.integerPanels Panels0013.aligned
    Panels0013.weightRows Panels0013.weights_checked ⟨1, by decide⟩
def b0014 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0014.block Panels0014.accepted Panels0014.integerPanels Panels0014.aligned
    Panels0014.weightRows Panels0014.weights_checked ⟨1, by decide⟩
def b0015 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0015.block Panels0015.accepted Panels0015.integerPanels Panels0015.aligned
    Panels0015.weightRows Panels0015.weights_checked ⟨1, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0008, b0009, b0010, b0011, b0012, b0013, b0014, b0015]
theorem chain_checked : blockChainCheck (12775982470807454187659253149/10^30) (16404185673485123870434928473/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row01
namespace Row02
abbrev ζ : ℚ := 153846153846153846153846153846/10^30
def b0008 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0008.block Panels0008.accepted Panels0008.integerPanels Panels0008.aligned
    Panels0008.weightRows Panels0008.weights_checked ⟨2, by decide⟩
def b0009 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0009.block Panels0009.accepted Panels0009.integerPanels Panels0009.aligned
    Panels0009.weightRows Panels0009.weights_checked ⟨2, by decide⟩
def b0010 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0010.block Panels0010.accepted Panels0010.integerPanels Panels0010.aligned
    Panels0010.weightRows Panels0010.weights_checked ⟨2, by decide⟩
def b0011 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0011.block Panels0011.accepted Panels0011.integerPanels Panels0011.aligned
    Panels0011.weightRows Panels0011.weights_checked ⟨2, by decide⟩
def b0012 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0012.block Panels0012.accepted Panels0012.integerPanels Panels0012.aligned
    Panels0012.weightRows Panels0012.weights_checked ⟨2, by decide⟩
def b0013 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0013.block Panels0013.accepted Panels0013.integerPanels Panels0013.aligned
    Panels0013.weightRows Panels0013.weights_checked ⟨2, by decide⟩
def b0014 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0014.block Panels0014.accepted Panels0014.integerPanels Panels0014.aligned
    Panels0014.weightRows Panels0014.weights_checked ⟨2, by decide⟩
def b0015 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0015.block Panels0015.accepted Panels0015.integerPanels Panels0015.aligned
    Panels0015.weightRows Panels0015.weights_checked ⟨2, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0008, b0009, b0010, b0011, b0012, b0013, b0014, b0015]
theorem chain_checked : blockChainCheck (12775982470807454187659253149/10^30) (16404185673485123870434928473/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row02
namespace Row03
abbrev ζ : ℚ := 117647058823529411764705882352/10^30
def b0008 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0008.block Panels0008.accepted Panels0008.integerPanels Panels0008.aligned
    Panels0008.weightRows Panels0008.weights_checked ⟨3, by decide⟩
def b0009 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0009.block Panels0009.accepted Panels0009.integerPanels Panels0009.aligned
    Panels0009.weightRows Panels0009.weights_checked ⟨3, by decide⟩
def b0010 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0010.block Panels0010.accepted Panels0010.integerPanels Panels0010.aligned
    Panels0010.weightRows Panels0010.weights_checked ⟨3, by decide⟩
def b0011 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0011.block Panels0011.accepted Panels0011.integerPanels Panels0011.aligned
    Panels0011.weightRows Panels0011.weights_checked ⟨3, by decide⟩
def b0012 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0012.block Panels0012.accepted Panels0012.integerPanels Panels0012.aligned
    Panels0012.weightRows Panels0012.weights_checked ⟨3, by decide⟩
def b0013 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0013.block Panels0013.accepted Panels0013.integerPanels Panels0013.aligned
    Panels0013.weightRows Panels0013.weights_checked ⟨3, by decide⟩
def b0014 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0014.block Panels0014.accepted Panels0014.integerPanels Panels0014.aligned
    Panels0014.weightRows Panels0014.weights_checked ⟨3, by decide⟩
def b0015 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0015.block Panels0015.accepted Panels0015.integerPanels Panels0015.aligned
    Panels0015.weightRows Panels0015.weights_checked ⟨3, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0008, b0009, b0010, b0011, b0012, b0013, b0014, b0015]
theorem chain_checked : blockChainCheck (12775982470807454187659253149/10^30) (16404185673485123870434928473/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row03
namespace Row04
abbrev ζ : ℚ := 86956521739130434782608695652/10^30
def b0008 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0008.block Panels0008.accepted Panels0008.integerPanels Panels0008.aligned
    Panels0008.weightRows Panels0008.weights_checked ⟨4, by decide⟩
def b0009 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0009.block Panels0009.accepted Panels0009.integerPanels Panels0009.aligned
    Panels0009.weightRows Panels0009.weights_checked ⟨4, by decide⟩
def b0010 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0010.block Panels0010.accepted Panels0010.integerPanels Panels0010.aligned
    Panels0010.weightRows Panels0010.weights_checked ⟨4, by decide⟩
def b0011 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0011.block Panels0011.accepted Panels0011.integerPanels Panels0011.aligned
    Panels0011.weightRows Panels0011.weights_checked ⟨4, by decide⟩
def b0012 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0012.block Panels0012.accepted Panels0012.integerPanels Panels0012.aligned
    Panels0012.weightRows Panels0012.weights_checked ⟨4, by decide⟩
def b0013 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0013.block Panels0013.accepted Panels0013.integerPanels Panels0013.aligned
    Panels0013.weightRows Panels0013.weights_checked ⟨4, by decide⟩
def b0014 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0014.block Panels0014.accepted Panels0014.integerPanels Panels0014.aligned
    Panels0014.weightRows Panels0014.weights_checked ⟨4, by decide⟩
def b0015 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0015.block Panels0015.accepted Panels0015.integerPanels Panels0015.aligned
    Panels0015.weightRows Panels0015.weights_checked ⟨4, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0008, b0009, b0010, b0011, b0012, b0013, b0014, b0015]
theorem chain_checked : blockChainCheck (12775982470807454187659253149/10^30) (16404185673485123870434928473/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row04
namespace Row05
abbrev ζ : ℚ := 64516129032258064516129032258/10^30
def b0008 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0008.block Panels0008.accepted Panels0008.integerPanels Panels0008.aligned
    Panels0008.weightRows Panels0008.weights_checked ⟨5, by decide⟩
def b0009 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0009.block Panels0009.accepted Panels0009.integerPanels Panels0009.aligned
    Panels0009.weightRows Panels0009.weights_checked ⟨5, by decide⟩
def b0010 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0010.block Panels0010.accepted Panels0010.integerPanels Panels0010.aligned
    Panels0010.weightRows Panels0010.weights_checked ⟨5, by decide⟩
def b0011 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0011.block Panels0011.accepted Panels0011.integerPanels Panels0011.aligned
    Panels0011.weightRows Panels0011.weights_checked ⟨5, by decide⟩
def b0012 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0012.block Panels0012.accepted Panels0012.integerPanels Panels0012.aligned
    Panels0012.weightRows Panels0012.weights_checked ⟨5, by decide⟩
def b0013 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0013.block Panels0013.accepted Panels0013.integerPanels Panels0013.aligned
    Panels0013.weightRows Panels0013.weights_checked ⟨5, by decide⟩
def b0014 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0014.block Panels0014.accepted Panels0014.integerPanels Panels0014.aligned
    Panels0014.weightRows Panels0014.weights_checked ⟨5, by decide⟩
def b0015 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0015.block Panels0015.accepted Panels0015.integerPanels Panels0015.aligned
    Panels0015.weightRows Panels0015.weights_checked ⟨5, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0008, b0009, b0010, b0011, b0012, b0013, b0014, b0015]
theorem chain_checked : blockChainCheck (12775982470807454187659253149/10^30) (16404185673485123870434928473/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row05
namespace Row06
abbrev ζ : ℚ := 46511627906976744186046511627/10^30
def b0008 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0008.block Panels0008.accepted Panels0008.integerPanels Panels0008.aligned
    Panels0008.weightRows Panels0008.weights_checked ⟨6, by decide⟩
def b0009 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0009.block Panels0009.accepted Panels0009.integerPanels Panels0009.aligned
    Panels0009.weightRows Panels0009.weights_checked ⟨6, by decide⟩
def b0010 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0010.block Panels0010.accepted Panels0010.integerPanels Panels0010.aligned
    Panels0010.weightRows Panels0010.weights_checked ⟨6, by decide⟩
def b0011 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0011.block Panels0011.accepted Panels0011.integerPanels Panels0011.aligned
    Panels0011.weightRows Panels0011.weights_checked ⟨6, by decide⟩
def b0012 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0012.block Panels0012.accepted Panels0012.integerPanels Panels0012.aligned
    Panels0012.weightRows Panels0012.weights_checked ⟨6, by decide⟩
def b0013 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0013.block Panels0013.accepted Panels0013.integerPanels Panels0013.aligned
    Panels0013.weightRows Panels0013.weights_checked ⟨6, by decide⟩
def b0014 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0014.block Panels0014.accepted Panels0014.integerPanels Panels0014.aligned
    Panels0014.weightRows Panels0014.weights_checked ⟨6, by decide⟩
def b0015 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0015.block Panels0015.accepted Panels0015.integerPanels Panels0015.aligned
    Panels0015.weightRows Panels0015.weights_checked ⟨6, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0008, b0009, b0010, b0011, b0012, b0013, b0014, b0015]
theorem chain_checked : blockChainCheck (12775982470807454187659253149/10^30) (16404185673485123870434928473/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row06
namespace Row07
abbrev ζ : ℚ := 33898305084745762711864406779/10^30
def b0008 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0008.block Panels0008.accepted Panels0008.integerPanels Panels0008.aligned
    Panels0008.weightRows Panels0008.weights_checked ⟨7, by decide⟩
def b0009 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0009.block Panels0009.accepted Panels0009.integerPanels Panels0009.aligned
    Panels0009.weightRows Panels0009.weights_checked ⟨7, by decide⟩
def b0010 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0010.block Panels0010.accepted Panels0010.integerPanels Panels0010.aligned
    Panels0010.weightRows Panels0010.weights_checked ⟨7, by decide⟩
def b0011 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0011.block Panels0011.accepted Panels0011.integerPanels Panels0011.aligned
    Panels0011.weightRows Panels0011.weights_checked ⟨7, by decide⟩
def b0012 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0012.block Panels0012.accepted Panels0012.integerPanels Panels0012.aligned
    Panels0012.weightRows Panels0012.weights_checked ⟨7, by decide⟩
def b0013 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0013.block Panels0013.accepted Panels0013.integerPanels Panels0013.aligned
    Panels0013.weightRows Panels0013.weights_checked ⟨7, by decide⟩
def b0014 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0014.block Panels0014.accepted Panels0014.integerPanels Panels0014.aligned
    Panels0014.weightRows Panels0014.weights_checked ⟨7, by decide⟩
def b0015 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0015.block Panels0015.accepted Panels0015.integerPanels Panels0015.aligned
    Panels0015.weightRows Panels0015.weights_checked ⟨7, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0008, b0009, b0010, b0011, b0012, b0013, b0014, b0015]
theorem chain_checked : blockChainCheck (12775982470807454187659253149/10^30) (16404185673485123870434928473/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row07
namespace Row08
abbrev ζ : ℚ := 25316455696202531645569620253/10^30
def b0008 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0008.block Panels0008.accepted Panels0008.integerPanels Panels0008.aligned
    Panels0008.weightRows Panels0008.weights_checked ⟨8, by decide⟩
def b0009 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0009.block Panels0009.accepted Panels0009.integerPanels Panels0009.aligned
    Panels0009.weightRows Panels0009.weights_checked ⟨8, by decide⟩
def b0010 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0010.block Panels0010.accepted Panels0010.integerPanels Panels0010.aligned
    Panels0010.weightRows Panels0010.weights_checked ⟨8, by decide⟩
def b0011 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0011.block Panels0011.accepted Panels0011.integerPanels Panels0011.aligned
    Panels0011.weightRows Panels0011.weights_checked ⟨8, by decide⟩
def b0012 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0012.block Panels0012.accepted Panels0012.integerPanels Panels0012.aligned
    Panels0012.weightRows Panels0012.weights_checked ⟨8, by decide⟩
def b0013 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0013.block Panels0013.accepted Panels0013.integerPanels Panels0013.aligned
    Panels0013.weightRows Panels0013.weights_checked ⟨8, by decide⟩
def b0014 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0014.block Panels0014.accepted Panels0014.integerPanels Panels0014.aligned
    Panels0014.weightRows Panels0014.weights_checked ⟨8, by decide⟩
def b0015 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0015.block Panels0015.accepted Panels0015.integerPanels Panels0015.aligned
    Panels0015.weightRows Panels0015.weights_checked ⟨8, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0008, b0009, b0010, b0011, b0012, b0013, b0014, b0015]
theorem chain_checked : blockChainCheck (12775982470807454187659253149/10^30) (16404185673485123870434928473/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row08
namespace Row09
abbrev ζ : ℚ := 18691588785046728971962616822/10^30
def b0008 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0008.block Panels0008.accepted Panels0008.integerPanels Panels0008.aligned
    Panels0008.weightRows Panels0008.weights_checked ⟨9, by decide⟩
def b0009 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0009.block Panels0009.accepted Panels0009.integerPanels Panels0009.aligned
    Panels0009.weightRows Panels0009.weights_checked ⟨9, by decide⟩
def b0010 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0010.block Panels0010.accepted Panels0010.integerPanels Panels0010.aligned
    Panels0010.weightRows Panels0010.weights_checked ⟨9, by decide⟩
def b0011 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0011.block Panels0011.accepted Panels0011.integerPanels Panels0011.aligned
    Panels0011.weightRows Panels0011.weights_checked ⟨9, by decide⟩
def b0012 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0012.block Panels0012.accepted Panels0012.integerPanels Panels0012.aligned
    Panels0012.weightRows Panels0012.weights_checked ⟨9, by decide⟩
def b0013 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0013.block Panels0013.accepted Panels0013.integerPanels Panels0013.aligned
    Panels0013.weightRows Panels0013.weights_checked ⟨9, by decide⟩
def b0014 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0014.block Panels0014.accepted Panels0014.integerPanels Panels0014.aligned
    Panels0014.weightRows Panels0014.weights_checked ⟨9, by decide⟩
def b0015 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0015.block Panels0015.accepted Panels0015.integerPanels Panels0015.aligned
    Panels0015.weightRows Panels0015.weights_checked ⟨9, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0008, b0009, b0010, b0011, b0012, b0013, b0014, b0015]
theorem chain_checked : blockChainCheck (12775982470807454187659253149/10^30) (16404185673485123870434928473/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row09
namespace Row10
abbrev ζ : ℚ := 13793103448275862068965517241/10^30
def b0008 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0008.block Panels0008.accepted Panels0008.integerPanels Panels0008.aligned
    Panels0008.weightRows Panels0008.weights_checked ⟨10, by decide⟩
def b0009 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0009.block Panels0009.accepted Panels0009.integerPanels Panels0009.aligned
    Panels0009.weightRows Panels0009.weights_checked ⟨10, by decide⟩
def b0010 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0010.block Panels0010.accepted Panels0010.integerPanels Panels0010.aligned
    Panels0010.weightRows Panels0010.weights_checked ⟨10, by decide⟩
def b0011 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0011.block Panels0011.accepted Panels0011.integerPanels Panels0011.aligned
    Panels0011.weightRows Panels0011.weights_checked ⟨10, by decide⟩
def b0012 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0012.block Panels0012.accepted Panels0012.integerPanels Panels0012.aligned
    Panels0012.weightRows Panels0012.weights_checked ⟨10, by decide⟩
def b0013 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0013.block Panels0013.accepted Panels0013.integerPanels Panels0013.aligned
    Panels0013.weightRows Panels0013.weights_checked ⟨10, by decide⟩
def b0014 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0014.block Panels0014.accepted Panels0014.integerPanels Panels0014.aligned
    Panels0014.weightRows Panels0014.weights_checked ⟨10, by decide⟩
def b0015 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0015.block Panels0015.accepted Panels0015.integerPanels Panels0015.aligned
    Panels0015.weightRows Panels0015.weights_checked ⟨10, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0008, b0009, b0010, b0011, b0012, b0013, b0014, b0015]
theorem chain_checked : blockChainCheck (12775982470807454187659253149/10^30) (16404185673485123870434928473/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=18127443518276726617534511041001558670332498080454263776869779502816544262382217072775627819689194213779158495660047642965342223111117408453168566371444720301268607634838021614160944723994082470780364670484673/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row10
namespace Row11
abbrev ζ : ℚ := 10152284263959390862944162436/10^30
def b0008 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0008.block Panels0008.accepted Panels0008.integerPanels Panels0008.aligned
    Panels0008.weightRows Panels0008.weights_checked ⟨11, by decide⟩
def b0009 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0009.block Panels0009.accepted Panels0009.integerPanels Panels0009.aligned
    Panels0009.weightRows Panels0009.weights_checked ⟨11, by decide⟩
def b0010 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0010.block Panels0010.accepted Panels0010.integerPanels Panels0010.aligned
    Panels0010.weightRows Panels0010.weights_checked ⟨11, by decide⟩
def b0011 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0011.block Panels0011.accepted Panels0011.integerPanels Panels0011.aligned
    Panels0011.weightRows Panels0011.weights_checked ⟨11, by decide⟩
def b0012 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0012.block Panels0012.accepted Panels0012.integerPanels Panels0012.aligned
    Panels0012.weightRows Panels0012.weights_checked ⟨11, by decide⟩
def b0013 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0013.block Panels0013.accepted Panels0013.integerPanels Panels0013.aligned
    Panels0013.weightRows Panels0013.weights_checked ⟨11, by decide⟩
def b0014 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0014.block Panels0014.accepted Panels0014.integerPanels Panels0014.aligned
    Panels0014.weightRows Panels0014.weights_checked ⟨11, by decide⟩
def b0015 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0015.block Panels0015.accepted Panels0015.integerPanels Panels0015.aligned
    Panels0015.weightRows Panels0015.weights_checked ⟨11, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0008, b0009, b0010, b0011, b0012, b0013, b0014, b0015]
theorem chain_checked : blockChainCheck (12775982470807454187659253149/10^30) (16404185673485123870434928473/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=4310881691062236488774354769752694665594590305734366282623651764928666409910207303374449842215741956927192630348607923349913452226984982205007218375478608077984652170348224654929409095702587813918335871328687005/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row11
namespace Row12
abbrev ζ : ℚ := 9950248756218905472636815920/10^30
def b0008 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0008.block Panels0008.accepted Panels0008.integerPanels Panels0008.aligned
    Panels0008.weightRows Panels0008.weights_checked ⟨12, by decide⟩
def b0009 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0009.block Panels0009.accepted Panels0009.integerPanels Panels0009.aligned
    Panels0009.weightRows Panels0009.weights_checked ⟨12, by decide⟩
def b0010 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0010.block Panels0010.accepted Panels0010.integerPanels Panels0010.aligned
    Panels0010.weightRows Panels0010.weights_checked ⟨12, by decide⟩
def b0011 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0011.block Panels0011.accepted Panels0011.integerPanels Panels0011.aligned
    Panels0011.weightRows Panels0011.weights_checked ⟨12, by decide⟩
def b0012 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0012.block Panels0012.accepted Panels0012.integerPanels Panels0012.aligned
    Panels0012.weightRows Panels0012.weights_checked ⟨12, by decide⟩
def b0013 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0013.block Panels0013.accepted Panels0013.integerPanels Panels0013.aligned
    Panels0013.weightRows Panels0013.weights_checked ⟨12, by decide⟩
def b0014 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0014.block Panels0014.accepted Panels0014.integerPanels Panels0014.aligned
    Panels0014.weightRows Panels0014.weights_checked ⟨12, by decide⟩
def b0015 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0015.block Panels0015.accepted Panels0015.integerPanels Panels0015.aligned
    Panels0015.weightRows Panels0015.weights_checked ⟨12, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0008, b0009, b0010, b0011, b0012, b0013, b0014, b0015]
theorem chain_checked : blockChainCheck (12775982470807454187659253149/10^30) (16404185673485123870434928473/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=5271384298421156955509490864634040666032750410832273478306084482382168744532485891693699611152125736795370808530640538266148590324416510358263954578371665974252125638893855256942920706053489869966291495762886613/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row12
#print axioms Row12.segment
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments001
