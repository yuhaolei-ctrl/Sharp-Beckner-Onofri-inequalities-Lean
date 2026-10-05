module

public import BecknerOnofri.EntropyHeatCheckedWeights
public import BecknerOnofri.EntropyHeatSegments
public import BecknerOnofri.EntropyHeatCertificate.Panels0016
public import BecknerOnofri.EntropyHeatCertificate.Panels0017
public import BecknerOnofri.EntropyHeatCertificate.Panels0018
public import BecknerOnofri.EntropyHeatCertificate.Panels0019
public import BecknerOnofri.EntropyHeatCertificate.Panels0020
public import BecknerOnofri.EntropyHeatCertificate.Panels0021
public import BecknerOnofri.EntropyHeatCertificate.Panels0022
public import BecknerOnofri.EntropyHeatCertificate.Panels0023

@[expose] public section
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments002
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace Row00
abbrev ζ : ℚ := 285714285714285714285714285714/10^30
def b0016 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0016.block Panels0016.accepted Panels0016.integerPanels Panels0016.aligned
    Panels0016.weightRows Panels0016.weights_checked ⟨0, by decide⟩
def b0017 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0017.block Panels0017.accepted Panels0017.integerPanels Panels0017.aligned
    Panels0017.weightRows Panels0017.weights_checked ⟨0, by decide⟩
def b0018 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0018.block Panels0018.accepted Panels0018.integerPanels Panels0018.aligned
    Panels0018.weightRows Panels0018.weights_checked ⟨0, by decide⟩
def b0019 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0019.block Panels0019.accepted Panels0019.integerPanels Panels0019.aligned
    Panels0019.weightRows Panels0019.weights_checked ⟨0, by decide⟩
def b0020 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0020.block Panels0020.accepted Panels0020.integerPanels Panels0020.aligned
    Panels0020.weightRows Panels0020.weights_checked ⟨0, by decide⟩
def b0021 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0021.block Panels0021.accepted Panels0021.integerPanels Panels0021.aligned
    Panels0021.weightRows Panels0021.weights_checked ⟨0, by decide⟩
def b0022 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0022.block Panels0022.accepted Panels0022.integerPanels Panels0022.aligned
    Panels0022.weightRows Panels0022.weights_checked ⟨0, by decide⟩
def b0023 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0023.block Panels0023.accepted Panels0023.integerPanels Panels0023.aligned
    Panels0023.weightRows Panels0023.weights_checked ⟨0, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0016, b0017, b0018, b0019, b0020, b0021, b0022, b0023]
theorem chain_checked : blockChainCheck (16404185673485123870434928473/10^30) (21062748655537829836560893631/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row00
namespace Row01
abbrev ζ : ℚ := 222222222222222222222222222222/10^30
def b0016 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0016.block Panels0016.accepted Panels0016.integerPanels Panels0016.aligned
    Panels0016.weightRows Panels0016.weights_checked ⟨1, by decide⟩
def b0017 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0017.block Panels0017.accepted Panels0017.integerPanels Panels0017.aligned
    Panels0017.weightRows Panels0017.weights_checked ⟨1, by decide⟩
def b0018 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0018.block Panels0018.accepted Panels0018.integerPanels Panels0018.aligned
    Panels0018.weightRows Panels0018.weights_checked ⟨1, by decide⟩
def b0019 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0019.block Panels0019.accepted Panels0019.integerPanels Panels0019.aligned
    Panels0019.weightRows Panels0019.weights_checked ⟨1, by decide⟩
def b0020 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0020.block Panels0020.accepted Panels0020.integerPanels Panels0020.aligned
    Panels0020.weightRows Panels0020.weights_checked ⟨1, by decide⟩
def b0021 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0021.block Panels0021.accepted Panels0021.integerPanels Panels0021.aligned
    Panels0021.weightRows Panels0021.weights_checked ⟨1, by decide⟩
def b0022 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0022.block Panels0022.accepted Panels0022.integerPanels Panels0022.aligned
    Panels0022.weightRows Panels0022.weights_checked ⟨1, by decide⟩
def b0023 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0023.block Panels0023.accepted Panels0023.integerPanels Panels0023.aligned
    Panels0023.weightRows Panels0023.weights_checked ⟨1, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0016, b0017, b0018, b0019, b0020, b0021, b0022, b0023]
theorem chain_checked : blockChainCheck (16404185673485123870434928473/10^30) (21062748655537829836560893631/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row01
namespace Row02
abbrev ζ : ℚ := 153846153846153846153846153846/10^30
def b0016 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0016.block Panels0016.accepted Panels0016.integerPanels Panels0016.aligned
    Panels0016.weightRows Panels0016.weights_checked ⟨2, by decide⟩
def b0017 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0017.block Panels0017.accepted Panels0017.integerPanels Panels0017.aligned
    Panels0017.weightRows Panels0017.weights_checked ⟨2, by decide⟩
def b0018 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0018.block Panels0018.accepted Panels0018.integerPanels Panels0018.aligned
    Panels0018.weightRows Panels0018.weights_checked ⟨2, by decide⟩
def b0019 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0019.block Panels0019.accepted Panels0019.integerPanels Panels0019.aligned
    Panels0019.weightRows Panels0019.weights_checked ⟨2, by decide⟩
def b0020 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0020.block Panels0020.accepted Panels0020.integerPanels Panels0020.aligned
    Panels0020.weightRows Panels0020.weights_checked ⟨2, by decide⟩
def b0021 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0021.block Panels0021.accepted Panels0021.integerPanels Panels0021.aligned
    Panels0021.weightRows Panels0021.weights_checked ⟨2, by decide⟩
def b0022 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0022.block Panels0022.accepted Panels0022.integerPanels Panels0022.aligned
    Panels0022.weightRows Panels0022.weights_checked ⟨2, by decide⟩
def b0023 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0023.block Panels0023.accepted Panels0023.integerPanels Panels0023.aligned
    Panels0023.weightRows Panels0023.weights_checked ⟨2, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0016, b0017, b0018, b0019, b0020, b0021, b0022, b0023]
theorem chain_checked : blockChainCheck (16404185673485123870434928473/10^30) (21062748655537829836560893631/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row02
namespace Row03
abbrev ζ : ℚ := 117647058823529411764705882352/10^30
def b0016 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0016.block Panels0016.accepted Panels0016.integerPanels Panels0016.aligned
    Panels0016.weightRows Panels0016.weights_checked ⟨3, by decide⟩
def b0017 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0017.block Panels0017.accepted Panels0017.integerPanels Panels0017.aligned
    Panels0017.weightRows Panels0017.weights_checked ⟨3, by decide⟩
def b0018 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0018.block Panels0018.accepted Panels0018.integerPanels Panels0018.aligned
    Panels0018.weightRows Panels0018.weights_checked ⟨3, by decide⟩
def b0019 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0019.block Panels0019.accepted Panels0019.integerPanels Panels0019.aligned
    Panels0019.weightRows Panels0019.weights_checked ⟨3, by decide⟩
def b0020 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0020.block Panels0020.accepted Panels0020.integerPanels Panels0020.aligned
    Panels0020.weightRows Panels0020.weights_checked ⟨3, by decide⟩
def b0021 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0021.block Panels0021.accepted Panels0021.integerPanels Panels0021.aligned
    Panels0021.weightRows Panels0021.weights_checked ⟨3, by decide⟩
def b0022 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0022.block Panels0022.accepted Panels0022.integerPanels Panels0022.aligned
    Panels0022.weightRows Panels0022.weights_checked ⟨3, by decide⟩
def b0023 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0023.block Panels0023.accepted Panels0023.integerPanels Panels0023.aligned
    Panels0023.weightRows Panels0023.weights_checked ⟨3, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0016, b0017, b0018, b0019, b0020, b0021, b0022, b0023]
theorem chain_checked : blockChainCheck (16404185673485123870434928473/10^30) (21062748655537829836560893631/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row03
namespace Row04
abbrev ζ : ℚ := 86956521739130434782608695652/10^30
def b0016 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0016.block Panels0016.accepted Panels0016.integerPanels Panels0016.aligned
    Panels0016.weightRows Panels0016.weights_checked ⟨4, by decide⟩
def b0017 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0017.block Panels0017.accepted Panels0017.integerPanels Panels0017.aligned
    Panels0017.weightRows Panels0017.weights_checked ⟨4, by decide⟩
def b0018 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0018.block Panels0018.accepted Panels0018.integerPanels Panels0018.aligned
    Panels0018.weightRows Panels0018.weights_checked ⟨4, by decide⟩
def b0019 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0019.block Panels0019.accepted Panels0019.integerPanels Panels0019.aligned
    Panels0019.weightRows Panels0019.weights_checked ⟨4, by decide⟩
def b0020 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0020.block Panels0020.accepted Panels0020.integerPanels Panels0020.aligned
    Panels0020.weightRows Panels0020.weights_checked ⟨4, by decide⟩
def b0021 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0021.block Panels0021.accepted Panels0021.integerPanels Panels0021.aligned
    Panels0021.weightRows Panels0021.weights_checked ⟨4, by decide⟩
def b0022 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0022.block Panels0022.accepted Panels0022.integerPanels Panels0022.aligned
    Panels0022.weightRows Panels0022.weights_checked ⟨4, by decide⟩
def b0023 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0023.block Panels0023.accepted Panels0023.integerPanels Panels0023.aligned
    Panels0023.weightRows Panels0023.weights_checked ⟨4, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0016, b0017, b0018, b0019, b0020, b0021, b0022, b0023]
theorem chain_checked : blockChainCheck (16404185673485123870434928473/10^30) (21062748655537829836560893631/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row04
namespace Row05
abbrev ζ : ℚ := 64516129032258064516129032258/10^30
def b0016 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0016.block Panels0016.accepted Panels0016.integerPanels Panels0016.aligned
    Panels0016.weightRows Panels0016.weights_checked ⟨5, by decide⟩
def b0017 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0017.block Panels0017.accepted Panels0017.integerPanels Panels0017.aligned
    Panels0017.weightRows Panels0017.weights_checked ⟨5, by decide⟩
def b0018 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0018.block Panels0018.accepted Panels0018.integerPanels Panels0018.aligned
    Panels0018.weightRows Panels0018.weights_checked ⟨5, by decide⟩
def b0019 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0019.block Panels0019.accepted Panels0019.integerPanels Panels0019.aligned
    Panels0019.weightRows Panels0019.weights_checked ⟨5, by decide⟩
def b0020 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0020.block Panels0020.accepted Panels0020.integerPanels Panels0020.aligned
    Panels0020.weightRows Panels0020.weights_checked ⟨5, by decide⟩
def b0021 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0021.block Panels0021.accepted Panels0021.integerPanels Panels0021.aligned
    Panels0021.weightRows Panels0021.weights_checked ⟨5, by decide⟩
def b0022 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0022.block Panels0022.accepted Panels0022.integerPanels Panels0022.aligned
    Panels0022.weightRows Panels0022.weights_checked ⟨5, by decide⟩
def b0023 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0023.block Panels0023.accepted Panels0023.integerPanels Panels0023.aligned
    Panels0023.weightRows Panels0023.weights_checked ⟨5, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0016, b0017, b0018, b0019, b0020, b0021, b0022, b0023]
theorem chain_checked : blockChainCheck (16404185673485123870434928473/10^30) (21062748655537829836560893631/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row05
namespace Row06
abbrev ζ : ℚ := 46511627906976744186046511627/10^30
def b0016 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0016.block Panels0016.accepted Panels0016.integerPanels Panels0016.aligned
    Panels0016.weightRows Panels0016.weights_checked ⟨6, by decide⟩
def b0017 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0017.block Panels0017.accepted Panels0017.integerPanels Panels0017.aligned
    Panels0017.weightRows Panels0017.weights_checked ⟨6, by decide⟩
def b0018 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0018.block Panels0018.accepted Panels0018.integerPanels Panels0018.aligned
    Panels0018.weightRows Panels0018.weights_checked ⟨6, by decide⟩
def b0019 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0019.block Panels0019.accepted Panels0019.integerPanels Panels0019.aligned
    Panels0019.weightRows Panels0019.weights_checked ⟨6, by decide⟩
def b0020 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0020.block Panels0020.accepted Panels0020.integerPanels Panels0020.aligned
    Panels0020.weightRows Panels0020.weights_checked ⟨6, by decide⟩
def b0021 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0021.block Panels0021.accepted Panels0021.integerPanels Panels0021.aligned
    Panels0021.weightRows Panels0021.weights_checked ⟨6, by decide⟩
def b0022 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0022.block Panels0022.accepted Panels0022.integerPanels Panels0022.aligned
    Panels0022.weightRows Panels0022.weights_checked ⟨6, by decide⟩
def b0023 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0023.block Panels0023.accepted Panels0023.integerPanels Panels0023.aligned
    Panels0023.weightRows Panels0023.weights_checked ⟨6, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0016, b0017, b0018, b0019, b0020, b0021, b0022, b0023]
theorem chain_checked : blockChainCheck (16404185673485123870434928473/10^30) (21062748655537829836560893631/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row06
namespace Row07
abbrev ζ : ℚ := 33898305084745762711864406779/10^30
def b0016 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0016.block Panels0016.accepted Panels0016.integerPanels Panels0016.aligned
    Panels0016.weightRows Panels0016.weights_checked ⟨7, by decide⟩
def b0017 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0017.block Panels0017.accepted Panels0017.integerPanels Panels0017.aligned
    Panels0017.weightRows Panels0017.weights_checked ⟨7, by decide⟩
def b0018 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0018.block Panels0018.accepted Panels0018.integerPanels Panels0018.aligned
    Panels0018.weightRows Panels0018.weights_checked ⟨7, by decide⟩
def b0019 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0019.block Panels0019.accepted Panels0019.integerPanels Panels0019.aligned
    Panels0019.weightRows Panels0019.weights_checked ⟨7, by decide⟩
def b0020 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0020.block Panels0020.accepted Panels0020.integerPanels Panels0020.aligned
    Panels0020.weightRows Panels0020.weights_checked ⟨7, by decide⟩
def b0021 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0021.block Panels0021.accepted Panels0021.integerPanels Panels0021.aligned
    Panels0021.weightRows Panels0021.weights_checked ⟨7, by decide⟩
def b0022 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0022.block Panels0022.accepted Panels0022.integerPanels Panels0022.aligned
    Panels0022.weightRows Panels0022.weights_checked ⟨7, by decide⟩
def b0023 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0023.block Panels0023.accepted Panels0023.integerPanels Panels0023.aligned
    Panels0023.weightRows Panels0023.weights_checked ⟨7, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0016, b0017, b0018, b0019, b0020, b0021, b0022, b0023]
theorem chain_checked : blockChainCheck (16404185673485123870434928473/10^30) (21062748655537829836560893631/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row07
namespace Row08
abbrev ζ : ℚ := 25316455696202531645569620253/10^30
def b0016 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0016.block Panels0016.accepted Panels0016.integerPanels Panels0016.aligned
    Panels0016.weightRows Panels0016.weights_checked ⟨8, by decide⟩
def b0017 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0017.block Panels0017.accepted Panels0017.integerPanels Panels0017.aligned
    Panels0017.weightRows Panels0017.weights_checked ⟨8, by decide⟩
def b0018 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0018.block Panels0018.accepted Panels0018.integerPanels Panels0018.aligned
    Panels0018.weightRows Panels0018.weights_checked ⟨8, by decide⟩
def b0019 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0019.block Panels0019.accepted Panels0019.integerPanels Panels0019.aligned
    Panels0019.weightRows Panels0019.weights_checked ⟨8, by decide⟩
def b0020 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0020.block Panels0020.accepted Panels0020.integerPanels Panels0020.aligned
    Panels0020.weightRows Panels0020.weights_checked ⟨8, by decide⟩
def b0021 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0021.block Panels0021.accepted Panels0021.integerPanels Panels0021.aligned
    Panels0021.weightRows Panels0021.weights_checked ⟨8, by decide⟩
def b0022 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0022.block Panels0022.accepted Panels0022.integerPanels Panels0022.aligned
    Panels0022.weightRows Panels0022.weights_checked ⟨8, by decide⟩
def b0023 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0023.block Panels0023.accepted Panels0023.integerPanels Panels0023.aligned
    Panels0023.weightRows Panels0023.weights_checked ⟨8, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0016, b0017, b0018, b0019, b0020, b0021, b0022, b0023]
theorem chain_checked : blockChainCheck (16404185673485123870434928473/10^30) (21062748655537829836560893631/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row08
namespace Row09
abbrev ζ : ℚ := 18691588785046728971962616822/10^30
def b0016 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0016.block Panels0016.accepted Panels0016.integerPanels Panels0016.aligned
    Panels0016.weightRows Panels0016.weights_checked ⟨9, by decide⟩
def b0017 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0017.block Panels0017.accepted Panels0017.integerPanels Panels0017.aligned
    Panels0017.weightRows Panels0017.weights_checked ⟨9, by decide⟩
def b0018 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0018.block Panels0018.accepted Panels0018.integerPanels Panels0018.aligned
    Panels0018.weightRows Panels0018.weights_checked ⟨9, by decide⟩
def b0019 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0019.block Panels0019.accepted Panels0019.integerPanels Panels0019.aligned
    Panels0019.weightRows Panels0019.weights_checked ⟨9, by decide⟩
def b0020 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0020.block Panels0020.accepted Panels0020.integerPanels Panels0020.aligned
    Panels0020.weightRows Panels0020.weights_checked ⟨9, by decide⟩
def b0021 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0021.block Panels0021.accepted Panels0021.integerPanels Panels0021.aligned
    Panels0021.weightRows Panels0021.weights_checked ⟨9, by decide⟩
def b0022 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0022.block Panels0022.accepted Panels0022.integerPanels Panels0022.aligned
    Panels0022.weightRows Panels0022.weights_checked ⟨9, by decide⟩
def b0023 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0023.block Panels0023.accepted Panels0023.integerPanels Panels0023.aligned
    Panels0023.weightRows Panels0023.weights_checked ⟨9, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0016, b0017, b0018, b0019, b0020, b0021, b0022, b0023]
theorem chain_checked : blockChainCheck (16404185673485123870434928473/10^30) (21062748655537829836560893631/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=2168017338110909473937750698524188337647274193857777618321170329422228363508065376110461239894665756410787008240934768786687195690194294705990178346760317609564046645932792869562937619579728620603353775446666/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row09
namespace Row10
abbrev ζ : ℚ := 13793103448275862068965517241/10^30
def b0016 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0016.block Panels0016.accepted Panels0016.integerPanels Panels0016.aligned
    Panels0016.weightRows Panels0016.weights_checked ⟨10, by decide⟩
def b0017 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0017.block Panels0017.accepted Panels0017.integerPanels Panels0017.aligned
    Panels0017.weightRows Panels0017.weights_checked ⟨10, by decide⟩
def b0018 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0018.block Panels0018.accepted Panels0018.integerPanels Panels0018.aligned
    Panels0018.weightRows Panels0018.weights_checked ⟨10, by decide⟩
def b0019 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0019.block Panels0019.accepted Panels0019.integerPanels Panels0019.aligned
    Panels0019.weightRows Panels0019.weights_checked ⟨10, by decide⟩
def b0020 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0020.block Panels0020.accepted Panels0020.integerPanels Panels0020.aligned
    Panels0020.weightRows Panels0020.weights_checked ⟨10, by decide⟩
def b0021 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0021.block Panels0021.accepted Panels0021.integerPanels Panels0021.aligned
    Panels0021.weightRows Panels0021.weights_checked ⟨10, by decide⟩
def b0022 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0022.block Panels0022.accepted Panels0022.integerPanels Panels0022.aligned
    Panels0022.weightRows Panels0022.weights_checked ⟨10, by decide⟩
def b0023 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0023.block Panels0023.accepted Panels0023.integerPanels Panels0023.aligned
    Panels0023.weightRows Panels0023.weights_checked ⟨10, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0016, b0017, b0018, b0019, b0020, b0021, b0022, b0023]
theorem chain_checked : blockChainCheck (16404185673485123870434928473/10^30) (21062748655537829836560893631/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=2299406939352415917191472098315218652235756581231960237517920267362985914092756788753252354630986780563628731079727381724975296162115280174356006047688533331805927195501625183997593794413600384093379119774938406/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row10
namespace Row11
abbrev ζ : ℚ := 10152284263959390862944162436/10^30
def b0016 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0016.block Panels0016.accepted Panels0016.integerPanels Panels0016.aligned
    Panels0016.weightRows Panels0016.weights_checked ⟨11, by decide⟩
def b0017 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0017.block Panels0017.accepted Panels0017.integerPanels Panels0017.aligned
    Panels0017.weightRows Panels0017.weights_checked ⟨11, by decide⟩
def b0018 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0018.block Panels0018.accepted Panels0018.integerPanels Panels0018.aligned
    Panels0018.weightRows Panels0018.weights_checked ⟨11, by decide⟩
def b0019 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0019.block Panels0019.accepted Panels0019.integerPanels Panels0019.aligned
    Panels0019.weightRows Panels0019.weights_checked ⟨11, by decide⟩
def b0020 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0020.block Panels0020.accepted Panels0020.integerPanels Panels0020.aligned
    Panels0020.weightRows Panels0020.weights_checked ⟨11, by decide⟩
def b0021 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0021.block Panels0021.accepted Panels0021.integerPanels Panels0021.aligned
    Panels0021.weightRows Panels0021.weights_checked ⟨11, by decide⟩
def b0022 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0022.block Panels0022.accepted Panels0022.integerPanels Panels0022.aligned
    Panels0022.weightRows Panels0022.weights_checked ⟨11, by decide⟩
def b0023 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0023.block Panels0023.accepted Panels0023.integerPanels Panels0023.aligned
    Panels0023.weightRows Panels0023.weights_checked ⟨11, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0016, b0017, b0018, b0019, b0020, b0021, b0022, b0023]
theorem chain_checked : blockChainCheck (16404185673485123870434928473/10^30) (21062748655537829836560893631/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=29428661846366724412586834748341651341849993081748176792502620740823283236605402380498576194711003418880807708924625371258167752511558656617669716855667027689898805016655839033354499844118015565146397581038732986/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row11
namespace Row12
abbrev ζ : ℚ := 9950248756218905472636815920/10^30
def b0016 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0016.block Panels0016.accepted Panels0016.integerPanels Panels0016.aligned
    Panels0016.weightRows Panels0016.weights_checked ⟨12, by decide⟩
def b0017 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0017.block Panels0017.accepted Panels0017.integerPanels Panels0017.aligned
    Panels0017.weightRows Panels0017.weights_checked ⟨12, by decide⟩
def b0018 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0018.block Panels0018.accepted Panels0018.integerPanels Panels0018.aligned
    Panels0018.weightRows Panels0018.weights_checked ⟨12, by decide⟩
def b0019 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0019.block Panels0019.accepted Panels0019.integerPanels Panels0019.aligned
    Panels0019.weightRows Panels0019.weights_checked ⟨12, by decide⟩
def b0020 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0020.block Panels0020.accepted Panels0020.integerPanels Panels0020.aligned
    Panels0020.weightRows Panels0020.weights_checked ⟨12, by decide⟩
def b0021 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0021.block Panels0021.accepted Panels0021.integerPanels Panels0021.aligned
    Panels0021.weightRows Panels0021.weights_checked ⟨12, by decide⟩
def b0022 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0022.block Panels0022.accepted Panels0022.integerPanels Panels0022.aligned
    Panels0022.weightRows Panels0022.weights_checked ⟨12, by decide⟩
def b0023 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0023.block Panels0023.accepted Panels0023.integerPanels Panels0023.aligned
    Panels0023.weightRows Panels0023.weights_checked ⟨12, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0016, b0017, b0018, b0019, b0020, b0021, b0022, b0023]
theorem chain_checked : blockChainCheck (16404185673485123870434928473/10^30) (21062748655537829836560893631/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=32950185019454569450702078364858025465139150907934026480475116674033013854552148076028498994553148206994149538093790784975715469278936898552287347978290472283027017477889214912667003113015498992194379493656754298/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row12
#print axioms Row12.segment
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments002
