module

public import BecknerOnofri.EntropyHeatCheckedWeights
public import BecknerOnofri.EntropyHeatSegments
public import BecknerOnofri.EntropyHeatCertificate.Panels0024
public import BecknerOnofri.EntropyHeatCertificate.Panels0025
public import BecknerOnofri.EntropyHeatCertificate.Panels0026
public import BecknerOnofri.EntropyHeatCertificate.Panels0027
public import BecknerOnofri.EntropyHeatCertificate.Panels0028
public import BecknerOnofri.EntropyHeatCertificate.Panels0029
public import BecknerOnofri.EntropyHeatCertificate.Panels0030
public import BecknerOnofri.EntropyHeatCertificate.Panels0031

@[expose] public section
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments003
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace Row00
abbrev ζ : ℚ := 285714285714285714285714285714/10^30
def b0024 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0024.block Panels0024.accepted Panels0024.integerPanels Panels0024.aligned
    Panels0024.weightRows Panels0024.weights_checked ⟨0, by decide⟩
def b0025 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0025.block Panels0025.accepted Panels0025.integerPanels Panels0025.aligned
    Panels0025.weightRows Panels0025.weights_checked ⟨0, by decide⟩
def b0026 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0026.block Panels0026.accepted Panels0026.integerPanels Panels0026.aligned
    Panels0026.weightRows Panels0026.weights_checked ⟨0, by decide⟩
def b0027 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0027.block Panels0027.accepted Panels0027.integerPanels Panels0027.aligned
    Panels0027.weightRows Panels0027.weights_checked ⟨0, by decide⟩
def b0028 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0028.block Panels0028.accepted Panels0028.integerPanels Panels0028.aligned
    Panels0028.weightRows Panels0028.weights_checked ⟨0, by decide⟩
def b0029 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0029.block Panels0029.accepted Panels0029.integerPanels Panels0029.aligned
    Panels0029.weightRows Panels0029.weights_checked ⟨0, by decide⟩
def b0030 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0030.block Panels0030.accepted Panels0030.integerPanels Panels0030.aligned
    Panels0030.weightRows Panels0030.weights_checked ⟨0, by decide⟩
def b0031 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0031.block Panels0031.accepted Panels0031.integerPanels Panels0031.aligned
    Panels0031.weightRows Panels0031.weights_checked ⟨0, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0024, b0025, b0026, b0027, b0028, b0029, b0030, b0031]
theorem chain_checked : blockChainCheck (21062748655537829836560893631/10^30) (27044279414822545995436962674/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row00
namespace Row01
abbrev ζ : ℚ := 222222222222222222222222222222/10^30
def b0024 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0024.block Panels0024.accepted Panels0024.integerPanels Panels0024.aligned
    Panels0024.weightRows Panels0024.weights_checked ⟨1, by decide⟩
def b0025 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0025.block Panels0025.accepted Panels0025.integerPanels Panels0025.aligned
    Panels0025.weightRows Panels0025.weights_checked ⟨1, by decide⟩
def b0026 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0026.block Panels0026.accepted Panels0026.integerPanels Panels0026.aligned
    Panels0026.weightRows Panels0026.weights_checked ⟨1, by decide⟩
def b0027 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0027.block Panels0027.accepted Panels0027.integerPanels Panels0027.aligned
    Panels0027.weightRows Panels0027.weights_checked ⟨1, by decide⟩
def b0028 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0028.block Panels0028.accepted Panels0028.integerPanels Panels0028.aligned
    Panels0028.weightRows Panels0028.weights_checked ⟨1, by decide⟩
def b0029 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0029.block Panels0029.accepted Panels0029.integerPanels Panels0029.aligned
    Panels0029.weightRows Panels0029.weights_checked ⟨1, by decide⟩
def b0030 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0030.block Panels0030.accepted Panels0030.integerPanels Panels0030.aligned
    Panels0030.weightRows Panels0030.weights_checked ⟨1, by decide⟩
def b0031 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0031.block Panels0031.accepted Panels0031.integerPanels Panels0031.aligned
    Panels0031.weightRows Panels0031.weights_checked ⟨1, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0024, b0025, b0026, b0027, b0028, b0029, b0030, b0031]
theorem chain_checked : blockChainCheck (21062748655537829836560893631/10^30) (27044279414822545995436962674/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row01
namespace Row02
abbrev ζ : ℚ := 153846153846153846153846153846/10^30
def b0024 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0024.block Panels0024.accepted Panels0024.integerPanels Panels0024.aligned
    Panels0024.weightRows Panels0024.weights_checked ⟨2, by decide⟩
def b0025 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0025.block Panels0025.accepted Panels0025.integerPanels Panels0025.aligned
    Panels0025.weightRows Panels0025.weights_checked ⟨2, by decide⟩
def b0026 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0026.block Panels0026.accepted Panels0026.integerPanels Panels0026.aligned
    Panels0026.weightRows Panels0026.weights_checked ⟨2, by decide⟩
def b0027 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0027.block Panels0027.accepted Panels0027.integerPanels Panels0027.aligned
    Panels0027.weightRows Panels0027.weights_checked ⟨2, by decide⟩
def b0028 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0028.block Panels0028.accepted Panels0028.integerPanels Panels0028.aligned
    Panels0028.weightRows Panels0028.weights_checked ⟨2, by decide⟩
def b0029 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0029.block Panels0029.accepted Panels0029.integerPanels Panels0029.aligned
    Panels0029.weightRows Panels0029.weights_checked ⟨2, by decide⟩
def b0030 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0030.block Panels0030.accepted Panels0030.integerPanels Panels0030.aligned
    Panels0030.weightRows Panels0030.weights_checked ⟨2, by decide⟩
def b0031 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0031.block Panels0031.accepted Panels0031.integerPanels Panels0031.aligned
    Panels0031.weightRows Panels0031.weights_checked ⟨2, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0024, b0025, b0026, b0027, b0028, b0029, b0030, b0031]
theorem chain_checked : blockChainCheck (21062748655537829836560893631/10^30) (27044279414822545995436962674/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row02
namespace Row03
abbrev ζ : ℚ := 117647058823529411764705882352/10^30
def b0024 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0024.block Panels0024.accepted Panels0024.integerPanels Panels0024.aligned
    Panels0024.weightRows Panels0024.weights_checked ⟨3, by decide⟩
def b0025 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0025.block Panels0025.accepted Panels0025.integerPanels Panels0025.aligned
    Panels0025.weightRows Panels0025.weights_checked ⟨3, by decide⟩
def b0026 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0026.block Panels0026.accepted Panels0026.integerPanels Panels0026.aligned
    Panels0026.weightRows Panels0026.weights_checked ⟨3, by decide⟩
def b0027 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0027.block Panels0027.accepted Panels0027.integerPanels Panels0027.aligned
    Panels0027.weightRows Panels0027.weights_checked ⟨3, by decide⟩
def b0028 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0028.block Panels0028.accepted Panels0028.integerPanels Panels0028.aligned
    Panels0028.weightRows Panels0028.weights_checked ⟨3, by decide⟩
def b0029 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0029.block Panels0029.accepted Panels0029.integerPanels Panels0029.aligned
    Panels0029.weightRows Panels0029.weights_checked ⟨3, by decide⟩
def b0030 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0030.block Panels0030.accepted Panels0030.integerPanels Panels0030.aligned
    Panels0030.weightRows Panels0030.weights_checked ⟨3, by decide⟩
def b0031 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0031.block Panels0031.accepted Panels0031.integerPanels Panels0031.aligned
    Panels0031.weightRows Panels0031.weights_checked ⟨3, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0024, b0025, b0026, b0027, b0028, b0029, b0030, b0031]
theorem chain_checked : blockChainCheck (21062748655537829836560893631/10^30) (27044279414822545995436962674/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row03
namespace Row04
abbrev ζ : ℚ := 86956521739130434782608695652/10^30
def b0024 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0024.block Panels0024.accepted Panels0024.integerPanels Panels0024.aligned
    Panels0024.weightRows Panels0024.weights_checked ⟨4, by decide⟩
def b0025 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0025.block Panels0025.accepted Panels0025.integerPanels Panels0025.aligned
    Panels0025.weightRows Panels0025.weights_checked ⟨4, by decide⟩
def b0026 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0026.block Panels0026.accepted Panels0026.integerPanels Panels0026.aligned
    Panels0026.weightRows Panels0026.weights_checked ⟨4, by decide⟩
def b0027 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0027.block Panels0027.accepted Panels0027.integerPanels Panels0027.aligned
    Panels0027.weightRows Panels0027.weights_checked ⟨4, by decide⟩
def b0028 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0028.block Panels0028.accepted Panels0028.integerPanels Panels0028.aligned
    Panels0028.weightRows Panels0028.weights_checked ⟨4, by decide⟩
def b0029 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0029.block Panels0029.accepted Panels0029.integerPanels Panels0029.aligned
    Panels0029.weightRows Panels0029.weights_checked ⟨4, by decide⟩
def b0030 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0030.block Panels0030.accepted Panels0030.integerPanels Panels0030.aligned
    Panels0030.weightRows Panels0030.weights_checked ⟨4, by decide⟩
def b0031 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0031.block Panels0031.accepted Panels0031.integerPanels Panels0031.aligned
    Panels0031.weightRows Panels0031.weights_checked ⟨4, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0024, b0025, b0026, b0027, b0028, b0029, b0030, b0031]
theorem chain_checked : blockChainCheck (21062748655537829836560893631/10^30) (27044279414822545995436962674/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row04
namespace Row05
abbrev ζ : ℚ := 64516129032258064516129032258/10^30
def b0024 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0024.block Panels0024.accepted Panels0024.integerPanels Panels0024.aligned
    Panels0024.weightRows Panels0024.weights_checked ⟨5, by decide⟩
def b0025 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0025.block Panels0025.accepted Panels0025.integerPanels Panels0025.aligned
    Panels0025.weightRows Panels0025.weights_checked ⟨5, by decide⟩
def b0026 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0026.block Panels0026.accepted Panels0026.integerPanels Panels0026.aligned
    Panels0026.weightRows Panels0026.weights_checked ⟨5, by decide⟩
def b0027 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0027.block Panels0027.accepted Panels0027.integerPanels Panels0027.aligned
    Panels0027.weightRows Panels0027.weights_checked ⟨5, by decide⟩
def b0028 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0028.block Panels0028.accepted Panels0028.integerPanels Panels0028.aligned
    Panels0028.weightRows Panels0028.weights_checked ⟨5, by decide⟩
def b0029 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0029.block Panels0029.accepted Panels0029.integerPanels Panels0029.aligned
    Panels0029.weightRows Panels0029.weights_checked ⟨5, by decide⟩
def b0030 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0030.block Panels0030.accepted Panels0030.integerPanels Panels0030.aligned
    Panels0030.weightRows Panels0030.weights_checked ⟨5, by decide⟩
def b0031 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0031.block Panels0031.accepted Panels0031.integerPanels Panels0031.aligned
    Panels0031.weightRows Panels0031.weights_checked ⟨5, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0024, b0025, b0026, b0027, b0028, b0029, b0030, b0031]
theorem chain_checked : blockChainCheck (21062748655537829836560893631/10^30) (27044279414822545995436962674/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row05
namespace Row06
abbrev ζ : ℚ := 46511627906976744186046511627/10^30
def b0024 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0024.block Panels0024.accepted Panels0024.integerPanels Panels0024.aligned
    Panels0024.weightRows Panels0024.weights_checked ⟨6, by decide⟩
def b0025 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0025.block Panels0025.accepted Panels0025.integerPanels Panels0025.aligned
    Panels0025.weightRows Panels0025.weights_checked ⟨6, by decide⟩
def b0026 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0026.block Panels0026.accepted Panels0026.integerPanels Panels0026.aligned
    Panels0026.weightRows Panels0026.weights_checked ⟨6, by decide⟩
def b0027 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0027.block Panels0027.accepted Panels0027.integerPanels Panels0027.aligned
    Panels0027.weightRows Panels0027.weights_checked ⟨6, by decide⟩
def b0028 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0028.block Panels0028.accepted Panels0028.integerPanels Panels0028.aligned
    Panels0028.weightRows Panels0028.weights_checked ⟨6, by decide⟩
def b0029 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0029.block Panels0029.accepted Panels0029.integerPanels Panels0029.aligned
    Panels0029.weightRows Panels0029.weights_checked ⟨6, by decide⟩
def b0030 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0030.block Panels0030.accepted Panels0030.integerPanels Panels0030.aligned
    Panels0030.weightRows Panels0030.weights_checked ⟨6, by decide⟩
def b0031 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0031.block Panels0031.accepted Panels0031.integerPanels Panels0031.aligned
    Panels0031.weightRows Panels0031.weights_checked ⟨6, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0024, b0025, b0026, b0027, b0028, b0029, b0030, b0031]
theorem chain_checked : blockChainCheck (21062748655537829836560893631/10^30) (27044279414822545995436962674/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row06
namespace Row07
abbrev ζ : ℚ := 33898305084745762711864406779/10^30
def b0024 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0024.block Panels0024.accepted Panels0024.integerPanels Panels0024.aligned
    Panels0024.weightRows Panels0024.weights_checked ⟨7, by decide⟩
def b0025 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0025.block Panels0025.accepted Panels0025.integerPanels Panels0025.aligned
    Panels0025.weightRows Panels0025.weights_checked ⟨7, by decide⟩
def b0026 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0026.block Panels0026.accepted Panels0026.integerPanels Panels0026.aligned
    Panels0026.weightRows Panels0026.weights_checked ⟨7, by decide⟩
def b0027 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0027.block Panels0027.accepted Panels0027.integerPanels Panels0027.aligned
    Panels0027.weightRows Panels0027.weights_checked ⟨7, by decide⟩
def b0028 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0028.block Panels0028.accepted Panels0028.integerPanels Panels0028.aligned
    Panels0028.weightRows Panels0028.weights_checked ⟨7, by decide⟩
def b0029 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0029.block Panels0029.accepted Panels0029.integerPanels Panels0029.aligned
    Panels0029.weightRows Panels0029.weights_checked ⟨7, by decide⟩
def b0030 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0030.block Panels0030.accepted Panels0030.integerPanels Panels0030.aligned
    Panels0030.weightRows Panels0030.weights_checked ⟨7, by decide⟩
def b0031 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0031.block Panels0031.accepted Panels0031.integerPanels Panels0031.aligned
    Panels0031.weightRows Panels0031.weights_checked ⟨7, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0024, b0025, b0026, b0027, b0028, b0029, b0030, b0031]
theorem chain_checked : blockChainCheck (21062748655537829836560893631/10^30) (27044279414822545995436962674/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row07
namespace Row08
abbrev ζ : ℚ := 25316455696202531645569620253/10^30
def b0024 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0024.block Panels0024.accepted Panels0024.integerPanels Panels0024.aligned
    Panels0024.weightRows Panels0024.weights_checked ⟨8, by decide⟩
def b0025 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0025.block Panels0025.accepted Panels0025.integerPanels Panels0025.aligned
    Panels0025.weightRows Panels0025.weights_checked ⟨8, by decide⟩
def b0026 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0026.block Panels0026.accepted Panels0026.integerPanels Panels0026.aligned
    Panels0026.weightRows Panels0026.weights_checked ⟨8, by decide⟩
def b0027 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0027.block Panels0027.accepted Panels0027.integerPanels Panels0027.aligned
    Panels0027.weightRows Panels0027.weights_checked ⟨8, by decide⟩
def b0028 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0028.block Panels0028.accepted Panels0028.integerPanels Panels0028.aligned
    Panels0028.weightRows Panels0028.weights_checked ⟨8, by decide⟩
def b0029 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0029.block Panels0029.accepted Panels0029.integerPanels Panels0029.aligned
    Panels0029.weightRows Panels0029.weights_checked ⟨8, by decide⟩
def b0030 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0030.block Panels0030.accepted Panels0030.integerPanels Panels0030.aligned
    Panels0030.weightRows Panels0030.weights_checked ⟨8, by decide⟩
def b0031 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0031.block Panels0031.accepted Panels0031.integerPanels Panels0031.aligned
    Panels0031.weightRows Panels0031.weights_checked ⟨8, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0024, b0025, b0026, b0027, b0028, b0029, b0030, b0031]
theorem chain_checked : blockChainCheck (21062748655537829836560893631/10^30) (27044279414822545995436962674/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=69223134498150199532529108736234227315078171326789230079976353031313071934221243384658954286681735618204290760286465067877284363816944237665832417827717441246332531111643862549705747085841498194172981533210/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row08
namespace Row09
abbrev ζ : ℚ := 18691588785046728971962616822/10^30
def b0024 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0024.block Panels0024.accepted Panels0024.integerPanels Panels0024.aligned
    Panels0024.weightRows Panels0024.weights_checked ⟨9, by decide⟩
def b0025 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0025.block Panels0025.accepted Panels0025.integerPanels Panels0025.aligned
    Panels0025.weightRows Panels0025.weights_checked ⟨9, by decide⟩
def b0026 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0026.block Panels0026.accepted Panels0026.integerPanels Panels0026.aligned
    Panels0026.weightRows Panels0026.weights_checked ⟨9, by decide⟩
def b0027 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0027.block Panels0027.accepted Panels0027.integerPanels Panels0027.aligned
    Panels0027.weightRows Panels0027.weights_checked ⟨9, by decide⟩
def b0028 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0028.block Panels0028.accepted Panels0028.integerPanels Panels0028.aligned
    Panels0028.weightRows Panels0028.weights_checked ⟨9, by decide⟩
def b0029 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0029.block Panels0029.accepted Panels0029.integerPanels Panels0029.aligned
    Panels0029.weightRows Panels0029.weights_checked ⟨9, by decide⟩
def b0030 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0030.block Panels0030.accepted Panels0030.integerPanels Panels0030.aligned
    Panels0030.weightRows Panels0030.weights_checked ⟨9, by decide⟩
def b0031 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0031.block Panels0031.accepted Panels0031.integerPanels Panels0031.aligned
    Panels0031.weightRows Panels0031.weights_checked ⟨9, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0024, b0025, b0026, b0027, b0028, b0029, b0030, b0031]
theorem chain_checked : blockChainCheck (21062748655537829836560893631/10^30) (27044279414822545995436962674/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=1136462765925519824581561708861132861037646808362305216051841800870745121023459285256782473876060375564352723912476219783647465821791353138304358356319025319726870801819221655694814690242354332422811353995097025/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row09
namespace Row10
abbrev ζ : ℚ := 13793103448275862068965517241/10^30
def b0024 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0024.block Panels0024.accepted Panels0024.integerPanels Panels0024.aligned
    Panels0024.weightRows Panels0024.weights_checked ⟨10, by decide⟩
def b0025 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0025.block Panels0025.accepted Panels0025.integerPanels Panels0025.aligned
    Panels0025.weightRows Panels0025.weights_checked ⟨10, by decide⟩
def b0026 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0026.block Panels0026.accepted Panels0026.integerPanels Panels0026.aligned
    Panels0026.weightRows Panels0026.weights_checked ⟨10, by decide⟩
def b0027 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0027.block Panels0027.accepted Panels0027.integerPanels Panels0027.aligned
    Panels0027.weightRows Panels0027.weights_checked ⟨10, by decide⟩
def b0028 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0028.block Panels0028.accepted Panels0028.integerPanels Panels0028.aligned
    Panels0028.weightRows Panels0028.weights_checked ⟨10, by decide⟩
def b0029 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0029.block Panels0029.accepted Panels0029.integerPanels Panels0029.aligned
    Panels0029.weightRows Panels0029.weights_checked ⟨10, by decide⟩
def b0030 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0030.block Panels0030.accepted Panels0030.integerPanels Panels0030.aligned
    Panels0030.weightRows Panels0030.weights_checked ⟨10, by decide⟩
def b0031 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0031.block Panels0031.accepted Panels0031.integerPanels Panels0031.aligned
    Panels0031.weightRows Panels0031.weights_checked ⟨10, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0024, b0025, b0026, b0027, b0028, b0029, b0030, b0031]
theorem chain_checked : blockChainCheck (21062748655537829836560893631/10^30) (27044279414822545995436962674/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=20863029936992555528123168667352301536822713769798015867151378983043793655169949020056044204401831451612937854901051524769783008648012520401271369390211063374729348849622850522517074432506863300192081509121639375/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row10
namespace Row11
abbrev ζ : ℚ := 10152284263959390862944162436/10^30
def b0024 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0024.block Panels0024.accepted Panels0024.integerPanels Panels0024.aligned
    Panels0024.weightRows Panels0024.weights_checked ⟨11, by decide⟩
def b0025 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0025.block Panels0025.accepted Panels0025.integerPanels Panels0025.aligned
    Panels0025.weightRows Panels0025.weights_checked ⟨11, by decide⟩
def b0026 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0026.block Panels0026.accepted Panels0026.integerPanels Panels0026.aligned
    Panels0026.weightRows Panels0026.weights_checked ⟨11, by decide⟩
def b0027 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0027.block Panels0027.accepted Panels0027.integerPanels Panels0027.aligned
    Panels0027.weightRows Panels0027.weights_checked ⟨11, by decide⟩
def b0028 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0028.block Panels0028.accepted Panels0028.integerPanels Panels0028.aligned
    Panels0028.weightRows Panels0028.weights_checked ⟨11, by decide⟩
def b0029 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0029.block Panels0029.accepted Panels0029.integerPanels Panels0029.aligned
    Panels0029.weightRows Panels0029.weights_checked ⟨11, by decide⟩
def b0030 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0030.block Panels0030.accepted Panels0030.integerPanels Panels0030.aligned
    Panels0030.weightRows Panels0030.weights_checked ⟨11, by decide⟩
def b0031 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0031.block Panels0031.accepted Panels0031.integerPanels Panels0031.aligned
    Panels0031.weightRows Panels0031.weights_checked ⟨11, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0024, b0025, b0026, b0027, b0028, b0029, b0030, b0031]
theorem chain_checked : blockChainCheck (21062748655537829836560893631/10^30) (27044279414822545995436962674/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=92106260461452144026685129397384062184686846987585253701674942361681418109226287739057535781534443905461201549095169503762188193218879806690901544209114136654321626614002738127294530449592179622935114936846517825/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row11
namespace Row12
abbrev ζ : ℚ := 9950248756218905472636815920/10^30
def b0024 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0024.block Panels0024.accepted Panels0024.integerPanels Panels0024.aligned
    Panels0024.weightRows Panels0024.weights_checked ⟨12, by decide⟩
def b0025 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0025.block Panels0025.accepted Panels0025.integerPanels Panels0025.aligned
    Panels0025.weightRows Panels0025.weights_checked ⟨12, by decide⟩
def b0026 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0026.block Panels0026.accepted Panels0026.integerPanels Panels0026.aligned
    Panels0026.weightRows Panels0026.weights_checked ⟨12, by decide⟩
def b0027 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0027.block Panels0027.accepted Panels0027.integerPanels Panels0027.aligned
    Panels0027.weightRows Panels0027.weights_checked ⟨12, by decide⟩
def b0028 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0028.block Panels0028.accepted Panels0028.integerPanels Panels0028.aligned
    Panels0028.weightRows Panels0028.weights_checked ⟨12, by decide⟩
def b0029 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0029.block Panels0029.accepted Panels0029.integerPanels Panels0029.aligned
    Panels0029.weightRows Panels0029.weights_checked ⟨12, by decide⟩
def b0030 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0030.block Panels0030.accepted Panels0030.integerPanels Panels0030.aligned
    Panels0030.weightRows Panels0030.weights_checked ⟨12, by decide⟩
def b0031 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0031.block Panels0031.accepted Panels0031.integerPanels Panels0031.aligned
    Panels0031.weightRows Panels0031.weights_checked ⟨12, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0024, b0025, b0026, b0027, b0028, b0029, b0030, b0031]
theorem chain_checked : blockChainCheck (21062748655537829836560893631/10^30) (27044279414822545995436962674/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=98940127436081564618384366485024729607199729792750409836480523358416558756043135183132685675374411117681576309973201886340493649660987175458467563076378215714967377206837555825563981977578316263329575386104670825/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row12
#print axioms Row12.segment
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments003
