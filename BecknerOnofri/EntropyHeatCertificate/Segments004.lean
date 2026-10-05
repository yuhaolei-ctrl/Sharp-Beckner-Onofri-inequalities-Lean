module

public import BecknerOnofri.EntropyHeatCheckedWeights
public import BecknerOnofri.EntropyHeatSegments
public import BecknerOnofri.EntropyHeatCertificate.Panels0032
public import BecknerOnofri.EntropyHeatCertificate.Panels0033
public import BecknerOnofri.EntropyHeatCertificate.Panels0034
public import BecknerOnofri.EntropyHeatCertificate.Panels0035
public import BecknerOnofri.EntropyHeatCertificate.Panels0036
public import BecknerOnofri.EntropyHeatCertificate.Panels0037
public import BecknerOnofri.EntropyHeatCertificate.Panels0038
public import BecknerOnofri.EntropyHeatCertificate.Panels0039

@[expose] public section
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments004
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace Row00
abbrev ζ : ℚ := 285714285714285714285714285714/10^30
def b0032 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0032.block Panels0032.accepted Panels0032.integerPanels Panels0032.aligned
    Panels0032.weightRows Panels0032.weights_checked ⟨0, by decide⟩
def b0033 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0033.block Panels0033.accepted Panels0033.integerPanels Panels0033.aligned
    Panels0033.weightRows Panels0033.weights_checked ⟨0, by decide⟩
def b0034 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0034.block Panels0034.accepted Panels0034.integerPanels Panels0034.aligned
    Panels0034.weightRows Panels0034.weights_checked ⟨0, by decide⟩
def b0035 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0035.block Panels0035.accepted Panels0035.integerPanels Panels0035.aligned
    Panels0035.weightRows Panels0035.weights_checked ⟨0, by decide⟩
def b0036 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0036.block Panels0036.accepted Panels0036.integerPanels Panels0036.aligned
    Panels0036.weightRows Panels0036.weights_checked ⟨0, by decide⟩
def b0037 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0037.block Panels0037.accepted Panels0037.integerPanels Panels0037.aligned
    Panels0037.weightRows Panels0037.weights_checked ⟨0, by decide⟩
def b0038 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0038.block Panels0038.accepted Panels0038.integerPanels Panels0038.aligned
    Panels0038.weightRows Panels0038.weights_checked ⟨0, by decide⟩
def b0039 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0039.block Panels0039.accepted Panels0039.integerPanels Panels0039.aligned
    Panels0039.weightRows Panels0039.weights_checked ⟨0, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0032, b0033, b0034, b0035, b0036, b0037, b0038, b0039]
theorem chain_checked : blockChainCheck (27044279414822545995436962674/10^30) (34724482593808868107651770989/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row00
namespace Row01
abbrev ζ : ℚ := 222222222222222222222222222222/10^30
def b0032 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0032.block Panels0032.accepted Panels0032.integerPanels Panels0032.aligned
    Panels0032.weightRows Panels0032.weights_checked ⟨1, by decide⟩
def b0033 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0033.block Panels0033.accepted Panels0033.integerPanels Panels0033.aligned
    Panels0033.weightRows Panels0033.weights_checked ⟨1, by decide⟩
def b0034 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0034.block Panels0034.accepted Panels0034.integerPanels Panels0034.aligned
    Panels0034.weightRows Panels0034.weights_checked ⟨1, by decide⟩
def b0035 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0035.block Panels0035.accepted Panels0035.integerPanels Panels0035.aligned
    Panels0035.weightRows Panels0035.weights_checked ⟨1, by decide⟩
def b0036 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0036.block Panels0036.accepted Panels0036.integerPanels Panels0036.aligned
    Panels0036.weightRows Panels0036.weights_checked ⟨1, by decide⟩
def b0037 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0037.block Panels0037.accepted Panels0037.integerPanels Panels0037.aligned
    Panels0037.weightRows Panels0037.weights_checked ⟨1, by decide⟩
def b0038 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0038.block Panels0038.accepted Panels0038.integerPanels Panels0038.aligned
    Panels0038.weightRows Panels0038.weights_checked ⟨1, by decide⟩
def b0039 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0039.block Panels0039.accepted Panels0039.integerPanels Panels0039.aligned
    Panels0039.weightRows Panels0039.weights_checked ⟨1, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0032, b0033, b0034, b0035, b0036, b0037, b0038, b0039]
theorem chain_checked : blockChainCheck (27044279414822545995436962674/10^30) (34724482593808868107651770989/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row01
namespace Row02
abbrev ζ : ℚ := 153846153846153846153846153846/10^30
def b0032 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0032.block Panels0032.accepted Panels0032.integerPanels Panels0032.aligned
    Panels0032.weightRows Panels0032.weights_checked ⟨2, by decide⟩
def b0033 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0033.block Panels0033.accepted Panels0033.integerPanels Panels0033.aligned
    Panels0033.weightRows Panels0033.weights_checked ⟨2, by decide⟩
def b0034 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0034.block Panels0034.accepted Panels0034.integerPanels Panels0034.aligned
    Panels0034.weightRows Panels0034.weights_checked ⟨2, by decide⟩
def b0035 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0035.block Panels0035.accepted Panels0035.integerPanels Panels0035.aligned
    Panels0035.weightRows Panels0035.weights_checked ⟨2, by decide⟩
def b0036 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0036.block Panels0036.accepted Panels0036.integerPanels Panels0036.aligned
    Panels0036.weightRows Panels0036.weights_checked ⟨2, by decide⟩
def b0037 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0037.block Panels0037.accepted Panels0037.integerPanels Panels0037.aligned
    Panels0037.weightRows Panels0037.weights_checked ⟨2, by decide⟩
def b0038 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0038.block Panels0038.accepted Panels0038.integerPanels Panels0038.aligned
    Panels0038.weightRows Panels0038.weights_checked ⟨2, by decide⟩
def b0039 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0039.block Panels0039.accepted Panels0039.integerPanels Panels0039.aligned
    Panels0039.weightRows Panels0039.weights_checked ⟨2, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0032, b0033, b0034, b0035, b0036, b0037, b0038, b0039]
theorem chain_checked : blockChainCheck (27044279414822545995436962674/10^30) (34724482593808868107651770989/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row02
namespace Row03
abbrev ζ : ℚ := 117647058823529411764705882352/10^30
def b0032 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0032.block Panels0032.accepted Panels0032.integerPanels Panels0032.aligned
    Panels0032.weightRows Panels0032.weights_checked ⟨3, by decide⟩
def b0033 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0033.block Panels0033.accepted Panels0033.integerPanels Panels0033.aligned
    Panels0033.weightRows Panels0033.weights_checked ⟨3, by decide⟩
def b0034 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0034.block Panels0034.accepted Panels0034.integerPanels Panels0034.aligned
    Panels0034.weightRows Panels0034.weights_checked ⟨3, by decide⟩
def b0035 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0035.block Panels0035.accepted Panels0035.integerPanels Panels0035.aligned
    Panels0035.weightRows Panels0035.weights_checked ⟨3, by decide⟩
def b0036 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0036.block Panels0036.accepted Panels0036.integerPanels Panels0036.aligned
    Panels0036.weightRows Panels0036.weights_checked ⟨3, by decide⟩
def b0037 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0037.block Panels0037.accepted Panels0037.integerPanels Panels0037.aligned
    Panels0037.weightRows Panels0037.weights_checked ⟨3, by decide⟩
def b0038 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0038.block Panels0038.accepted Panels0038.integerPanels Panels0038.aligned
    Panels0038.weightRows Panels0038.weights_checked ⟨3, by decide⟩
def b0039 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0039.block Panels0039.accepted Panels0039.integerPanels Panels0039.aligned
    Panels0039.weightRows Panels0039.weights_checked ⟨3, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0032, b0033, b0034, b0035, b0036, b0037, b0038, b0039]
theorem chain_checked : blockChainCheck (27044279414822545995436962674/10^30) (34724482593808868107651770989/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row03
namespace Row04
abbrev ζ : ℚ := 86956521739130434782608695652/10^30
def b0032 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0032.block Panels0032.accepted Panels0032.integerPanels Panels0032.aligned
    Panels0032.weightRows Panels0032.weights_checked ⟨4, by decide⟩
def b0033 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0033.block Panels0033.accepted Panels0033.integerPanels Panels0033.aligned
    Panels0033.weightRows Panels0033.weights_checked ⟨4, by decide⟩
def b0034 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0034.block Panels0034.accepted Panels0034.integerPanels Panels0034.aligned
    Panels0034.weightRows Panels0034.weights_checked ⟨4, by decide⟩
def b0035 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0035.block Panels0035.accepted Panels0035.integerPanels Panels0035.aligned
    Panels0035.weightRows Panels0035.weights_checked ⟨4, by decide⟩
def b0036 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0036.block Panels0036.accepted Panels0036.integerPanels Panels0036.aligned
    Panels0036.weightRows Panels0036.weights_checked ⟨4, by decide⟩
def b0037 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0037.block Panels0037.accepted Panels0037.integerPanels Panels0037.aligned
    Panels0037.weightRows Panels0037.weights_checked ⟨4, by decide⟩
def b0038 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0038.block Panels0038.accepted Panels0038.integerPanels Panels0038.aligned
    Panels0038.weightRows Panels0038.weights_checked ⟨4, by decide⟩
def b0039 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0039.block Panels0039.accepted Panels0039.integerPanels Panels0039.aligned
    Panels0039.weightRows Panels0039.weights_checked ⟨4, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0032, b0033, b0034, b0035, b0036, b0037, b0038, b0039]
theorem chain_checked : blockChainCheck (27044279414822545995436962674/10^30) (34724482593808868107651770989/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row04
namespace Row05
abbrev ζ : ℚ := 64516129032258064516129032258/10^30
def b0032 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0032.block Panels0032.accepted Panels0032.integerPanels Panels0032.aligned
    Panels0032.weightRows Panels0032.weights_checked ⟨5, by decide⟩
def b0033 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0033.block Panels0033.accepted Panels0033.integerPanels Panels0033.aligned
    Panels0033.weightRows Panels0033.weights_checked ⟨5, by decide⟩
def b0034 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0034.block Panels0034.accepted Panels0034.integerPanels Panels0034.aligned
    Panels0034.weightRows Panels0034.weights_checked ⟨5, by decide⟩
def b0035 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0035.block Panels0035.accepted Panels0035.integerPanels Panels0035.aligned
    Panels0035.weightRows Panels0035.weights_checked ⟨5, by decide⟩
def b0036 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0036.block Panels0036.accepted Panels0036.integerPanels Panels0036.aligned
    Panels0036.weightRows Panels0036.weights_checked ⟨5, by decide⟩
def b0037 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0037.block Panels0037.accepted Panels0037.integerPanels Panels0037.aligned
    Panels0037.weightRows Panels0037.weights_checked ⟨5, by decide⟩
def b0038 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0038.block Panels0038.accepted Panels0038.integerPanels Panels0038.aligned
    Panels0038.weightRows Panels0038.weights_checked ⟨5, by decide⟩
def b0039 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0039.block Panels0039.accepted Panels0039.integerPanels Panels0039.aligned
    Panels0039.weightRows Panels0039.weights_checked ⟨5, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0032, b0033, b0034, b0035, b0036, b0037, b0038, b0039]
theorem chain_checked : blockChainCheck (27044279414822545995436962674/10^30) (34724482593808868107651770989/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row05
namespace Row06
abbrev ζ : ℚ := 46511627906976744186046511627/10^30
def b0032 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0032.block Panels0032.accepted Panels0032.integerPanels Panels0032.aligned
    Panels0032.weightRows Panels0032.weights_checked ⟨6, by decide⟩
def b0033 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0033.block Panels0033.accepted Panels0033.integerPanels Panels0033.aligned
    Panels0033.weightRows Panels0033.weights_checked ⟨6, by decide⟩
def b0034 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0034.block Panels0034.accepted Panels0034.integerPanels Panels0034.aligned
    Panels0034.weightRows Panels0034.weights_checked ⟨6, by decide⟩
def b0035 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0035.block Panels0035.accepted Panels0035.integerPanels Panels0035.aligned
    Panels0035.weightRows Panels0035.weights_checked ⟨6, by decide⟩
def b0036 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0036.block Panels0036.accepted Panels0036.integerPanels Panels0036.aligned
    Panels0036.weightRows Panels0036.weights_checked ⟨6, by decide⟩
def b0037 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0037.block Panels0037.accepted Panels0037.integerPanels Panels0037.aligned
    Panels0037.weightRows Panels0037.weights_checked ⟨6, by decide⟩
def b0038 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0038.block Panels0038.accepted Panels0038.integerPanels Panels0038.aligned
    Panels0038.weightRows Panels0038.weights_checked ⟨6, by decide⟩
def b0039 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0039.block Panels0039.accepted Panels0039.integerPanels Panels0039.aligned
    Panels0039.weightRows Panels0039.weights_checked ⟨6, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0032, b0033, b0034, b0035, b0036, b0037, b0038, b0039]
theorem chain_checked : blockChainCheck (27044279414822545995436962674/10^30) (34724482593808868107651770989/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row06
namespace Row07
abbrev ζ : ℚ := 33898305084745762711864406779/10^30
def b0032 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0032.block Panels0032.accepted Panels0032.integerPanels Panels0032.aligned
    Panels0032.weightRows Panels0032.weights_checked ⟨7, by decide⟩
def b0033 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0033.block Panels0033.accepted Panels0033.integerPanels Panels0033.aligned
    Panels0033.weightRows Panels0033.weights_checked ⟨7, by decide⟩
def b0034 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0034.block Panels0034.accepted Panels0034.integerPanels Panels0034.aligned
    Panels0034.weightRows Panels0034.weights_checked ⟨7, by decide⟩
def b0035 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0035.block Panels0035.accepted Panels0035.integerPanels Panels0035.aligned
    Panels0035.weightRows Panels0035.weights_checked ⟨7, by decide⟩
def b0036 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0036.block Panels0036.accepted Panels0036.integerPanels Panels0036.aligned
    Panels0036.weightRows Panels0036.weights_checked ⟨7, by decide⟩
def b0037 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0037.block Panels0037.accepted Panels0037.integerPanels Panels0037.aligned
    Panels0037.weightRows Panels0037.weights_checked ⟨7, by decide⟩
def b0038 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0038.block Panels0038.accepted Panels0038.integerPanels Panels0038.aligned
    Panels0038.weightRows Panels0038.weights_checked ⟨7, by decide⟩
def b0039 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0039.block Panels0039.accepted Panels0039.integerPanels Panels0039.aligned
    Panels0039.weightRows Panels0039.weights_checked ⟨7, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0032, b0033, b0034, b0035, b0036, b0037, b0038, b0039]
theorem chain_checked : blockChainCheck (27044279414822545995436962674/10^30) (34724482593808868107651770989/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=178154970159956302770864251004323221177849632429860584355110328073045720812188889831240149123496669260206997387323980173477820507857331578300933247656457461124061072236137245427729363591816359056766346848/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row07
namespace Row08
abbrev ζ : ℚ := 25316455696202531645569620253/10^30
def b0032 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0032.block Panels0032.accepted Panels0032.integerPanels Panels0032.aligned
    Panels0032.weightRows Panels0032.weights_checked ⟨8, by decide⟩
def b0033 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0033.block Panels0033.accepted Panels0033.integerPanels Panels0033.aligned
    Panels0033.weightRows Panels0033.weights_checked ⟨8, by decide⟩
def b0034 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0034.block Panels0034.accepted Panels0034.integerPanels Panels0034.aligned
    Panels0034.weightRows Panels0034.weights_checked ⟨8, by decide⟩
def b0035 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0035.block Panels0035.accepted Panels0035.integerPanels Panels0035.aligned
    Panels0035.weightRows Panels0035.weights_checked ⟨8, by decide⟩
def b0036 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0036.block Panels0036.accepted Panels0036.integerPanels Panels0036.aligned
    Panels0036.weightRows Panels0036.weights_checked ⟨8, by decide⟩
def b0037 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0037.block Panels0037.accepted Panels0037.integerPanels Panels0037.aligned
    Panels0037.weightRows Panels0037.weights_checked ⟨8, by decide⟩
def b0038 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0038.block Panels0038.accepted Panels0038.integerPanels Panels0038.aligned
    Panels0038.weightRows Panels0038.weights_checked ⟨8, by decide⟩
def b0039 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0039.block Panels0039.accepted Panels0039.integerPanels Panels0039.aligned
    Panels0039.weightRows Panels0039.weights_checked ⟨8, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0032, b0033, b0034, b0035, b0036, b0037, b0038, b0039]
theorem chain_checked : blockChainCheck (27044279414822545995436962674/10^30) (34724482593808868107651770989/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=496465053652569830212561790817468658708131351681063770895761118224542560505005244906794557693449828798340841997265719654818738684755072133757414335050445455863354546776015082634981862262266397376394879700384321/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row08
namespace Row09
abbrev ζ : ℚ := 18691588785046728971962616822/10^30
def b0032 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0032.block Panels0032.accepted Panels0032.integerPanels Panels0032.aligned
    Panels0032.weightRows Panels0032.weights_checked ⟨9, by decide⟩
def b0033 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0033.block Panels0033.accepted Panels0033.integerPanels Panels0033.aligned
    Panels0033.weightRows Panels0033.weights_checked ⟨9, by decide⟩
def b0034 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0034.block Panels0034.accepted Panels0034.integerPanels Panels0034.aligned
    Panels0034.weightRows Panels0034.weights_checked ⟨9, by decide⟩
def b0035 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0035.block Panels0035.accepted Panels0035.integerPanels Panels0035.aligned
    Panels0035.weightRows Panels0035.weights_checked ⟨9, by decide⟩
def b0036 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0036.block Panels0036.accepted Panels0036.integerPanels Panels0036.aligned
    Panels0036.weightRows Panels0036.weights_checked ⟨9, by decide⟩
def b0037 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0037.block Panels0037.accepted Panels0037.integerPanels Panels0037.aligned
    Panels0037.weightRows Panels0037.weights_checked ⟨9, by decide⟩
def b0038 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0038.block Panels0038.accepted Panels0038.integerPanels Panels0038.aligned
    Panels0038.weightRows Panels0038.weights_checked ⟨9, by decide⟩
def b0039 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0039.block Panels0039.accepted Panels0039.integerPanels Panels0039.aligned
    Panels0039.weightRows Panels0039.weights_checked ⟨9, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0032, b0033, b0034, b0035, b0036, b0037, b0038, b0039]
theorem chain_checked : blockChainCheck (27044279414822545995436962674/10^30) (34724482593808868107651770989/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=14413374386935725238224743742150297692278821355904168364090595153794315625140861875820593718590320309702470850578547651835872342502025609644803020420166707228849722724138491330004889249502571219274415867253234327/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row09
namespace Row10
abbrev ζ : ℚ := 13793103448275862068965517241/10^30
def b0032 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0032.block Panels0032.accepted Panels0032.integerPanels Panels0032.aligned
    Panels0032.weightRows Panels0032.weights_checked ⟨10, by decide⟩
def b0033 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0033.block Panels0033.accepted Panels0033.integerPanels Panels0033.aligned
    Panels0033.weightRows Panels0033.weights_checked ⟨10, by decide⟩
def b0034 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0034.block Panels0034.accepted Panels0034.integerPanels Panels0034.aligned
    Panels0034.weightRows Panels0034.weights_checked ⟨10, by decide⟩
def b0035 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0035.block Panels0035.accepted Panels0035.integerPanels Panels0035.aligned
    Panels0035.weightRows Panels0035.weights_checked ⟨10, by decide⟩
def b0036 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0036.block Panels0036.accepted Panels0036.integerPanels Panels0036.aligned
    Panels0036.weightRows Panels0036.weights_checked ⟨10, by decide⟩
def b0037 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0037.block Panels0037.accepted Panels0037.integerPanels Panels0037.aligned
    Panels0037.weightRows Panels0037.weights_checked ⟨10, by decide⟩
def b0038 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0038.block Panels0038.accepted Panels0038.integerPanels Panels0038.aligned
    Panels0038.weightRows Panels0038.weights_checked ⟨10, by decide⟩
def b0039 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0039.block Panels0039.accepted Panels0039.integerPanels Panels0039.aligned
    Panels0039.weightRows Panels0039.weights_checked ⟨10, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0032, b0033, b0034, b0035, b0036, b0037, b0038, b0039]
theorem chain_checked : blockChainCheck (27044279414822545995436962674/10^30) (34724482593808868107651770989/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=74308028191572007009977831640775289508718905773106376083119225947437428256452260293906088510795531968527490508592415746371159592448405921983342344868932218308800391208441292091184030237603056909482032184048477353/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row10
namespace Row11
abbrev ζ : ℚ := 10152284263959390862944162436/10^30
def b0032 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0032.block Panels0032.accepted Panels0032.integerPanels Panels0032.aligned
    Panels0032.weightRows Panels0032.weights_checked ⟨11, by decide⟩
def b0033 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0033.block Panels0033.accepted Panels0033.integerPanels Panels0033.aligned
    Panels0033.weightRows Panels0033.weights_checked ⟨11, by decide⟩
def b0034 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0034.block Panels0034.accepted Panels0034.integerPanels Panels0034.aligned
    Panels0034.weightRows Panels0034.weights_checked ⟨11, by decide⟩
def b0035 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0035.block Panels0035.accepted Panels0035.integerPanels Panels0035.aligned
    Panels0035.weightRows Panels0035.weights_checked ⟨11, by decide⟩
def b0036 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0036.block Panels0036.accepted Panels0036.integerPanels Panels0036.aligned
    Panels0036.weightRows Panels0036.weights_checked ⟨11, by decide⟩
def b0037 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0037.block Panels0037.accepted Panels0037.integerPanels Panels0037.aligned
    Panels0037.weightRows Panels0037.weights_checked ⟨11, by decide⟩
def b0038 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0038.block Panels0038.accepted Panels0038.integerPanels Panels0038.aligned
    Panels0038.weightRows Panels0038.weights_checked ⟨11, by decide⟩
def b0039 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0039.block Panels0039.accepted Panels0039.integerPanels Panels0039.aligned
    Panels0039.weightRows Panels0039.weights_checked ⟨11, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0032, b0033, b0034, b0035, b0036, b0037, b0038, b0039]
theorem chain_checked : blockChainCheck (27044279414822545995436962674/10^30) (34724482593808868107651770989/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=194169759734014127885796580926625386574935719696341092758053164118260621834364159179601789830833747288012609305958122988890646953002297185582786201095195715549334708677413546199598076868915551600908910400217614143/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row11
namespace Row12
abbrev ζ : ℚ := 9950248756218905472636815920/10^30
def b0032 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0032.block Panels0032.accepted Panels0032.integerPanels Panels0032.aligned
    Panels0032.weightRows Panels0032.weights_checked ⟨12, by decide⟩
def b0033 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0033.block Panels0033.accepted Panels0033.integerPanels Panels0033.aligned
    Panels0033.weightRows Panels0033.weights_checked ⟨12, by decide⟩
def b0034 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0034.block Panels0034.accepted Panels0034.integerPanels Panels0034.aligned
    Panels0034.weightRows Panels0034.weights_checked ⟨12, by decide⟩
def b0035 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0035.block Panels0035.accepted Panels0035.integerPanels Panels0035.aligned
    Panels0035.weightRows Panels0035.weights_checked ⟨12, by decide⟩
def b0036 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0036.block Panels0036.accepted Panels0036.integerPanels Panels0036.aligned
    Panels0036.weightRows Panels0036.weights_checked ⟨12, by decide⟩
def b0037 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0037.block Panels0037.accepted Panels0037.integerPanels Panels0037.aligned
    Panels0037.weightRows Panels0037.weights_checked ⟨12, by decide⟩
def b0038 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0038.block Panels0038.accepted Panels0038.integerPanels Panels0038.aligned
    Panels0038.weightRows Panels0038.weights_checked ⟨12, by decide⟩
def b0039 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0039.block Panels0039.accepted Panels0039.integerPanels Panels0039.aligned
    Panels0039.weightRows Panels0039.weights_checked ⟨12, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0032, b0033, b0034, b0035, b0036, b0037, b0038, b0039]
theorem chain_checked : blockChainCheck (27044279414822545995436962674/10^30) (34724482593808868107651770989/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=203820531511292199668497248959098544881601940733607514794949157424173857331927386786170768917739233779517730564039881195142790784269346077024441217188069078363736833107434416477087906703849234104201224580230840359/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row12
#print axioms Row12.segment
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments004
