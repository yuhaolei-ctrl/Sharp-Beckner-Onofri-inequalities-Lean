module

public import BecknerOnofri.EntropyHeatCheckedWeights
public import BecknerOnofri.EntropyHeatSegments
public import BecknerOnofri.EntropyHeatCertificate.Panels0064
public import BecknerOnofri.EntropyHeatCertificate.Panels0065
public import BecknerOnofri.EntropyHeatCertificate.Panels0066
public import BecknerOnofri.EntropyHeatCertificate.Panels0067
public import BecknerOnofri.EntropyHeatCertificate.Panels0068
public import BecknerOnofri.EntropyHeatCertificate.Panels0069
public import BecknerOnofri.EntropyHeatCertificate.Panels0070
public import BecknerOnofri.EntropyHeatCertificate.Panels0071

@[expose] public section
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments008
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace Row00
abbrev ζ : ℚ := 285714285714285714285714285714/10^30
def b0064 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0064.block Panels0064.accepted Panels0064.integerPanels Panels0064.aligned
    Panels0064.weightRows Panels0064.weights_checked ⟨0, by decide⟩
def b0065 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0065.block Panels0065.accepted Panels0065.integerPanels Panels0065.aligned
    Panels0065.weightRows Panels0065.weights_checked ⟨0, by decide⟩
def b0066 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0066.block Panels0066.accepted Panels0066.integerPanels Panels0066.aligned
    Panels0066.weightRows Panels0066.weights_checked ⟨0, by decide⟩
def b0067 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0067.block Panels0067.accepted Panels0067.integerPanels Panels0067.aligned
    Panels0067.weightRows Panels0067.weights_checked ⟨0, by decide⟩
def b0068 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0068.block Panels0068.accepted Panels0068.integerPanels Panels0068.aligned
    Panels0068.weightRows Panels0068.weights_checked ⟨0, by decide⟩
def b0069 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0069.block Panels0069.accepted Panels0069.integerPanels Panels0069.aligned
    Panels0069.weightRows Panels0069.weights_checked ⟨0, by decide⟩
def b0070 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0070.block Panels0070.accepted Panels0070.integerPanels Panels0070.aligned
    Panels0070.weightRows Panels0070.weights_checked ⟨0, by decide⟩
def b0071 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0071.block Panels0071.accepted Panels0071.integerPanels Panels0071.aligned
    Panels0071.weightRows Panels0071.weights_checked ⟨0, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0064, b0065, b0066, b0067, b0068, b0069, b0070, b0071]
theorem chain_checked : blockChainCheck (73505001431232948341390251911/10^30) (94379410285111952461414366608/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row00
namespace Row01
abbrev ζ : ℚ := 222222222222222222222222222222/10^30
def b0064 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0064.block Panels0064.accepted Panels0064.integerPanels Panels0064.aligned
    Panels0064.weightRows Panels0064.weights_checked ⟨1, by decide⟩
def b0065 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0065.block Panels0065.accepted Panels0065.integerPanels Panels0065.aligned
    Panels0065.weightRows Panels0065.weights_checked ⟨1, by decide⟩
def b0066 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0066.block Panels0066.accepted Panels0066.integerPanels Panels0066.aligned
    Panels0066.weightRows Panels0066.weights_checked ⟨1, by decide⟩
def b0067 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0067.block Panels0067.accepted Panels0067.integerPanels Panels0067.aligned
    Panels0067.weightRows Panels0067.weights_checked ⟨1, by decide⟩
def b0068 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0068.block Panels0068.accepted Panels0068.integerPanels Panels0068.aligned
    Panels0068.weightRows Panels0068.weights_checked ⟨1, by decide⟩
def b0069 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0069.block Panels0069.accepted Panels0069.integerPanels Panels0069.aligned
    Panels0069.weightRows Panels0069.weights_checked ⟨1, by decide⟩
def b0070 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0070.block Panels0070.accepted Panels0070.integerPanels Panels0070.aligned
    Panels0070.weightRows Panels0070.weights_checked ⟨1, by decide⟩
def b0071 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0071.block Panels0071.accepted Panels0071.integerPanels Panels0071.aligned
    Panels0071.weightRows Panels0071.weights_checked ⟨1, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0064, b0065, b0066, b0067, b0068, b0069, b0070, b0071]
theorem chain_checked : blockChainCheck (73505001431232948341390251911/10^30) (94379410285111952461414366608/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row01
namespace Row02
abbrev ζ : ℚ := 153846153846153846153846153846/10^30
def b0064 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0064.block Panels0064.accepted Panels0064.integerPanels Panels0064.aligned
    Panels0064.weightRows Panels0064.weights_checked ⟨2, by decide⟩
def b0065 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0065.block Panels0065.accepted Panels0065.integerPanels Panels0065.aligned
    Panels0065.weightRows Panels0065.weights_checked ⟨2, by decide⟩
def b0066 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0066.block Panels0066.accepted Panels0066.integerPanels Panels0066.aligned
    Panels0066.weightRows Panels0066.weights_checked ⟨2, by decide⟩
def b0067 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0067.block Panels0067.accepted Panels0067.integerPanels Panels0067.aligned
    Panels0067.weightRows Panels0067.weights_checked ⟨2, by decide⟩
def b0068 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0068.block Panels0068.accepted Panels0068.integerPanels Panels0068.aligned
    Panels0068.weightRows Panels0068.weights_checked ⟨2, by decide⟩
def b0069 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0069.block Panels0069.accepted Panels0069.integerPanels Panels0069.aligned
    Panels0069.weightRows Panels0069.weights_checked ⟨2, by decide⟩
def b0070 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0070.block Panels0070.accepted Panels0070.integerPanels Panels0070.aligned
    Panels0070.weightRows Panels0070.weights_checked ⟨2, by decide⟩
def b0071 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0071.block Panels0071.accepted Panels0071.integerPanels Panels0071.aligned
    Panels0071.weightRows Panels0071.weights_checked ⟨2, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0064, b0065, b0066, b0067, b0068, b0069, b0070, b0071]
theorem chain_checked : blockChainCheck (73505001431232948341390251911/10^30) (94379410285111952461414366608/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row02
namespace Row03
abbrev ζ : ℚ := 117647058823529411764705882352/10^30
def b0064 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0064.block Panels0064.accepted Panels0064.integerPanels Panels0064.aligned
    Panels0064.weightRows Panels0064.weights_checked ⟨3, by decide⟩
def b0065 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0065.block Panels0065.accepted Panels0065.integerPanels Panels0065.aligned
    Panels0065.weightRows Panels0065.weights_checked ⟨3, by decide⟩
def b0066 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0066.block Panels0066.accepted Panels0066.integerPanels Panels0066.aligned
    Panels0066.weightRows Panels0066.weights_checked ⟨3, by decide⟩
def b0067 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0067.block Panels0067.accepted Panels0067.integerPanels Panels0067.aligned
    Panels0067.weightRows Panels0067.weights_checked ⟨3, by decide⟩
def b0068 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0068.block Panels0068.accepted Panels0068.integerPanels Panels0068.aligned
    Panels0068.weightRows Panels0068.weights_checked ⟨3, by decide⟩
def b0069 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0069.block Panels0069.accepted Panels0069.integerPanels Panels0069.aligned
    Panels0069.weightRows Panels0069.weights_checked ⟨3, by decide⟩
def b0070 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0070.block Panels0070.accepted Panels0070.integerPanels Panels0070.aligned
    Panels0070.weightRows Panels0070.weights_checked ⟨3, by decide⟩
def b0071 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0071.block Panels0071.accepted Panels0071.integerPanels Panels0071.aligned
    Panels0071.weightRows Panels0071.weights_checked ⟨3, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0064, b0065, b0066, b0067, b0068, b0069, b0070, b0071]
theorem chain_checked : blockChainCheck (73505001431232948341390251911/10^30) (94379410285111952461414366608/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row03
namespace Row04
abbrev ζ : ℚ := 86956521739130434782608695652/10^30
def b0064 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0064.block Panels0064.accepted Panels0064.integerPanels Panels0064.aligned
    Panels0064.weightRows Panels0064.weights_checked ⟨4, by decide⟩
def b0065 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0065.block Panels0065.accepted Panels0065.integerPanels Panels0065.aligned
    Panels0065.weightRows Panels0065.weights_checked ⟨4, by decide⟩
def b0066 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0066.block Panels0066.accepted Panels0066.integerPanels Panels0066.aligned
    Panels0066.weightRows Panels0066.weights_checked ⟨4, by decide⟩
def b0067 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0067.block Panels0067.accepted Panels0067.integerPanels Panels0067.aligned
    Panels0067.weightRows Panels0067.weights_checked ⟨4, by decide⟩
def b0068 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0068.block Panels0068.accepted Panels0068.integerPanels Panels0068.aligned
    Panels0068.weightRows Panels0068.weights_checked ⟨4, by decide⟩
def b0069 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0069.block Panels0069.accepted Panels0069.integerPanels Panels0069.aligned
    Panels0069.weightRows Panels0069.weights_checked ⟨4, by decide⟩
def b0070 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0070.block Panels0070.accepted Panels0070.integerPanels Panels0070.aligned
    Panels0070.weightRows Panels0070.weights_checked ⟨4, by decide⟩
def b0071 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0071.block Panels0071.accepted Panels0071.integerPanels Panels0071.aligned
    Panels0071.weightRows Panels0071.weights_checked ⟨4, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0064, b0065, b0066, b0067, b0068, b0069, b0070, b0071]
theorem chain_checked : blockChainCheck (73505001431232948341390251911/10^30) (94379410285111952461414366608/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=244159808143627894713833271731356408918736920802958559561126134312022599210199454596314440315638459054021264992630475043977596002985217525913422225578862639430537891866801803030767035262792381609602823612568/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row04
namespace Row05
abbrev ζ : ℚ := 64516129032258064516129032258/10^30
def b0064 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0064.block Panels0064.accepted Panels0064.integerPanels Panels0064.aligned
    Panels0064.weightRows Panels0064.weights_checked ⟨5, by decide⟩
def b0065 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0065.block Panels0065.accepted Panels0065.integerPanels Panels0065.aligned
    Panels0065.weightRows Panels0065.weights_checked ⟨5, by decide⟩
def b0066 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0066.block Panels0066.accepted Panels0066.integerPanels Panels0066.aligned
    Panels0066.weightRows Panels0066.weights_checked ⟨5, by decide⟩
def b0067 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0067.block Panels0067.accepted Panels0067.integerPanels Panels0067.aligned
    Panels0067.weightRows Panels0067.weights_checked ⟨5, by decide⟩
def b0068 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0068.block Panels0068.accepted Panels0068.integerPanels Panels0068.aligned
    Panels0068.weightRows Panels0068.weights_checked ⟨5, by decide⟩
def b0069 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0069.block Panels0069.accepted Panels0069.integerPanels Panels0069.aligned
    Panels0069.weightRows Panels0069.weights_checked ⟨5, by decide⟩
def b0070 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0070.block Panels0070.accepted Panels0070.integerPanels Panels0070.aligned
    Panels0070.weightRows Panels0070.weights_checked ⟨5, by decide⟩
def b0071 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0071.block Panels0071.accepted Panels0071.integerPanels Panels0071.aligned
    Panels0071.weightRows Panels0071.weights_checked ⟨5, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0064, b0065, b0066, b0067, b0068, b0069, b0070, b0071]
theorem chain_checked : blockChainCheck (73505001431232948341390251911/10^30) (94379410285111952461414366608/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=1324712014456144013441963520804895670957350589548186575418418800755795761920968292811003416716734939314264171152431796127790347905309786826279714120770167136418253350392433599787711481571651168076603990267786766/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row05
namespace Row06
abbrev ζ : ℚ := 46511627906976744186046511627/10^30
def b0064 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0064.block Panels0064.accepted Panels0064.integerPanels Panels0064.aligned
    Panels0064.weightRows Panels0064.weights_checked ⟨6, by decide⟩
def b0065 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0065.block Panels0065.accepted Panels0065.integerPanels Panels0065.aligned
    Panels0065.weightRows Panels0065.weights_checked ⟨6, by decide⟩
def b0066 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0066.block Panels0066.accepted Panels0066.integerPanels Panels0066.aligned
    Panels0066.weightRows Panels0066.weights_checked ⟨6, by decide⟩
def b0067 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0067.block Panels0067.accepted Panels0067.integerPanels Panels0067.aligned
    Panels0067.weightRows Panels0067.weights_checked ⟨6, by decide⟩
def b0068 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0068.block Panels0068.accepted Panels0068.integerPanels Panels0068.aligned
    Panels0068.weightRows Panels0068.weights_checked ⟨6, by decide⟩
def b0069 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0069.block Panels0069.accepted Panels0069.integerPanels Panels0069.aligned
    Panels0069.weightRows Panels0069.weights_checked ⟨6, by decide⟩
def b0070 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0070.block Panels0070.accepted Panels0070.integerPanels Panels0070.aligned
    Panels0070.weightRows Panels0070.weights_checked ⟨6, by decide⟩
def b0071 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0071.block Panels0071.accepted Panels0071.integerPanels Panels0071.aligned
    Panels0071.weightRows Panels0071.weights_checked ⟨6, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0064, b0065, b0066, b0067, b0068, b0069, b0070, b0071]
theorem chain_checked : blockChainCheck (73505001431232948341390251911/10^30) (94379410285111952461414366608/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=25831471741751502063400187824835064078499205431155720699153470160225044698898249792252386997551332748834112505724755125206421740386751762416806250253226781876011612060386477814169109032979329045876359451858993322/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row06
namespace Row07
abbrev ζ : ℚ := 33898305084745762711864406779/10^30
def b0064 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0064.block Panels0064.accepted Panels0064.integerPanels Panels0064.aligned
    Panels0064.weightRows Panels0064.weights_checked ⟨7, by decide⟩
def b0065 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0065.block Panels0065.accepted Panels0065.integerPanels Panels0065.aligned
    Panels0065.weightRows Panels0065.weights_checked ⟨7, by decide⟩
def b0066 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0066.block Panels0066.accepted Panels0066.integerPanels Panels0066.aligned
    Panels0066.weightRows Panels0066.weights_checked ⟨7, by decide⟩
def b0067 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0067.block Panels0067.accepted Panels0067.integerPanels Panels0067.aligned
    Panels0067.weightRows Panels0067.weights_checked ⟨7, by decide⟩
def b0068 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0068.block Panels0068.accepted Panels0068.integerPanels Panels0068.aligned
    Panels0068.weightRows Panels0068.weights_checked ⟨7, by decide⟩
def b0069 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0069.block Panels0069.accepted Panels0069.integerPanels Panels0069.aligned
    Panels0069.weightRows Panels0069.weights_checked ⟨7, by decide⟩
def b0070 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0070.block Panels0070.accepted Panels0070.integerPanels Panels0070.aligned
    Panels0070.weightRows Panels0070.weights_checked ⟨7, by decide⟩
def b0071 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0071.block Panels0071.accepted Panels0071.integerPanels Panels0071.aligned
    Panels0071.weightRows Panels0071.weights_checked ⟨7, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0064, b0065, b0066, b0067, b0068, b0069, b0070, b0071]
theorem chain_checked : blockChainCheck (73505001431232948341390251911/10^30) (94379410285111952461414366608/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=107453913775395266618284788913158338629406037014529249015038972885701599232726941134118600573149488464364428474890450601569625611588116956891675202031477500242902558650644491423023998534155527829182106629411016490/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row07
namespace Row08
abbrev ζ : ℚ := 25316455696202531645569620253/10^30
def b0064 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0064.block Panels0064.accepted Panels0064.integerPanels Panels0064.aligned
    Panels0064.weightRows Panels0064.weights_checked ⟨8, by decide⟩
def b0065 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0065.block Panels0065.accepted Panels0065.integerPanels Panels0065.aligned
    Panels0065.weightRows Panels0065.weights_checked ⟨8, by decide⟩
def b0066 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0066.block Panels0066.accepted Panels0066.integerPanels Panels0066.aligned
    Panels0066.weightRows Panels0066.weights_checked ⟨8, by decide⟩
def b0067 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0067.block Panels0067.accepted Panels0067.integerPanels Panels0067.aligned
    Panels0067.weightRows Panels0067.weights_checked ⟨8, by decide⟩
def b0068 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0068.block Panels0068.accepted Panels0068.integerPanels Panels0068.aligned
    Panels0068.weightRows Panels0068.weights_checked ⟨8, by decide⟩
def b0069 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0069.block Panels0069.accepted Panels0069.integerPanels Panels0069.aligned
    Panels0069.weightRows Panels0069.weights_checked ⟨8, by decide⟩
def b0070 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0070.block Panels0070.accepted Panels0070.integerPanels Panels0070.aligned
    Panels0070.weightRows Panels0070.weights_checked ⟨8, by decide⟩
def b0071 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0071.block Panels0071.accepted Panels0071.integerPanels Panels0071.aligned
    Panels0071.weightRows Panels0071.weights_checked ⟨8, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0064, b0065, b0066, b0067, b0068, b0069, b0070, b0071]
theorem chain_checked : blockChainCheck (73505001431232948341390251911/10^30) (94379410285111952461414366608/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=236723375764061832370248425112243995934604138905484538717154149175860157776268907826664850597136901671442219381980443978712786971944051431608967294089422491587173679696136127329066818145456284878056896570297749906/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row08
namespace Row09
abbrev ζ : ℚ := 18691588785046728971962616822/10^30
def b0064 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0064.block Panels0064.accepted Panels0064.integerPanels Panels0064.aligned
    Panels0064.weightRows Panels0064.weights_checked ⟨9, by decide⟩
def b0065 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0065.block Panels0065.accepted Panels0065.integerPanels Panels0065.aligned
    Panels0065.weightRows Panels0065.weights_checked ⟨9, by decide⟩
def b0066 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0066.block Panels0066.accepted Panels0066.integerPanels Panels0066.aligned
    Panels0066.weightRows Panels0066.weights_checked ⟨9, by decide⟩
def b0067 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0067.block Panels0067.accepted Panels0067.integerPanels Panels0067.aligned
    Panels0067.weightRows Panels0067.weights_checked ⟨9, by decide⟩
def b0068 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0068.block Panels0068.accepted Panels0068.integerPanels Panels0068.aligned
    Panels0068.weightRows Panels0068.weights_checked ⟨9, by decide⟩
def b0069 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0069.block Panels0069.accepted Panels0069.integerPanels Panels0069.aligned
    Panels0069.weightRows Panels0069.weights_checked ⟨9, by decide⟩
def b0070 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0070.block Panels0070.accepted Panels0070.integerPanels Panels0070.aligned
    Panels0070.weightRows Panels0070.weights_checked ⟨9, by decide⟩
def b0071 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0071.block Panels0071.accepted Panels0071.integerPanels Panels0071.aligned
    Panels0071.weightRows Panels0071.weights_checked ⟨9, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0064, b0065, b0066, b0067, b0068, b0069, b0070, b0071]
theorem chain_checked : blockChainCheck (73505001431232948341390251911/10^30) (94379410285111952461414366608/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=405153586658824149988915137927788155447260539842177168518315423918260293830631812873096651606038158244477086280109419812392306171988823128025542158316074156482898182118298381322703270684857089757142977615011839262/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row09
namespace Row10
abbrev ζ : ℚ := 13793103448275862068965517241/10^30
def b0064 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0064.block Panels0064.accepted Panels0064.integerPanels Panels0064.aligned
    Panels0064.weightRows Panels0064.weights_checked ⟨10, by decide⟩
def b0065 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0065.block Panels0065.accepted Panels0065.integerPanels Panels0065.aligned
    Panels0065.weightRows Panels0065.weights_checked ⟨10, by decide⟩
def b0066 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0066.block Panels0066.accepted Panels0066.integerPanels Panels0066.aligned
    Panels0066.weightRows Panels0066.weights_checked ⟨10, by decide⟩
def b0067 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0067.block Panels0067.accepted Panels0067.integerPanels Panels0067.aligned
    Panels0067.weightRows Panels0067.weights_checked ⟨10, by decide⟩
def b0068 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0068.block Panels0068.accepted Panels0068.integerPanels Panels0068.aligned
    Panels0068.weightRows Panels0068.weights_checked ⟨10, by decide⟩
def b0069 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0069.block Panels0069.accepted Panels0069.integerPanels Panels0069.aligned
    Panels0069.weightRows Panels0069.weights_checked ⟨10, by decide⟩
def b0070 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0070.block Panels0070.accepted Panels0070.integerPanels Panels0070.aligned
    Panels0070.weightRows Panels0070.weights_checked ⟨10, by decide⟩
def b0071 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0071.block Panels0071.accepted Panels0071.integerPanels Panels0071.aligned
    Panels0071.weightRows Panels0071.weights_checked ⟨10, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0064, b0065, b0066, b0067, b0068, b0069, b0070, b0071]
theorem chain_checked : blockChainCheck (73505001431232948341390251911/10^30) (94379410285111952461414366608/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=583239633840894456952146034520991842268497465181902772746531066631150165868261403696492630470245228898829317616966058558126043829183840687213972089439289300304519210348429809516817751692020605710917754169813492658/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row10
namespace Row11
abbrev ζ : ℚ := 10152284263959390862944162436/10^30
def b0064 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0064.block Panels0064.accepted Panels0064.integerPanels Panels0064.aligned
    Panels0064.weightRows Panels0064.weights_checked ⟨11, by decide⟩
def b0065 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0065.block Panels0065.accepted Panels0065.integerPanels Panels0065.aligned
    Panels0065.weightRows Panels0065.weights_checked ⟨11, by decide⟩
def b0066 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0066.block Panels0066.accepted Panels0066.integerPanels Panels0066.aligned
    Panels0066.weightRows Panels0066.weights_checked ⟨11, by decide⟩
def b0067 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0067.block Panels0067.accepted Panels0067.integerPanels Panels0067.aligned
    Panels0067.weightRows Panels0067.weights_checked ⟨11, by decide⟩
def b0068 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0068.block Panels0068.accepted Panels0068.integerPanels Panels0068.aligned
    Panels0068.weightRows Panels0068.weights_checked ⟨11, by decide⟩
def b0069 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0069.block Panels0069.accepted Panels0069.integerPanels Panels0069.aligned
    Panels0069.weightRows Panels0069.weights_checked ⟨11, by decide⟩
def b0070 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0070.block Panels0070.accepted Panels0070.integerPanels Panels0070.aligned
    Panels0070.weightRows Panels0070.weights_checked ⟨11, by decide⟩
def b0071 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0071.block Panels0071.accepted Panels0071.integerPanels Panels0071.aligned
    Panels0071.weightRows Panels0071.weights_checked ⟨11, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0064, b0065, b0066, b0067, b0068, b0069, b0070, b0071]
theorem chain_checked : blockChainCheck (73505001431232948341390251911/10^30) (94379410285111952461414366608/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=752675001221911953204063454714321267918422795800741876248782734542048706683154855132675949007648999242550912764569098157918542354564150866460606023604643932043901273795661651535968121610328261646030878266434337198/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row11
namespace Row12
abbrev ζ : ℚ := 9950248756218905472636815920/10^30
def b0064 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0064.block Panels0064.accepted Panels0064.integerPanels Panels0064.aligned
    Panels0064.weightRows Panels0064.weights_checked ⟨12, by decide⟩
def b0065 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0065.block Panels0065.accepted Panels0065.integerPanels Panels0065.aligned
    Panels0065.weightRows Panels0065.weights_checked ⟨12, by decide⟩
def b0066 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0066.block Panels0066.accepted Panels0066.integerPanels Panels0066.aligned
    Panels0066.weightRows Panels0066.weights_checked ⟨12, by decide⟩
def b0067 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0067.block Panels0067.accepted Panels0067.integerPanels Panels0067.aligned
    Panels0067.weightRows Panels0067.weights_checked ⟨12, by decide⟩
def b0068 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0068.block Panels0068.accepted Panels0068.integerPanels Panels0068.aligned
    Panels0068.weightRows Panels0068.weights_checked ⟨12, by decide⟩
def b0069 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0069.block Panels0069.accepted Panels0069.integerPanels Panels0069.aligned
    Panels0069.weightRows Panels0069.weights_checked ⟨12, by decide⟩
def b0070 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0070.block Panels0070.accepted Panels0070.integerPanels Panels0070.aligned
    Panels0070.weightRows Panels0070.weights_checked ⟨12, by decide⟩
def b0071 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0071.block Panels0071.accepted Panels0071.integerPanels Panels0071.aligned
    Panels0071.weightRows Panels0071.weights_checked ⟨12, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0064, b0065, b0066, b0067, b0068, b0069, b0070, b0071]
theorem chain_checked : blockChainCheck (73505001431232948341390251911/10^30) (94379410285111952461414366608/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=763125329431976246878470668029286132038268946291298866858124909929118853241669076664393841803735745745595430272159398833854606154889773821533959810765918048877942756400791434557806363906156874399702182506044682174/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row12
#print axioms Row12.segment
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments008
