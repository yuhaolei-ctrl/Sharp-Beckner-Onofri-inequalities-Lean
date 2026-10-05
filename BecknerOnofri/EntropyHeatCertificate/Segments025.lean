module

public import BecknerOnofri.EntropyHeatCheckedWeights
public import BecknerOnofri.EntropyHeatSegments
public import BecknerOnofri.EntropyHeatCertificate.Panels0200
public import BecknerOnofri.EntropyHeatCertificate.Panels0201
public import BecknerOnofri.EntropyHeatCertificate.Panels0202
public import BecknerOnofri.EntropyHeatCertificate.Panels0203
public import BecknerOnofri.EntropyHeatCertificate.Panels0204
public import BecknerOnofri.EntropyHeatCertificate.Panels0205
public import BecknerOnofri.EntropyHeatCertificate.Panels0206
public import BecknerOnofri.EntropyHeatCertificate.Panels0207

@[expose] public section
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments025
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace Row00
abbrev ζ : ℚ := 285714285714285714285714285714/10^30
def b0200 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0200.block Panels0200.accepted Panels0200.integerPanels Panels0200.aligned
    Panels0200.weightRows Panels0200.weights_checked ⟨0, by decide⟩
def b0201 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0201.block Panels0201.accepted Panels0201.integerPanels Panels0201.aligned
    Panels0201.weightRows Panels0201.weights_checked ⟨0, by decide⟩
def b0202 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0202.block Panels0202.accepted Panels0202.integerPanels Panels0202.aligned
    Panels0202.weightRows Panels0202.weights_checked ⟨0, by decide⟩
def b0203 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0203.block Panels0203.accepted Panels0203.integerPanels Panels0203.aligned
    Panels0203.weightRows Panels0203.weights_checked ⟨0, by decide⟩
def b0204 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0204.block Panels0204.accepted Panels0204.integerPanels Panels0204.aligned
    Panels0204.weightRows Panels0204.weights_checked ⟨0, by decide⟩
def b0205 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0205.block Panels0205.accepted Panels0205.integerPanels Panels0205.aligned
    Panels0205.weightRows Panels0205.weights_checked ⟨0, by decide⟩
def b0206 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0206.block Panels0206.accepted Panels0206.integerPanels Panels0206.aligned
    Panels0206.weightRows Panels0206.weights_checked ⟨0, by decide⟩
def b0207 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0207.block Panels0207.accepted Panels0207.integerPanels Panels0207.aligned
    Panels0207.weightRows Panels0207.weights_checked ⟨0, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0200, b0201, b0202, b0203, b0204, b0205, b0206, b0207]
theorem chain_checked : blockChainCheck (5150426141637181757933211818553/10^30) (6613076287325882991783239235141/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=159737148932355599837900026125322935611932172628141406491507934277623950164335555203073921252189862800711436458002078346642456771114265621401064165674729083516977781121634297439443948797562805685863244315040/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row00
namespace Row01
abbrev ζ : ℚ := 222222222222222222222222222222/10^30
def b0200 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0200.block Panels0200.accepted Panels0200.integerPanels Panels0200.aligned
    Panels0200.weightRows Panels0200.weights_checked ⟨1, by decide⟩
def b0201 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0201.block Panels0201.accepted Panels0201.integerPanels Panels0201.aligned
    Panels0201.weightRows Panels0201.weights_checked ⟨1, by decide⟩
def b0202 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0202.block Panels0202.accepted Panels0202.integerPanels Panels0202.aligned
    Panels0202.weightRows Panels0202.weights_checked ⟨1, by decide⟩
def b0203 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0203.block Panels0203.accepted Panels0203.integerPanels Panels0203.aligned
    Panels0203.weightRows Panels0203.weights_checked ⟨1, by decide⟩
def b0204 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0204.block Panels0204.accepted Panels0204.integerPanels Panels0204.aligned
    Panels0204.weightRows Panels0204.weights_checked ⟨1, by decide⟩
def b0205 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0205.block Panels0205.accepted Panels0205.integerPanels Panels0205.aligned
    Panels0205.weightRows Panels0205.weights_checked ⟨1, by decide⟩
def b0206 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0206.block Panels0206.accepted Panels0206.integerPanels Panels0206.aligned
    Panels0206.weightRows Panels0206.weights_checked ⟨1, by decide⟩
def b0207 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0207.block Panels0207.accepted Panels0207.integerPanels Panels0207.aligned
    Panels0207.weightRows Panels0207.weights_checked ⟨1, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0200, b0201, b0202, b0203, b0204, b0205, b0206, b0207]
theorem chain_checked : blockChainCheck (5150426141637181757933211818553/10^30) (6613076287325882991783239235141/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=169822938858575261307042923831345803736872983447312685049860590571638198148096618140954041422645247095989520731864339582979429615435970085544542712798614796266067515351598125001571533075322650621509826454000/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row01
namespace Row02
abbrev ζ : ℚ := 153846153846153846153846153846/10^30
def b0200 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0200.block Panels0200.accepted Panels0200.integerPanels Panels0200.aligned
    Panels0200.weightRows Panels0200.weights_checked ⟨2, by decide⟩
def b0201 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0201.block Panels0201.accepted Panels0201.integerPanels Panels0201.aligned
    Panels0201.weightRows Panels0201.weights_checked ⟨2, by decide⟩
def b0202 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0202.block Panels0202.accepted Panels0202.integerPanels Panels0202.aligned
    Panels0202.weightRows Panels0202.weights_checked ⟨2, by decide⟩
def b0203 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0203.block Panels0203.accepted Panels0203.integerPanels Panels0203.aligned
    Panels0203.weightRows Panels0203.weights_checked ⟨2, by decide⟩
def b0204 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0204.block Panels0204.accepted Panels0204.integerPanels Panels0204.aligned
    Panels0204.weightRows Panels0204.weights_checked ⟨2, by decide⟩
def b0205 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0205.block Panels0205.accepted Panels0205.integerPanels Panels0205.aligned
    Panels0205.weightRows Panels0205.weights_checked ⟨2, by decide⟩
def b0206 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0206.block Panels0206.accepted Panels0206.integerPanels Panels0206.aligned
    Panels0206.weightRows Panels0206.weights_checked ⟨2, by decide⟩
def b0207 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0207.block Panels0207.accepted Panels0207.integerPanels Panels0207.aligned
    Panels0207.weightRows Panels0207.weights_checked ⟨2, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0200, b0201, b0202, b0203, b0204, b0205, b0206, b0207]
theorem chain_checked : blockChainCheck (5150426141637181757933211818553/10^30) (6613076287325882991783239235141/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=181249255842745676984835484057382417329938922635522868163116656316415686164409239159801088458402221859970866440268328491529447646059418439603003977925865602273862001215322380603416839119878340836440082748880/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row02
namespace Row03
abbrev ζ : ℚ := 117647058823529411764705882352/10^30
def b0200 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0200.block Panels0200.accepted Panels0200.integerPanels Panels0200.aligned
    Panels0200.weightRows Panels0200.weights_checked ⟨3, by decide⟩
def b0201 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0201.block Panels0201.accepted Panels0201.integerPanels Panels0201.aligned
    Panels0201.weightRows Panels0201.weights_checked ⟨3, by decide⟩
def b0202 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0202.block Panels0202.accepted Panels0202.integerPanels Panels0202.aligned
    Panels0202.weightRows Panels0202.weights_checked ⟨3, by decide⟩
def b0203 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0203.block Panels0203.accepted Panels0203.integerPanels Panels0203.aligned
    Panels0203.weightRows Panels0203.weights_checked ⟨3, by decide⟩
def b0204 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0204.block Panels0204.accepted Panels0204.integerPanels Panels0204.aligned
    Panels0204.weightRows Panels0204.weights_checked ⟨3, by decide⟩
def b0205 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0205.block Panels0205.accepted Panels0205.integerPanels Panels0205.aligned
    Panels0205.weightRows Panels0205.weights_checked ⟨3, by decide⟩
def b0206 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0206.block Panels0206.accepted Panels0206.integerPanels Panels0206.aligned
    Panels0206.weightRows Panels0206.weights_checked ⟨3, by decide⟩
def b0207 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0207.block Panels0207.accepted Panels0207.integerPanels Panels0207.aligned
    Panels0207.weightRows Panels0207.weights_checked ⟨3, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0200, b0201, b0202, b0203, b0204, b0205, b0206, b0207]
theorem chain_checked : blockChainCheck (5150426141637181757933211818553/10^30) (6613076287325882991783239235141/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=187543313207577379483000352766306187665099549791179892429684349359726460800652554540072283095819175743633475631854791470961028140651920570923466684803610336790744059031144536795992298541584575652417445681800/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row03
namespace Row04
abbrev ζ : ℚ := 86956521739130434782608695652/10^30
def b0200 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0200.block Panels0200.accepted Panels0200.integerPanels Panels0200.aligned
    Panels0200.weightRows Panels0200.weights_checked ⟨4, by decide⟩
def b0201 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0201.block Panels0201.accepted Panels0201.integerPanels Panels0201.aligned
    Panels0201.weightRows Panels0201.weights_checked ⟨4, by decide⟩
def b0202 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0202.block Panels0202.accepted Panels0202.integerPanels Panels0202.aligned
    Panels0202.weightRows Panels0202.weights_checked ⟨4, by decide⟩
def b0203 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0203.block Panels0203.accepted Panels0203.integerPanels Panels0203.aligned
    Panels0203.weightRows Panels0203.weights_checked ⟨4, by decide⟩
def b0204 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0204.block Panels0204.accepted Panels0204.integerPanels Panels0204.aligned
    Panels0204.weightRows Panels0204.weights_checked ⟨4, by decide⟩
def b0205 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0205.block Panels0205.accepted Panels0205.integerPanels Panels0205.aligned
    Panels0205.weightRows Panels0205.weights_checked ⟨4, by decide⟩
def b0206 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0206.block Panels0206.accepted Panels0206.integerPanels Panels0206.aligned
    Panels0206.weightRows Panels0206.weights_checked ⟨4, by decide⟩
def b0207 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0207.block Panels0207.accepted Panels0207.integerPanels Panels0207.aligned
    Panels0207.weightRows Panels0207.weights_checked ⟨4, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0200, b0201, b0202, b0203, b0204, b0205, b0206, b0207]
theorem chain_checked : blockChainCheck (5150426141637181757933211818553/10^30) (6613076287325882991783239235141/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=193015797134566261968742824722174541010320195664426333729445407003508216020851657311169011013006626272907899833133665217049658249833710120667181997429966568203155297676306434904530177264551702551446388439800/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row04
namespace Row05
abbrev ζ : ℚ := 64516129032258064516129032258/10^30
def b0200 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0200.block Panels0200.accepted Panels0200.integerPanels Panels0200.aligned
    Panels0200.weightRows Panels0200.weights_checked ⟨5, by decide⟩
def b0201 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0201.block Panels0201.accepted Panels0201.integerPanels Panels0201.aligned
    Panels0201.weightRows Panels0201.weights_checked ⟨5, by decide⟩
def b0202 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0202.block Panels0202.accepted Panels0202.integerPanels Panels0202.aligned
    Panels0202.weightRows Panels0202.weights_checked ⟨5, by decide⟩
def b0203 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0203.block Panels0203.accepted Panels0203.integerPanels Panels0203.aligned
    Panels0203.weightRows Panels0203.weights_checked ⟨5, by decide⟩
def b0204 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0204.block Panels0204.accepted Panels0204.integerPanels Panels0204.aligned
    Panels0204.weightRows Panels0204.weights_checked ⟨5, by decide⟩
def b0205 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0205.block Panels0205.accepted Panels0205.integerPanels Panels0205.aligned
    Panels0205.weightRows Panels0205.weights_checked ⟨5, by decide⟩
def b0206 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0206.block Panels0206.accepted Panels0206.integerPanels Panels0206.aligned
    Panels0206.weightRows Panels0206.weights_checked ⟨5, by decide⟩
def b0207 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0207.block Panels0207.accepted Panels0207.integerPanels Panels0207.aligned
    Panels0207.weightRows Panels0207.weights_checked ⟨5, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0200, b0201, b0202, b0203, b0204, b0205, b0206, b0207]
theorem chain_checked : blockChainCheck (5150426141637181757933211818553/10^30) (6613076287325882991783239235141/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=197097638386149490458963921718094719306977892579773343238079087946601592905902911860217464953259940819676420053865828270845388122641921739372454767336964659782427064990321059077633717374447603009354348383200/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row05
namespace Row06
abbrev ζ : ℚ := 46511627906976744186046511627/10^30
def b0200 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0200.block Panels0200.accepted Panels0200.integerPanels Panels0200.aligned
    Panels0200.weightRows Panels0200.weights_checked ⟨6, by decide⟩
def b0201 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0201.block Panels0201.accepted Panels0201.integerPanels Panels0201.aligned
    Panels0201.weightRows Panels0201.weights_checked ⟨6, by decide⟩
def b0202 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0202.block Panels0202.accepted Panels0202.integerPanels Panels0202.aligned
    Panels0202.weightRows Panels0202.weights_checked ⟨6, by decide⟩
def b0203 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0203.block Panels0203.accepted Panels0203.integerPanels Panels0203.aligned
    Panels0203.weightRows Panels0203.weights_checked ⟨6, by decide⟩
def b0204 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0204.block Panels0204.accepted Panels0204.integerPanels Panels0204.aligned
    Panels0204.weightRows Panels0204.weights_checked ⟨6, by decide⟩
def b0205 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0205.block Panels0205.accepted Panels0205.integerPanels Panels0205.aligned
    Panels0205.weightRows Panels0205.weights_checked ⟨6, by decide⟩
def b0206 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0206.block Panels0206.accepted Panels0206.integerPanels Panels0206.aligned
    Panels0206.weightRows Panels0206.weights_checked ⟨6, by decide⟩
def b0207 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0207.block Panels0207.accepted Panels0207.integerPanels Panels0207.aligned
    Panels0207.weightRows Panels0207.weights_checked ⟨6, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0200, b0201, b0202, b0203, b0204, b0205, b0206, b0207]
theorem chain_checked : blockChainCheck (5150426141637181757933211818553/10^30) (6613076287325882991783239235141/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=200422401732483626687099541120183654434282644930600024027891958219095932721700024109656603189411078361420758977644128230886685417468914475073445977291236623065098185235957710502947685910906037534559143480800/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row06
namespace Row07
abbrev ζ : ℚ := 33898305084745762711864406779/10^30
def b0200 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0200.block Panels0200.accepted Panels0200.integerPanels Panels0200.aligned
    Panels0200.weightRows Panels0200.weights_checked ⟨7, by decide⟩
def b0201 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0201.block Panels0201.accepted Panels0201.integerPanels Panels0201.aligned
    Panels0201.weightRows Panels0201.weights_checked ⟨7, by decide⟩
def b0202 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0202.block Panels0202.accepted Panels0202.integerPanels Panels0202.aligned
    Panels0202.weightRows Panels0202.weights_checked ⟨7, by decide⟩
def b0203 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0203.block Panels0203.accepted Panels0203.integerPanels Panels0203.aligned
    Panels0203.weightRows Panels0203.weights_checked ⟨7, by decide⟩
def b0204 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0204.block Panels0204.accepted Panels0204.integerPanels Panels0204.aligned
    Panels0204.weightRows Panels0204.weights_checked ⟨7, by decide⟩
def b0205 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0205.block Panels0205.accepted Panels0205.integerPanels Panels0205.aligned
    Panels0205.weightRows Panels0205.weights_checked ⟨7, by decide⟩
def b0206 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0206.block Panels0206.accepted Panels0206.integerPanels Panels0206.aligned
    Panels0206.weightRows Panels0206.weights_checked ⟨7, by decide⟩
def b0207 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0207.block Panels0207.accepted Panels0207.integerPanels Panels0207.aligned
    Panels0207.weightRows Panels0207.weights_checked ⟨7, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0200, b0201, b0202, b0203, b0204, b0205, b0206, b0207]
theorem chain_checked : blockChainCheck (5150426141637181757933211818553/10^30) (6613076287325882991783239235141/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=202778287324864485703097944153972551668761948953126169421608988865406051451368851613052860359847647496526843613027273612856863227054733011586570089843364705007435467921845123617095346474884345493190258372640/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row07
namespace Row08
abbrev ζ : ℚ := 25316455696202531645569620253/10^30
def b0200 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0200.block Panels0200.accepted Panels0200.integerPanels Panels0200.aligned
    Panels0200.weightRows Panels0200.weights_checked ⟨8, by decide⟩
def b0201 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0201.block Panels0201.accepted Panels0201.integerPanels Panels0201.aligned
    Panels0201.weightRows Panels0201.weights_checked ⟨8, by decide⟩
def b0202 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0202.block Panels0202.accepted Panels0202.integerPanels Panels0202.aligned
    Panels0202.weightRows Panels0202.weights_checked ⟨8, by decide⟩
def b0203 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0203.block Panels0203.accepted Panels0203.integerPanels Panels0203.aligned
    Panels0203.weightRows Panels0203.weights_checked ⟨8, by decide⟩
def b0204 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0204.block Panels0204.accepted Panels0204.integerPanels Panels0204.aligned
    Panels0204.weightRows Panels0204.weights_checked ⟨8, by decide⟩
def b0205 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0205.block Panels0205.accepted Panels0205.integerPanels Panels0205.aligned
    Panels0205.weightRows Panels0205.weights_checked ⟨8, by decide⟩
def b0206 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0206.block Panels0206.accepted Panels0206.integerPanels Panels0206.aligned
    Panels0206.weightRows Panels0206.weights_checked ⟨8, by decide⟩
def b0207 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0207.block Panels0207.accepted Panels0207.integerPanels Panels0207.aligned
    Panels0207.weightRows Panels0207.weights_checked ⟨8, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0200, b0201, b0202, b0203, b0204, b0205, b0206, b0207]
theorem chain_checked : blockChainCheck (5150426141637181757933211818553/10^30) (6613076287325882991783239235141/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=204393838878381193402814190275992913098707716441716638246191338067489919355855214842987486300245019444601389849058490672534313699975822382335740274197639700070277887030621480627050530206408952457634684568600/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row08
namespace Row09
abbrev ζ : ℚ := 18691588785046728971962616822/10^30
def b0200 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0200.block Panels0200.accepted Panels0200.integerPanels Panels0200.aligned
    Panels0200.weightRows Panels0200.weights_checked ⟨9, by decide⟩
def b0201 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0201.block Panels0201.accepted Panels0201.integerPanels Panels0201.aligned
    Panels0201.weightRows Panels0201.weights_checked ⟨9, by decide⟩
def b0202 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0202.block Panels0202.accepted Panels0202.integerPanels Panels0202.aligned
    Panels0202.weightRows Panels0202.weights_checked ⟨9, by decide⟩
def b0203 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0203.block Panels0203.accepted Panels0203.integerPanels Panels0203.aligned
    Panels0203.weightRows Panels0203.weights_checked ⟨9, by decide⟩
def b0204 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0204.block Panels0204.accepted Panels0204.integerPanels Panels0204.aligned
    Panels0204.weightRows Panels0204.weights_checked ⟨9, by decide⟩
def b0205 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0205.block Panels0205.accepted Panels0205.integerPanels Panels0205.aligned
    Panels0205.weightRows Panels0205.weights_checked ⟨9, by decide⟩
def b0206 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0206.block Panels0206.accepted Panels0206.integerPanels Panels0206.aligned
    Panels0206.weightRows Panels0206.weights_checked ⟨9, by decide⟩
def b0207 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0207.block Panels0207.accepted Panels0207.integerPanels Panels0207.aligned
    Panels0207.weightRows Panels0207.weights_checked ⟨9, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0200, b0201, b0202, b0203, b0204, b0205, b0206, b0207]
theorem chain_checked : blockChainCheck (5150426141637181757933211818553/10^30) (6613076287325882991783239235141/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=205648029452618057465886248739026771373581850487616966545706871166203033995931178610837458529017715558004827505486026558426613473555272753486595076369796401423618165374781443695912589400316133173116497410000/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row09
namespace Row10
abbrev ζ : ℚ := 13793103448275862068965517241/10^30
def b0200 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0200.block Panels0200.accepted Panels0200.integerPanels Panels0200.aligned
    Panels0200.weightRows Panels0200.weights_checked ⟨10, by decide⟩
def b0201 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0201.block Panels0201.accepted Panels0201.integerPanels Panels0201.aligned
    Panels0201.weightRows Panels0201.weights_checked ⟨10, by decide⟩
def b0202 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0202.block Panels0202.accepted Panels0202.integerPanels Panels0202.aligned
    Panels0202.weightRows Panels0202.weights_checked ⟨10, by decide⟩
def b0203 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0203.block Panels0203.accepted Panels0203.integerPanels Panels0203.aligned
    Panels0203.weightRows Panels0203.weights_checked ⟨10, by decide⟩
def b0204 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0204.block Panels0204.accepted Panels0204.integerPanels Panels0204.aligned
    Panels0204.weightRows Panels0204.weights_checked ⟨10, by decide⟩
def b0205 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0205.block Panels0205.accepted Panels0205.integerPanels Panels0205.aligned
    Panels0205.weightRows Panels0205.weights_checked ⟨10, by decide⟩
def b0206 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0206.block Panels0206.accepted Panels0206.integerPanels Panels0206.aligned
    Panels0206.weightRows Panels0206.weights_checked ⟨10, by decide⟩
def b0207 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0207.block Panels0207.accepted Panels0207.integerPanels Panels0207.aligned
    Panels0207.weightRows Panels0207.weights_checked ⟨10, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0200, b0201, b0202, b0203, b0204, b0205, b0206, b0207]
theorem chain_checked : blockChainCheck (5150426141637181757933211818553/10^30) (6613076287325882991783239235141/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=206579351310178876768361182021806804646851909061655879784799723668507093126131288677439776186261276548898160527261181114153324862523316075174708715710545252088904984197141005106749775886491479102801333735080/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row10
namespace Row11
abbrev ζ : ℚ := 10152284263959390862944162436/10^30
def b0200 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0200.block Panels0200.accepted Panels0200.integerPanels Panels0200.aligned
    Panels0200.weightRows Panels0200.weights_checked ⟨11, by decide⟩
def b0201 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0201.block Panels0201.accepted Panels0201.integerPanels Panels0201.aligned
    Panels0201.weightRows Panels0201.weights_checked ⟨11, by decide⟩
def b0202 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0202.block Panels0202.accepted Panels0202.integerPanels Panels0202.aligned
    Panels0202.weightRows Panels0202.weights_checked ⟨11, by decide⟩
def b0203 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0203.block Panels0203.accepted Panels0203.integerPanels Panels0203.aligned
    Panels0203.weightRows Panels0203.weights_checked ⟨11, by decide⟩
def b0204 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0204.block Panels0204.accepted Panels0204.integerPanels Panels0204.aligned
    Panels0204.weightRows Panels0204.weights_checked ⟨11, by decide⟩
def b0205 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0205.block Panels0205.accepted Panels0205.integerPanels Panels0205.aligned
    Panels0205.weightRows Panels0205.weights_checked ⟨11, by decide⟩
def b0206 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0206.block Panels0206.accepted Panels0206.integerPanels Panels0206.aligned
    Panels0206.weightRows Panels0206.weights_checked ⟨11, by decide⟩
def b0207 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0207.block Panels0207.accepted Panels0207.integerPanels Panels0207.aligned
    Panels0207.weightRows Panels0207.weights_checked ⟨11, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0200, b0201, b0202, b0203, b0204, b0205, b0206, b0207]
theorem chain_checked : blockChainCheck (5150426141637181757933211818553/10^30) (6613076287325882991783239235141/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=207273748545318449153312394083716277387548821636899221865999468695671101452372739169662798870624274079472375541257177019698607856372727845692323236843877650212857640533381953146802233593947599577185404252280/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row11
namespace Row12
abbrev ζ : ℚ := 9950248756218905472636815920/10^30
def b0200 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0200.block Panels0200.accepted Panels0200.integerPanels Panels0200.aligned
    Panels0200.weightRows Panels0200.weights_checked ⟨12, by decide⟩
def b0201 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0201.block Panels0201.accepted Panels0201.integerPanels Panels0201.aligned
    Panels0201.weightRows Panels0201.weights_checked ⟨12, by decide⟩
def b0202 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0202.block Panels0202.accepted Panels0202.integerPanels Panels0202.aligned
    Panels0202.weightRows Panels0202.weights_checked ⟨12, by decide⟩
def b0203 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0203.block Panels0203.accepted Panels0203.integerPanels Panels0203.aligned
    Panels0203.weightRows Panels0203.weights_checked ⟨12, by decide⟩
def b0204 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0204.block Panels0204.accepted Panels0204.integerPanels Panels0204.aligned
    Panels0204.weightRows Panels0204.weights_checked ⟨12, by decide⟩
def b0205 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0205.block Panels0205.accepted Panels0205.integerPanels Panels0205.aligned
    Panels0205.weightRows Panels0205.weights_checked ⟨12, by decide⟩
def b0206 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0206.block Panels0206.accepted Panels0206.integerPanels Panels0206.aligned
    Panels0206.weightRows Panels0206.weights_checked ⟨12, by decide⟩
def b0207 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0207.block Panels0207.accepted Panels0207.integerPanels Panels0207.aligned
    Panels0207.weightRows Panels0207.weights_checked ⟨12, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0200, b0201, b0202, b0203, b0204, b0205, b0206, b0207]
theorem chain_checked : blockChainCheck (5150426141637181757933211818553/10^30) (6613076287325882991783239235141/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=207312336618155147966566664347398156364487518435693300815331632654867025574548749249260730848882254866367402273003522757911262879048155635653178865288773593579896930476294518345092919654117733010452419443080/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row12
#print axioms Row12.segment
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments025
