module

public import BecknerOnofri.EntropyHeatCheckedWeights
public import BecknerOnofri.EntropyHeatSegments
public import BecknerOnofri.EntropyHeatCertificate.Panels0104
public import BecknerOnofri.EntropyHeatCertificate.Panels0105
public import BecknerOnofri.EntropyHeatCertificate.Panels0106
public import BecknerOnofri.EntropyHeatCertificate.Panels0107
public import BecknerOnofri.EntropyHeatCertificate.Panels0108
public import BecknerOnofri.EntropyHeatCertificate.Panels0109
public import BecknerOnofri.EntropyHeatCertificate.Panels0110
public import BecknerOnofri.EntropyHeatCertificate.Panels0111

@[expose] public section
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments013
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace Row00
abbrev ζ : ℚ := 285714285714285714285714285714/10^30
def b0104 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0104.block Panels0104.accepted Panels0104.integerPanels Panels0104.aligned
    Panels0104.weightRows Panels0104.weights_checked ⟨0, by decide⟩
def b0105 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0105.block Panels0105.accepted Panels0105.integerPanels Panels0105.aligned
    Panels0105.weightRows Panels0105.weights_checked ⟨0, by decide⟩
def b0106 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0106.block Panels0106.accepted Panels0106.integerPanels Panels0106.aligned
    Panels0106.weightRows Panels0106.weights_checked ⟨0, by decide⟩
def b0107 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0107.block Panels0107.accepted Panels0107.integerPanels Panels0107.aligned
    Panels0107.weightRows Panels0107.weights_checked ⟨0, by decide⟩
def b0108 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0108.block Panels0108.accepted Panels0108.integerPanels Panels0108.aligned
    Panels0108.weightRows Panels0108.weights_checked ⟨0, by decide⟩
def b0109 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0109.block Panels0109.accepted Panels0109.integerPanels Panels0109.aligned
    Panels0109.weightRows Panels0109.weights_checked ⟨0, by decide⟩
def b0110 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0110.block Panels0110.accepted Panels0110.integerPanels Panels0110.aligned
    Panels0110.weightRows Panels0110.weights_checked ⟨0, by decide⟩
def b0111 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0111.block Panels0111.accepted Panels0111.integerPanels Panels0111.aligned
    Panels0111.weightRows Panels0111.weights_checked ⟨0, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0104, b0105, b0106, b0107, b0108, b0109, b0110, b0111]
theorem chain_checked : blockChainCheck (256518525847052817488239228851/10^30) (329366257060761223357774101419/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=5563709866826960911403235695496097010241258181455884245347145361539537336692023049673121952032877518279058464542219589979147793970552823908063035745610646570891401842320010482066419675992778860035348431742193/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row00
namespace Row01
abbrev ζ : ℚ := 222222222222222222222222222222/10^30
def b0104 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0104.block Panels0104.accepted Panels0104.integerPanels Panels0104.aligned
    Panels0104.weightRows Panels0104.weights_checked ⟨1, by decide⟩
def b0105 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0105.block Panels0105.accepted Panels0105.integerPanels Panels0105.aligned
    Panels0105.weightRows Panels0105.weights_checked ⟨1, by decide⟩
def b0106 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0106.block Panels0106.accepted Panels0106.integerPanels Panels0106.aligned
    Panels0106.weightRows Panels0106.weights_checked ⟨1, by decide⟩
def b0107 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0107.block Panels0107.accepted Panels0107.integerPanels Panels0107.aligned
    Panels0107.weightRows Panels0107.weights_checked ⟨1, by decide⟩
def b0108 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0108.block Panels0108.accepted Panels0108.integerPanels Panels0108.aligned
    Panels0108.weightRows Panels0108.weights_checked ⟨1, by decide⟩
def b0109 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0109.block Panels0109.accepted Panels0109.integerPanels Panels0109.aligned
    Panels0109.weightRows Panels0109.weights_checked ⟨1, by decide⟩
def b0110 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0110.block Panels0110.accepted Panels0110.integerPanels Panels0110.aligned
    Panels0110.weightRows Panels0110.weights_checked ⟨1, by decide⟩
def b0111 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0111.block Panels0111.accepted Panels0111.integerPanels Panels0111.aligned
    Panels0111.weightRows Panels0111.weights_checked ⟨1, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0104, b0105, b0106, b0107, b0108, b0109, b0110, b0111]
theorem chain_checked : blockChainCheck (256518525847052817488239228851/10^30) (329366257060761223357774101419/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=1504443691797288361504476336100658186180578434545179423325353604068996179619694336140981957329127225856107856253189471079816593167644065320028827367130964726494482681352317955032428381459462955305530768496086872/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row01
namespace Row02
abbrev ζ : ℚ := 153846153846153846153846153846/10^30
def b0104 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0104.block Panels0104.accepted Panels0104.integerPanels Panels0104.aligned
    Panels0104.weightRows Panels0104.weights_checked ⟨2, by decide⟩
def b0105 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0105.block Panels0105.accepted Panels0105.integerPanels Panels0105.aligned
    Panels0105.weightRows Panels0105.weights_checked ⟨2, by decide⟩
def b0106 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0106.block Panels0106.accepted Panels0106.integerPanels Panels0106.aligned
    Panels0106.weightRows Panels0106.weights_checked ⟨2, by decide⟩
def b0107 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0107.block Panels0107.accepted Panels0107.integerPanels Panels0107.aligned
    Panels0107.weightRows Panels0107.weights_checked ⟨2, by decide⟩
def b0108 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0108.block Panels0108.accepted Panels0108.integerPanels Panels0108.aligned
    Panels0108.weightRows Panels0108.weights_checked ⟨2, by decide⟩
def b0109 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0109.block Panels0109.accepted Panels0109.integerPanels Panels0109.aligned
    Panels0109.weightRows Panels0109.weights_checked ⟨2, by decide⟩
def b0110 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0110.block Panels0110.accepted Panels0110.integerPanels Panels0110.aligned
    Panels0110.weightRows Panels0110.weights_checked ⟨2, by decide⟩
def b0111 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0111.block Panels0111.accepted Panels0111.integerPanels Panels0111.aligned
    Panels0111.weightRows Panels0111.weights_checked ⟨2, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0104, b0105, b0106, b0107, b0108, b0109, b0110, b0111]
theorem chain_checked : blockChainCheck (256518525847052817488239228851/10^30) (329366257060761223357774101419/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=33573312575380345197180509440340509192235040684970828409175250970326278610933452552711621867142621173191128723257421513476666910423955186183654080558382557077928319046709272462908997044292810124382551848041587704/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row02
namespace Row03
abbrev ζ : ℚ := 117647058823529411764705882352/10^30
def b0104 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0104.block Panels0104.accepted Panels0104.integerPanels Panels0104.aligned
    Panels0104.weightRows Panels0104.weights_checked ⟨3, by decide⟩
def b0105 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0105.block Panels0105.accepted Panels0105.integerPanels Panels0105.aligned
    Panels0105.weightRows Panels0105.weights_checked ⟨3, by decide⟩
def b0106 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0106.block Panels0106.accepted Panels0106.integerPanels Panels0106.aligned
    Panels0106.weightRows Panels0106.weights_checked ⟨3, by decide⟩
def b0107 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0107.block Panels0107.accepted Panels0107.integerPanels Panels0107.aligned
    Panels0107.weightRows Panels0107.weights_checked ⟨3, by decide⟩
def b0108 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0108.block Panels0108.accepted Panels0108.integerPanels Panels0108.aligned
    Panels0108.weightRows Panels0108.weights_checked ⟨3, by decide⟩
def b0109 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0109.block Panels0109.accepted Panels0109.integerPanels Panels0109.aligned
    Panels0109.weightRows Panels0109.weights_checked ⟨3, by decide⟩
def b0110 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0110.block Panels0110.accepted Panels0110.integerPanels Panels0110.aligned
    Panels0110.weightRows Panels0110.weights_checked ⟨3, by decide⟩
def b0111 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0111.block Panels0111.accepted Panels0111.integerPanels Panels0111.aligned
    Panels0111.weightRows Panels0111.weights_checked ⟨3, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0104, b0105, b0106, b0107, b0108, b0109, b0110, b0111]
theorem chain_checked : blockChainCheck (256518525847052817488239228851/10^30) (329366257060761223357774101419/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=105050052133433119995448698863672179108451906452259442397522421662647041217043161565270893602332874706760008148206744923751405571868401984815122804118054332460666859347964869404638334047074035867387141526422852992/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row03
namespace Row04
abbrev ζ : ℚ := 86956521739130434782608695652/10^30
def b0104 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0104.block Panels0104.accepted Panels0104.integerPanels Panels0104.aligned
    Panels0104.weightRows Panels0104.weights_checked ⟨4, by decide⟩
def b0105 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0105.block Panels0105.accepted Panels0105.integerPanels Panels0105.aligned
    Panels0105.weightRows Panels0105.weights_checked ⟨4, by decide⟩
def b0106 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0106.block Panels0106.accepted Panels0106.integerPanels Panels0106.aligned
    Panels0106.weightRows Panels0106.weights_checked ⟨4, by decide⟩
def b0107 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0107.block Panels0107.accepted Panels0107.integerPanels Panels0107.aligned
    Panels0107.weightRows Panels0107.weights_checked ⟨4, by decide⟩
def b0108 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0108.block Panels0108.accepted Panels0108.integerPanels Panels0108.aligned
    Panels0108.weightRows Panels0108.weights_checked ⟨4, by decide⟩
def b0109 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0109.block Panels0109.accepted Panels0109.integerPanels Panels0109.aligned
    Panels0109.weightRows Panels0109.weights_checked ⟨4, by decide⟩
def b0110 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0110.block Panels0110.accepted Panels0110.integerPanels Panels0110.aligned
    Panels0110.weightRows Panels0110.weights_checked ⟨4, by decide⟩
def b0111 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0111.block Panels0111.accepted Panels0111.integerPanels Panels0111.aligned
    Panels0111.weightRows Panels0111.weights_checked ⟨4, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0104, b0105, b0106, b0107, b0108, b0109, b0110, b0111]
theorem chain_checked : blockChainCheck (256518525847052817488239228851/10^30) (329366257060761223357774101419/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=235269415180927259765986563180303207587847719621513075053066825458627614522286929536118263836508409833343125887986525745951138350365100330310954918674668172241565700064450148232314192317952998833731372663646362192/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row04
namespace Row05
abbrev ζ : ℚ := 64516129032258064516129032258/10^30
def b0104 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0104.block Panels0104.accepted Panels0104.integerPanels Panels0104.aligned
    Panels0104.weightRows Panels0104.weights_checked ⟨5, by decide⟩
def b0105 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0105.block Panels0105.accepted Panels0105.integerPanels Panels0105.aligned
    Panels0105.weightRows Panels0105.weights_checked ⟨5, by decide⟩
def b0106 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0106.block Panels0106.accepted Panels0106.integerPanels Panels0106.aligned
    Panels0106.weightRows Panels0106.weights_checked ⟨5, by decide⟩
def b0107 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0107.block Panels0107.accepted Panels0107.integerPanels Panels0107.aligned
    Panels0107.weightRows Panels0107.weights_checked ⟨5, by decide⟩
def b0108 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0108.block Panels0108.accepted Panels0108.integerPanels Panels0108.aligned
    Panels0108.weightRows Panels0108.weights_checked ⟨5, by decide⟩
def b0109 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0109.block Panels0109.accepted Panels0109.integerPanels Panels0109.aligned
    Panels0109.weightRows Panels0109.weights_checked ⟨5, by decide⟩
def b0110 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0110.block Panels0110.accepted Panels0110.integerPanels Panels0110.aligned
    Panels0110.weightRows Panels0110.weights_checked ⟨5, by decide⟩
def b0111 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0111.block Panels0111.accepted Panels0111.integerPanels Panels0111.aligned
    Panels0111.weightRows Panels0111.weights_checked ⟨5, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0104, b0105, b0106, b0107, b0108, b0109, b0110, b0111]
theorem chain_checked : blockChainCheck (256518525847052817488239228851/10^30) (329366257060761223357774101419/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=395597658720013783673701096250435388265189062091746393560527028029167554406970925271949183899710506248754354510324649189074631162978140830656051185925461745886001462176225964689271266145205839481251911928690081320/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row05
namespace Row06
abbrev ζ : ℚ := 46511627906976744186046511627/10^30
def b0104 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0104.block Panels0104.accepted Panels0104.integerPanels Panels0104.aligned
    Panels0104.weightRows Panels0104.weights_checked ⟨6, by decide⟩
def b0105 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0105.block Panels0105.accepted Panels0105.integerPanels Panels0105.aligned
    Panels0105.weightRows Panels0105.weights_checked ⟨6, by decide⟩
def b0106 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0106.block Panels0106.accepted Panels0106.integerPanels Panels0106.aligned
    Panels0106.weightRows Panels0106.weights_checked ⟨6, by decide⟩
def b0107 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0107.block Panels0107.accepted Panels0107.integerPanels Panels0107.aligned
    Panels0107.weightRows Panels0107.weights_checked ⟨6, by decide⟩
def b0108 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0108.block Panels0108.accepted Panels0108.integerPanels Panels0108.aligned
    Panels0108.weightRows Panels0108.weights_checked ⟨6, by decide⟩
def b0109 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0109.block Panels0109.accepted Panels0109.integerPanels Panels0109.aligned
    Panels0109.weightRows Panels0109.weights_checked ⟨6, by decide⟩
def b0110 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0110.block Panels0110.accepted Panels0110.integerPanels Panels0110.aligned
    Panels0110.weightRows Panels0110.weights_checked ⟨6, by decide⟩
def b0111 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0111.block Panels0111.accepted Panels0111.integerPanels Panels0111.aligned
    Panels0111.weightRows Panels0111.weights_checked ⟨6, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0104, b0105, b0106, b0107, b0108, b0109, b0110, b0111]
theorem chain_checked : blockChainCheck (256518525847052817488239228851/10^30) (329366257060761223357774101419/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=579787745859650095433565938789512152410879032331116975452046161336340963001622859894486386812384151071915281669770252923223060031743645062704415281979496477333112849796223661428100362344655039103215345753785400592/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row06
namespace Row07
abbrev ζ : ℚ := 33898305084745762711864406779/10^30
def b0104 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0104.block Panels0104.accepted Panels0104.integerPanels Panels0104.aligned
    Panels0104.weightRows Panels0104.weights_checked ⟨7, by decide⟩
def b0105 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0105.block Panels0105.accepted Panels0105.integerPanels Panels0105.aligned
    Panels0105.weightRows Panels0105.weights_checked ⟨7, by decide⟩
def b0106 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0106.block Panels0106.accepted Panels0106.integerPanels Panels0106.aligned
    Panels0106.weightRows Panels0106.weights_checked ⟨7, by decide⟩
def b0107 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0107.block Panels0107.accepted Panels0107.integerPanels Panels0107.aligned
    Panels0107.weightRows Panels0107.weights_checked ⟨7, by decide⟩
def b0108 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0108.block Panels0108.accepted Panels0108.integerPanels Panels0108.aligned
    Panels0108.weightRows Panels0108.weights_checked ⟨7, by decide⟩
def b0109 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0109.block Panels0109.accepted Panels0109.integerPanels Panels0109.aligned
    Panels0109.weightRows Panels0109.weights_checked ⟨7, by decide⟩
def b0110 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0110.block Panels0110.accepted Panels0110.integerPanels Panels0110.aligned
    Panels0110.weightRows Panels0110.weights_checked ⟨7, by decide⟩
def b0111 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0111.block Panels0111.accepted Panels0111.integerPanels Panels0111.aligned
    Panels0111.weightRows Panels0111.weights_checked ⟨7, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0104, b0105, b0106, b0107, b0108, b0109, b0110, b0111]
theorem chain_checked : blockChainCheck (256518525847052817488239228851/10^30) (329366257060761223357774101419/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=745847377648592461422728628739805783114994607466685196195873194927222832183586962809406925091666091610843115721166571924777165317433708984939340476433711690472318159012592789168825824445478233364429869729781123088/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row07
namespace Row08
abbrev ζ : ℚ := 25316455696202531645569620253/10^30
def b0104 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0104.block Panels0104.accepted Panels0104.integerPanels Panels0104.aligned
    Panels0104.weightRows Panels0104.weights_checked ⟨8, by decide⟩
def b0105 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0105.block Panels0105.accepted Panels0105.integerPanels Panels0105.aligned
    Panels0105.weightRows Panels0105.weights_checked ⟨8, by decide⟩
def b0106 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0106.block Panels0106.accepted Panels0106.integerPanels Panels0106.aligned
    Panels0106.weightRows Panels0106.weights_checked ⟨8, by decide⟩
def b0107 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0107.block Panels0107.accepted Panels0107.integerPanels Panels0107.aligned
    Panels0107.weightRows Panels0107.weights_checked ⟨8, by decide⟩
def b0108 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0108.block Panels0108.accepted Panels0108.integerPanels Panels0108.aligned
    Panels0108.weightRows Panels0108.weights_checked ⟨8, by decide⟩
def b0109 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0109.block Panels0109.accepted Panels0109.integerPanels Panels0109.aligned
    Panels0109.weightRows Panels0109.weights_checked ⟨8, by decide⟩
def b0110 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0110.block Panels0110.accepted Panels0110.integerPanels Panels0110.aligned
    Panels0110.weightRows Panels0110.weights_checked ⟨8, by decide⟩
def b0111 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0111.block Panels0111.accepted Panels0111.integerPanels Panels0111.aligned
    Panels0111.weightRows Panels0111.weights_checked ⟨8, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0104, b0105, b0106, b0107, b0108, b0109, b0110, b0111]
theorem chain_checked : blockChainCheck (256518525847052817488239228851/10^30) (329366257060761223357774101419/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=879264571189344568999056596177460308402537149273344700958827853716157463957792585637544268949889566601706230783909824503782539753350761008550665526636069518531433170957135702913532054778770381608132223440132469200/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row08
namespace Row09
abbrev ζ : ℚ := 18691588785046728971962616822/10^30
def b0104 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0104.block Panels0104.accepted Panels0104.integerPanels Panels0104.aligned
    Panels0104.weightRows Panels0104.weights_checked ⟨9, by decide⟩
def b0105 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0105.block Panels0105.accepted Panels0105.integerPanels Panels0105.aligned
    Panels0105.weightRows Panels0105.weights_checked ⟨9, by decide⟩
def b0106 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0106.block Panels0106.accepted Panels0106.integerPanels Panels0106.aligned
    Panels0106.weightRows Panels0106.weights_checked ⟨9, by decide⟩
def b0107 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0107.block Panels0107.accepted Panels0107.integerPanels Panels0107.aligned
    Panels0107.weightRows Panels0107.weights_checked ⟨9, by decide⟩
def b0108 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0108.block Panels0108.accepted Panels0108.integerPanels Panels0108.aligned
    Panels0108.weightRows Panels0108.weights_checked ⟨9, by decide⟩
def b0109 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0109.block Panels0109.accepted Panels0109.integerPanels Panels0109.aligned
    Panels0109.weightRows Panels0109.weights_checked ⟨9, by decide⟩
def b0110 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0110.block Panels0110.accepted Panels0110.integerPanels Panels0110.aligned
    Panels0110.weightRows Panels0110.weights_checked ⟨9, by decide⟩
def b0111 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0111.block Panels0111.accepted Panels0111.integerPanels Panels0111.aligned
    Panels0111.weightRows Panels0111.weights_checked ⟨9, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0104, b0105, b0106, b0107, b0108, b0109, b0110, b0111]
theorem chain_checked : blockChainCheck (256518525847052817488239228851/10^30) (329366257060761223357774101419/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=994865783019028779543892130624528536502928297599286860479445713606430878705366535425285164697567004065792699447328394786210363525617451851713068605159898518200652494509001663195277602740464922202448588039454497272/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row09
namespace Row10
abbrev ζ : ℚ := 13793103448275862068965517241/10^30
def b0104 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0104.block Panels0104.accepted Panels0104.integerPanels Panels0104.aligned
    Panels0104.weightRows Panels0104.weights_checked ⟨10, by decide⟩
def b0105 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0105.block Panels0105.accepted Panels0105.integerPanels Panels0105.aligned
    Panels0105.weightRows Panels0105.weights_checked ⟨10, by decide⟩
def b0106 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0106.block Panels0106.accepted Panels0106.integerPanels Panels0106.aligned
    Panels0106.weightRows Panels0106.weights_checked ⟨10, by decide⟩
def b0107 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0107.block Panels0107.accepted Panels0107.integerPanels Panels0107.aligned
    Panels0107.weightRows Panels0107.weights_checked ⟨10, by decide⟩
def b0108 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0108.block Panels0108.accepted Panels0108.integerPanels Panels0108.aligned
    Panels0108.weightRows Panels0108.weights_checked ⟨10, by decide⟩
def b0109 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0109.block Panels0109.accepted Panels0109.integerPanels Panels0109.aligned
    Panels0109.weightRows Panels0109.weights_checked ⟨10, by decide⟩
def b0110 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0110.block Panels0110.accepted Panels0110.integerPanels Panels0110.aligned
    Panels0110.weightRows Panels0110.weights_checked ⟨10, by decide⟩
def b0111 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0111.block Panels0111.accepted Panels0111.integerPanels Panels0111.aligned
    Panels0111.weightRows Panels0111.weights_checked ⟨10, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0104, b0105, b0106, b0107, b0108, b0109, b0110, b0111]
theorem chain_checked : blockChainCheck (256518525847052817488239228851/10^30) (329366257060761223357774101419/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=1087963598519405128541876665402378765110083839445728149559980012613692710206707955450945514097942137354057314777965150843611788803964364874073423868204255062349727453153994392438791527181318479818467121324725239184/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row10
namespace Row11
abbrev ζ : ℚ := 10152284263959390862944162436/10^30
def b0104 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0104.block Panels0104.accepted Panels0104.integerPanels Panels0104.aligned
    Panels0104.weightRows Panels0104.weights_checked ⟨11, by decide⟩
def b0105 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0105.block Panels0105.accepted Panels0105.integerPanels Panels0105.aligned
    Panels0105.weightRows Panels0105.weights_checked ⟨11, by decide⟩
def b0106 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0106.block Panels0106.accepted Panels0106.integerPanels Panels0106.aligned
    Panels0106.weightRows Panels0106.weights_checked ⟨11, by decide⟩
def b0107 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0107.block Panels0107.accepted Panels0107.integerPanels Panels0107.aligned
    Panels0107.weightRows Panels0107.weights_checked ⟨11, by decide⟩
def b0108 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0108.block Panels0108.accepted Panels0108.integerPanels Panels0108.aligned
    Panels0108.weightRows Panels0108.weights_checked ⟨11, by decide⟩
def b0109 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0109.block Panels0109.accepted Panels0109.integerPanels Panels0109.aligned
    Panels0109.weightRows Panels0109.weights_checked ⟨11, by decide⟩
def b0110 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0110.block Panels0110.accepted Panels0110.integerPanels Panels0110.aligned
    Panels0110.weightRows Panels0110.weights_checked ⟨11, by decide⟩
def b0111 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0111.block Panels0111.accepted Panels0111.integerPanels Panels0111.aligned
    Panels0111.weightRows Panels0111.weights_checked ⟨11, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0104, b0105, b0106, b0107, b0108, b0109, b0110, b0111]
theorem chain_checked : blockChainCheck (256518525847052817488239228851/10^30) (329366257060761223357774101419/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=1161598462812044627260215752586731768882668703360806231111569411990076277006832655656646081402607366427379511344001701666348550736653619813192248471646406116211166567071924352123915860673042841093307793206783238864/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row11
namespace Row12
abbrev ζ : ℚ := 9950248756218905472636815920/10^30
def b0104 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0104.block Panels0104.accepted Panels0104.integerPanels Panels0104.aligned
    Panels0104.weightRows Panels0104.weights_checked ⟨12, by decide⟩
def b0105 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0105.block Panels0105.accepted Panels0105.integerPanels Panels0105.aligned
    Panels0105.weightRows Panels0105.weights_checked ⟨12, by decide⟩
def b0106 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0106.block Panels0106.accepted Panels0106.integerPanels Panels0106.aligned
    Panels0106.weightRows Panels0106.weights_checked ⟨12, by decide⟩
def b0107 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0107.block Panels0107.accepted Panels0107.integerPanels Panels0107.aligned
    Panels0107.weightRows Panels0107.weights_checked ⟨12, by decide⟩
def b0108 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0108.block Panels0108.accepted Panels0108.integerPanels Panels0108.aligned
    Panels0108.weightRows Panels0108.weights_checked ⟨12, by decide⟩
def b0109 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0109.block Panels0109.accepted Panels0109.integerPanels Panels0109.aligned
    Panels0109.weightRows Panels0109.weights_checked ⟨12, by decide⟩
def b0110 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0110.block Panels0110.accepted Panels0110.integerPanels Panels0110.aligned
    Panels0110.weightRows Panels0110.weights_checked ⟨12, by decide⟩
def b0111 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0111.block Panels0111.accepted Panels0111.integerPanels Panels0111.aligned
    Panels0111.weightRows Panels0111.weights_checked ⟨12, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0104, b0105, b0106, b0107, b0108, b0109, b0110, b0111]
theorem chain_checked : blockChainCheck (256518525847052817488239228851/10^30) (329366257060761223357774101419/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=1165799039660544688299493385760010239404160623730412623915217522733283340260795545387483942241415316339815623787271985420432622628982675018358552770119443952537740608235431619254132327840147613289300057553568240256/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row12
#print axioms Row12.segment
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments013
