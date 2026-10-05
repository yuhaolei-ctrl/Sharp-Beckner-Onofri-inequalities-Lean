module

public import BecknerOnofri.EntropyHeatCheckedWeights
public import BecknerOnofri.EntropyHeatSegments
public import BecknerOnofri.EntropyHeatCertificate.Panels0184
public import BecknerOnofri.EntropyHeatCertificate.Panels0185
public import BecknerOnofri.EntropyHeatCertificate.Panels0186
public import BecknerOnofri.EntropyHeatCertificate.Panels0187
public import BecknerOnofri.EntropyHeatCertificate.Panels0188
public import BecknerOnofri.EntropyHeatCertificate.Panels0189
public import BecknerOnofri.EntropyHeatCertificate.Panels0190
public import BecknerOnofri.EntropyHeatCertificate.Panels0191

@[expose] public section
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments023
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace Row00
abbrev ζ : ℚ := 285714285714285714285714285714/10^30
def b0184 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0184.block Panels0184.accepted Panels0184.integerPanels Panels0184.aligned
    Panels0184.weightRows Panels0184.weights_checked ⟨0, by decide⟩
def b0185 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0185.block Panels0185.accepted Panels0185.integerPanels Panels0185.aligned
    Panels0185.weightRows Panels0185.weights_checked ⟨0, by decide⟩
def b0186 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0186.block Panels0186.accepted Panels0186.integerPanels Panels0186.aligned
    Panels0186.weightRows Panels0186.weights_checked ⟨0, by decide⟩
def b0187 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0187.block Panels0187.accepted Panels0187.integerPanels Panels0187.aligned
    Panels0187.weightRows Panels0187.weights_checked ⟨0, by decide⟩
def b0188 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0188.block Panels0188.accepted Panels0188.integerPanels Panels0188.aligned
    Panels0188.weightRows Panels0188.weights_checked ⟨0, by decide⟩
def b0189 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0189.block Panels0189.accepted Panels0189.integerPanels Panels0189.aligned
    Panels0189.weightRows Panels0189.weights_checked ⟨0, by decide⟩
def b0190 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0190.block Panels0190.accepted Panels0190.integerPanels Panels0190.aligned
    Panels0190.weightRows Panels0190.weights_checked ⟨0, by decide⟩
def b0191 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0191.block Panels0191.accepted Panels0191.integerPanels Panels0191.aligned
    Panels0191.weightRows Panels0191.weights_checked ⟨0, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0184, b0185, b0186, b0187, b0188, b0189, b0190, b0191]
theorem chain_checked : blockChainCheck (3124082007475528121207110426578/10^30) (4011278304969667087671142319973/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=76000260877819303908462606350739193492973928439577732574491659839884386860362655816006628489175703954307762818862236653365173796555365351318050942265145929449188416656463408174494646880828962680514063209415022/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row00
namespace Row01
abbrev ζ : ℚ := 222222222222222222222222222222/10^30
def b0184 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0184.block Panels0184.accepted Panels0184.integerPanels Panels0184.aligned
    Panels0184.weightRows Panels0184.weights_checked ⟨1, by decide⟩
def b0185 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0185.block Panels0185.accepted Panels0185.integerPanels Panels0185.aligned
    Panels0185.weightRows Panels0185.weights_checked ⟨1, by decide⟩
def b0186 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0186.block Panels0186.accepted Panels0186.integerPanels Panels0186.aligned
    Panels0186.weightRows Panels0186.weights_checked ⟨1, by decide⟩
def b0187 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0187.block Panels0187.accepted Panels0187.integerPanels Panels0187.aligned
    Panels0187.weightRows Panels0187.weights_checked ⟨1, by decide⟩
def b0188 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0188.block Panels0188.accepted Panels0188.integerPanels Panels0188.aligned
    Panels0188.weightRows Panels0188.weights_checked ⟨1, by decide⟩
def b0189 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0189.block Panels0189.accepted Panels0189.integerPanels Panels0189.aligned
    Panels0189.weightRows Panels0189.weights_checked ⟨1, by decide⟩
def b0190 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0190.block Panels0190.accepted Panels0190.integerPanels Panels0190.aligned
    Panels0190.weightRows Panels0190.weights_checked ⟨1, by decide⟩
def b0191 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0191.block Panels0191.accepted Panels0191.integerPanels Panels0191.aligned
    Panels0191.weightRows Panels0191.weights_checked ⟨1, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0184, b0185, b0186, b0187, b0188, b0189, b0190, b0191]
theorem chain_checked : blockChainCheck (3124082007475528121207110426578/10^30) (4011278304969667087671142319973/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=84145174530631356798151841204912762688005321422486223168796523977131026678377122904845492935537292231154363593361510380884459695703497122048836802361806324690610479719630730049823355939125743996981506286118798/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row01
namespace Row02
abbrev ζ : ℚ := 153846153846153846153846153846/10^30
def b0184 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0184.block Panels0184.accepted Panels0184.integerPanels Panels0184.aligned
    Panels0184.weightRows Panels0184.weights_checked ⟨2, by decide⟩
def b0185 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0185.block Panels0185.accepted Panels0185.integerPanels Panels0185.aligned
    Panels0185.weightRows Panels0185.weights_checked ⟨2, by decide⟩
def b0186 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0186.block Panels0186.accepted Panels0186.integerPanels Panels0186.aligned
    Panels0186.weightRows Panels0186.weights_checked ⟨2, by decide⟩
def b0187 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0187.block Panels0187.accepted Panels0187.integerPanels Panels0187.aligned
    Panels0187.weightRows Panels0187.weights_checked ⟨2, by decide⟩
def b0188 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0188.block Panels0188.accepted Panels0188.integerPanels Panels0188.aligned
    Panels0188.weightRows Panels0188.weights_checked ⟨2, by decide⟩
def b0189 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0189.block Panels0189.accepted Panels0189.integerPanels Panels0189.aligned
    Panels0189.weightRows Panels0189.weights_checked ⟨2, by decide⟩
def b0190 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0190.block Panels0190.accepted Panels0190.integerPanels Panels0190.aligned
    Panels0190.weightRows Panels0190.weights_checked ⟨2, by decide⟩
def b0191 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0191.block Panels0191.accepted Panels0191.integerPanels Panels0191.aligned
    Panels0191.weightRows Panels0191.weights_checked ⟨2, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0184, b0185, b0186, b0187, b0188, b0189, b0190, b0191]
theorem chain_checked : blockChainCheck (3124082007475528121207110426578/10^30) (4011278304969667087671142319973/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=93686040627354282032686444872327757752363746416996135488987545049911284958395546575302765263580556664516459188730818933868765603523056609641913251928299807621626500852059005480406130139337402651968747088574606/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row02
namespace Row03
abbrev ζ : ℚ := 117647058823529411764705882352/10^30
def b0184 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0184.block Panels0184.accepted Panels0184.integerPanels Panels0184.aligned
    Panels0184.weightRows Panels0184.weights_checked ⟨3, by decide⟩
def b0185 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0185.block Panels0185.accepted Panels0185.integerPanels Panels0185.aligned
    Panels0185.weightRows Panels0185.weights_checked ⟨3, by decide⟩
def b0186 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0186.block Panels0186.accepted Panels0186.integerPanels Panels0186.aligned
    Panels0186.weightRows Panels0186.weights_checked ⟨3, by decide⟩
def b0187 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0187.block Panels0187.accepted Panels0187.integerPanels Panels0187.aligned
    Panels0187.weightRows Panels0187.weights_checked ⟨3, by decide⟩
def b0188 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0188.block Panels0188.accepted Panels0188.integerPanels Panels0188.aligned
    Panels0188.weightRows Panels0188.weights_checked ⟨3, by decide⟩
def b0189 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0189.block Panels0189.accepted Panels0189.integerPanels Panels0189.aligned
    Panels0189.weightRows Panels0189.weights_checked ⟨3, by decide⟩
def b0190 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0190.block Panels0190.accepted Panels0190.integerPanels Panels0190.aligned
    Panels0190.weightRows Panels0190.weights_checked ⟨3, by decide⟩
def b0191 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0191.block Panels0191.accepted Panels0191.integerPanels Panels0191.aligned
    Panels0191.weightRows Panels0191.weights_checked ⟨3, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0184, b0185, b0186, b0187, b0188, b0189, b0190, b0191]
theorem chain_checked : blockChainCheck (3124082007475528121207110426578/10^30) (4011278304969667087671142319973/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=99077775031117906470506046492052264575117056977829284276070145375428029389927414498758797475488916367605915991226367005783522310921289830086272087593010378762299948350322985236405809692911050291721381413530678/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row03
namespace Row04
abbrev ζ : ℚ := 86956521739130434782608695652/10^30
def b0184 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0184.block Panels0184.accepted Panels0184.integerPanels Panels0184.aligned
    Panels0184.weightRows Panels0184.weights_checked ⟨4, by decide⟩
def b0185 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0185.block Panels0185.accepted Panels0185.integerPanels Panels0185.aligned
    Panels0185.weightRows Panels0185.weights_checked ⟨4, by decide⟩
def b0186 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0186.block Panels0186.accepted Panels0186.integerPanels Panels0186.aligned
    Panels0186.weightRows Panels0186.weights_checked ⟨4, by decide⟩
def b0187 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0187.block Panels0187.accepted Panels0187.integerPanels Panels0187.aligned
    Panels0187.weightRows Panels0187.weights_checked ⟨4, by decide⟩
def b0188 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0188.block Panels0188.accepted Panels0188.integerPanels Panels0188.aligned
    Panels0188.weightRows Panels0188.weights_checked ⟨4, by decide⟩
def b0189 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0189.block Panels0189.accepted Panels0189.integerPanels Panels0189.aligned
    Panels0189.weightRows Panels0189.weights_checked ⟨4, by decide⟩
def b0190 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0190.block Panels0190.accepted Panels0190.integerPanels Panels0190.aligned
    Panels0190.weightRows Panels0190.weights_checked ⟨4, by decide⟩
def b0191 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0191.block Panels0191.accepted Panels0191.integerPanels Panels0191.aligned
    Panels0191.weightRows Panels0191.weights_checked ⟨4, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0184, b0185, b0186, b0187, b0188, b0189, b0190, b0191]
theorem chain_checked : blockChainCheck (3124082007475528121207110426578/10^30) (4011278304969667087671142319973/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=103841733240879762070008368195923641066565543229717296374709374661819563690468118860741486947928411648855878147093846343027640010613242075553704631027426055480258204399688415604288641311822587334794851334151478/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row04
namespace Row05
abbrev ζ : ℚ := 64516129032258064516129032258/10^30
def b0184 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0184.block Panels0184.accepted Panels0184.integerPanels Panels0184.aligned
    Panels0184.weightRows Panels0184.weights_checked ⟨5, by decide⟩
def b0185 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0185.block Panels0185.accepted Panels0185.integerPanels Panels0185.aligned
    Panels0185.weightRows Panels0185.weights_checked ⟨5, by decide⟩
def b0186 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0186.block Panels0186.accepted Panels0186.integerPanels Panels0186.aligned
    Panels0186.weightRows Panels0186.weights_checked ⟨5, by decide⟩
def b0187 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0187.block Panels0187.accepted Panels0187.integerPanels Panels0187.aligned
    Panels0187.weightRows Panels0187.weights_checked ⟨5, by decide⟩
def b0188 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0188.block Panels0188.accepted Panels0188.integerPanels Panels0188.aligned
    Panels0188.weightRows Panels0188.weights_checked ⟨5, by decide⟩
def b0189 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0189.block Panels0189.accepted Panels0189.integerPanels Panels0189.aligned
    Panels0189.weightRows Panels0189.weights_checked ⟨5, by decide⟩
def b0190 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0190.block Panels0190.accepted Panels0190.integerPanels Panels0190.aligned
    Panels0190.weightRows Panels0190.weights_checked ⟨5, by decide⟩
def b0191 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0191.block Panels0191.accepted Panels0191.integerPanels Panels0191.aligned
    Panels0191.weightRows Panels0191.weights_checked ⟨5, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0184, b0185, b0186, b0187, b0188, b0189, b0190, b0191]
theorem chain_checked : blockChainCheck (3124082007475528121207110426578/10^30) (4011278304969667087671142319973/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=107440103084272192415939568415931419302213857291814030558450975761950786176443374744760346098743291020603279482241754857873954788710194755541127612430556582590523654098235364815735131286782265689454366056019310/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row05
namespace Row06
abbrev ζ : ℚ := 46511627906976744186046511627/10^30
def b0184 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0184.block Panels0184.accepted Panels0184.integerPanels Panels0184.aligned
    Panels0184.weightRows Panels0184.weights_checked ⟨6, by decide⟩
def b0185 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0185.block Panels0185.accepted Panels0185.integerPanels Panels0185.aligned
    Panels0185.weightRows Panels0185.weights_checked ⟨6, by decide⟩
def b0186 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0186.block Panels0186.accepted Panels0186.integerPanels Panels0186.aligned
    Panels0186.weightRows Panels0186.weights_checked ⟨6, by decide⟩
def b0187 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0187.block Panels0187.accepted Panels0187.integerPanels Panels0187.aligned
    Panels0187.weightRows Panels0187.weights_checked ⟨6, by decide⟩
def b0188 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0188.block Panels0188.accepted Panels0188.integerPanels Panels0188.aligned
    Panels0188.weightRows Panels0188.weights_checked ⟨6, by decide⟩
def b0189 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0189.block Panels0189.accepted Panels0189.integerPanels Panels0189.aligned
    Panels0189.weightRows Panels0189.weights_checked ⟨6, by decide⟩
def b0190 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0190.block Panels0190.accepted Panels0190.integerPanels Panels0190.aligned
    Panels0190.weightRows Panels0190.weights_checked ⟨6, by decide⟩
def b0191 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0191.block Panels0191.accepted Panels0191.integerPanels Panels0191.aligned
    Panels0191.weightRows Panels0191.weights_checked ⟨6, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0184, b0185, b0186, b0187, b0188, b0189, b0190, b0191]
theorem chain_checked : blockChainCheck (3124082007475528121207110426578/10^30) (4011278304969667087671142319973/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=110398977377118199970301780194860891125711801507119013431663584527981509575176665279481818460225344619875817111113801949952494179816648981077860550439637252386289284324240855072312704313080011302941379459560578/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row06
namespace Row07
abbrev ζ : ℚ := 33898305084745762711864406779/10^30
def b0184 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0184.block Panels0184.accepted Panels0184.integerPanels Panels0184.aligned
    Panels0184.weightRows Panels0184.weights_checked ⟨7, by decide⟩
def b0185 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0185.block Panels0185.accepted Panels0185.integerPanels Panels0185.aligned
    Panels0185.weightRows Panels0185.weights_checked ⟨7, by decide⟩
def b0186 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0186.block Panels0186.accepted Panels0186.integerPanels Panels0186.aligned
    Panels0186.weightRows Panels0186.weights_checked ⟨7, by decide⟩
def b0187 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0187.block Panels0187.accepted Panels0187.integerPanels Panels0187.aligned
    Panels0187.weightRows Panels0187.weights_checked ⟨7, by decide⟩
def b0188 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0188.block Panels0188.accepted Panels0188.integerPanels Panels0188.aligned
    Panels0188.weightRows Panels0188.weights_checked ⟨7, by decide⟩
def b0189 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0189.block Panels0189.accepted Panels0189.integerPanels Panels0189.aligned
    Panels0189.weightRows Panels0189.weights_checked ⟨7, by decide⟩
def b0190 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0190.block Panels0190.accepted Panels0190.integerPanels Panels0190.aligned
    Panels0190.weightRows Panels0190.weights_checked ⟨7, by decide⟩
def b0191 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0191.block Panels0191.accepted Panels0191.integerPanels Panels0191.aligned
    Panels0191.weightRows Panels0191.weights_checked ⟨7, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0184, b0185, b0186, b0187, b0188, b0189, b0190, b0191]
theorem chain_checked : blockChainCheck (3124082007475528121207110426578/10^30) (4011278304969667087671142319973/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=112510564483181967681869155390802012926375913788599577261925893214772523887182286299540320215454321975859227927910376731565346463440504639270026858633642511641581786526630472617451402485069536355559777433031362/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row07
namespace Row08
abbrev ζ : ℚ := 25316455696202531645569620253/10^30
def b0184 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0184.block Panels0184.accepted Panels0184.integerPanels Panels0184.aligned
    Panels0184.weightRows Panels0184.weights_checked ⟨8, by decide⟩
def b0185 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0185.block Panels0185.accepted Panels0185.integerPanels Panels0185.aligned
    Panels0185.weightRows Panels0185.weights_checked ⟨8, by decide⟩
def b0186 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0186.block Panels0186.accepted Panels0186.integerPanels Panels0186.aligned
    Panels0186.weightRows Panels0186.weights_checked ⟨8, by decide⟩
def b0187 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0187.block Panels0187.accepted Panels0187.integerPanels Panels0187.aligned
    Panels0187.weightRows Panels0187.weights_checked ⟨8, by decide⟩
def b0188 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0188.block Panels0188.accepted Panels0188.integerPanels Panels0188.aligned
    Panels0188.weightRows Panels0188.weights_checked ⟨8, by decide⟩
def b0189 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0189.block Panels0189.accepted Panels0189.integerPanels Panels0189.aligned
    Panels0189.weightRows Panels0189.weights_checked ⟨8, by decide⟩
def b0190 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0190.block Panels0190.accepted Panels0190.integerPanels Panels0190.aligned
    Panels0190.weightRows Panels0190.weights_checked ⟨8, by decide⟩
def b0191 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0191.block Panels0191.accepted Panels0191.integerPanels Panels0191.aligned
    Panels0191.weightRows Panels0191.weights_checked ⟨8, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0184, b0185, b0186, b0187, b0188, b0189, b0190, b0191]
theorem chain_checked : blockChainCheck (3124082007475528121207110426578/10^30) (4011278304969667087671142319973/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=113965692112658300502825386598938107502500684018158025205993703033755236063262350657429402863866528845937776477296256599168594613332170926757840629934403288898030378466892849913429244494636941517704147662892530/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row08
namespace Row09
abbrev ζ : ℚ := 18691588785046728971962616822/10^30
def b0184 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0184.block Panels0184.accepted Panels0184.integerPanels Panels0184.aligned
    Panels0184.weightRows Panels0184.weights_checked ⟨9, by decide⟩
def b0185 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0185.block Panels0185.accepted Panels0185.integerPanels Panels0185.aligned
    Panels0185.weightRows Panels0185.weights_checked ⟨9, by decide⟩
def b0186 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0186.block Panels0186.accepted Panels0186.integerPanels Panels0186.aligned
    Panels0186.weightRows Panels0186.weights_checked ⟨9, by decide⟩
def b0187 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0187.block Panels0187.accepted Panels0187.integerPanels Panels0187.aligned
    Panels0187.weightRows Panels0187.weights_checked ⟨9, by decide⟩
def b0188 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0188.block Panels0188.accepted Panels0188.integerPanels Panels0188.aligned
    Panels0188.weightRows Panels0188.weights_checked ⟨9, by decide⟩
def b0189 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0189.block Panels0189.accepted Panels0189.integerPanels Panels0189.aligned
    Panels0189.weightRows Panels0189.weights_checked ⟨9, by decide⟩
def b0190 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0190.block Panels0190.accepted Panels0190.integerPanels Panels0190.aligned
    Panels0190.weightRows Panels0190.weights_checked ⟨9, by decide⟩
def b0191 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0191.block Panels0191.accepted Panels0191.integerPanels Panels0191.aligned
    Panels0191.weightRows Panels0191.weights_checked ⟨9, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0184, b0185, b0186, b0187, b0188, b0189, b0190, b0191]
theorem chain_checked : blockChainCheck (3124082007475528121207110426578/10^30) (4011278304969667087671142319973/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=115099299008213737879226918700735778458843572706724780634932913655978874598257046914330433192924328400889274249472308504915379988538282256352445753092865887365220039241945269006171266308984035517403119369568398/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row09
namespace Row10
abbrev ζ : ℚ := 13793103448275862068965517241/10^30
def b0184 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0184.block Panels0184.accepted Panels0184.integerPanels Panels0184.aligned
    Panels0184.weightRows Panels0184.weights_checked ⟨10, by decide⟩
def b0185 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0185.block Panels0185.accepted Panels0185.integerPanels Panels0185.aligned
    Panels0185.weightRows Panels0185.weights_checked ⟨10, by decide⟩
def b0186 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0186.block Panels0186.accepted Panels0186.integerPanels Panels0186.aligned
    Panels0186.weightRows Panels0186.weights_checked ⟨10, by decide⟩
def b0187 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0187.block Panels0187.accepted Panels0187.integerPanels Panels0187.aligned
    Panels0187.weightRows Panels0187.weights_checked ⟨10, by decide⟩
def b0188 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0188.block Panels0188.accepted Panels0188.integerPanels Panels0188.aligned
    Panels0188.weightRows Panels0188.weights_checked ⟨10, by decide⟩
def b0189 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0189.block Panels0189.accepted Panels0189.integerPanels Panels0189.aligned
    Panels0189.weightRows Panels0189.weights_checked ⟨10, by decide⟩
def b0190 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0190.block Panels0190.accepted Panels0190.integerPanels Panels0190.aligned
    Panels0190.weightRows Panels0190.weights_checked ⟨10, by decide⟩
def b0191 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0191.block Panels0191.accepted Panels0191.integerPanels Panels0191.aligned
    Panels0191.weightRows Panels0191.weights_checked ⟨10, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0184, b0185, b0186, b0187, b0188, b0189, b0190, b0191]
theorem chain_checked : blockChainCheck (3124082007475528121207110426578/10^30) (4011278304969667087671142319973/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=115943305769065876252156629849377794665441639294408244860393664255358683661678546459730506290089791815757602123784684911521464206312296116387287756775192950988186639381157273533833406056404533450851272211636226/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row10
namespace Row11
abbrev ζ : ℚ := 10152284263959390862944162436/10^30
def b0184 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0184.block Panels0184.accepted Panels0184.integerPanels Panels0184.aligned
    Panels0184.weightRows Panels0184.weights_checked ⟨11, by decide⟩
def b0185 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0185.block Panels0185.accepted Panels0185.integerPanels Panels0185.aligned
    Panels0185.weightRows Panels0185.weights_checked ⟨11, by decide⟩
def b0186 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0186.block Panels0186.accepted Panels0186.integerPanels Panels0186.aligned
    Panels0186.weightRows Panels0186.weights_checked ⟨11, by decide⟩
def b0187 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0187.block Panels0187.accepted Panels0187.integerPanels Panels0187.aligned
    Panels0187.weightRows Panels0187.weights_checked ⟨11, by decide⟩
def b0188 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0188.block Panels0188.accepted Panels0188.integerPanels Panels0188.aligned
    Panels0188.weightRows Panels0188.weights_checked ⟨11, by decide⟩
def b0189 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0189.block Panels0189.accepted Panels0189.integerPanels Panels0189.aligned
    Panels0189.weightRows Panels0189.weights_checked ⟨11, by decide⟩
def b0190 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0190.block Panels0190.accepted Panels0190.integerPanels Panels0190.aligned
    Panels0190.weightRows Panels0190.weights_checked ⟨11, by decide⟩
def b0191 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0191.block Panels0191.accepted Panels0191.integerPanels Panels0191.aligned
    Panels0191.weightRows Panels0191.weights_checked ⟨11, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0184, b0185, b0186, b0187, b0188, b0189, b0190, b0191]
theorem chain_checked : blockChainCheck (3124082007475528121207110426578/10^30) (4011278304969667087671142319973/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=116573830663406930425232656918445443107441737113123846813212501470565525956736860610636393888057201016430983608134976940345984902922065071825655411651071422556703483005791406276256116783162889129372889701934646/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row11
namespace Row12
abbrev ζ : ℚ := 9950248756218905472636815920/10^30
def b0184 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0184.block Panels0184.accepted Panels0184.integerPanels Panels0184.aligned
    Panels0184.weightRows Panels0184.weights_checked ⟨12, by decide⟩
def b0185 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0185.block Panels0185.accepted Panels0185.integerPanels Panels0185.aligned
    Panels0185.weightRows Panels0185.weights_checked ⟨12, by decide⟩
def b0186 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0186.block Panels0186.accepted Panels0186.integerPanels Panels0186.aligned
    Panels0186.weightRows Panels0186.weights_checked ⟨12, by decide⟩
def b0187 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0187.block Panels0187.accepted Panels0187.integerPanels Panels0187.aligned
    Panels0187.weightRows Panels0187.weights_checked ⟨12, by decide⟩
def b0188 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0188.block Panels0188.accepted Panels0188.integerPanels Panels0188.aligned
    Panels0188.weightRows Panels0188.weights_checked ⟨12, by decide⟩
def b0189 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0189.block Panels0189.accepted Panels0189.integerPanels Panels0189.aligned
    Panels0189.weightRows Panels0189.weights_checked ⟨12, by decide⟩
def b0190 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0190.block Panels0190.accepted Panels0190.integerPanels Panels0190.aligned
    Panels0190.weightRows Panels0190.weights_checked ⟨12, by decide⟩
def b0191 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0191.block Panels0191.accepted Panels0191.integerPanels Panels0191.aligned
    Panels0191.weightRows Panels0191.weights_checked ⟨12, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0184, b0185, b0186, b0187, b0188, b0189, b0190, b0191]
theorem chain_checked : blockChainCheck (3124082007475528121207110426578/10^30) (4011278304969667087671142319973/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=116608900064805726933075179600214099867055926234364650963510049830450920585538722141997971666873702571397845087406245156967781191495784425899775041709591496456241802030998395238011014981150806343925372367188534/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row12
#print axioms Row12.segment
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments023
