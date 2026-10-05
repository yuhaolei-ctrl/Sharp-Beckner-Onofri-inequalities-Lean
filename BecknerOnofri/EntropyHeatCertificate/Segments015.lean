import BecknerOnofri.EntropyHeatCheckedWeights
import BecknerOnofri.EntropyHeatSegments
import BecknerOnofri.EntropyHeatCertificate.Panels0120
import BecknerOnofri.EntropyHeatCertificate.Panels0121
import BecknerOnofri.EntropyHeatCertificate.Panels0122
import BecknerOnofri.EntropyHeatCertificate.Panels0123
import BecknerOnofri.EntropyHeatCertificate.Panels0124
import BecknerOnofri.EntropyHeatCertificate.Panels0125
import BecknerOnofri.EntropyHeatCertificate.Panels0126
import BecknerOnofri.EntropyHeatCertificate.Panels0127
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments015
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace Row00
abbrev ζ : ℚ := 285714285714285714285714285714/10^30
def b0120 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0120.block Panels0120.accepted Panels0120.integerPanels Panels0120.aligned
    Panels0120.weightRows Panels0120.weights_checked ⟨0, by decide⟩
def b0121 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0121.block Panels0121.accepted Panels0121.integerPanels Panels0121.aligned
    Panels0121.weightRows Panels0121.weights_checked ⟨0, by decide⟩
def b0122 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0122.block Panels0122.accepted Panels0122.integerPanels Panels0122.aligned
    Panels0122.weightRows Panels0122.weights_checked ⟨0, by decide⟩
def b0123 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0123.block Panels0123.accepted Panels0123.integerPanels Panels0123.aligned
    Panels0123.weightRows Panels0123.weights_checked ⟨0, by decide⟩
def b0124 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0124.block Panels0124.accepted Panels0124.integerPanels Panels0124.aligned
    Panels0124.weightRows Panels0124.weights_checked ⟨0, by decide⟩
def b0125 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0125.block Panels0125.accepted Panels0125.integerPanels Panels0125.aligned
    Panels0125.weightRows Panels0125.weights_checked ⟨0, by decide⟩
def b0126 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0126.block Panels0126.accepted Panels0126.integerPanels Panels0126.aligned
    Panels0126.weightRows Panels0126.weights_checked ⟨0, by decide⟩
def b0127 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0127.block Panels0127.accepted Panels0127.integerPanels Panels0127.aligned
    Panels0127.weightRows Panels0127.weights_checked ⟨0, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0120, b0121, b0122, b0123, b0124, b0125, b0126, b0127]
theorem chain_checked : blockChainCheck (422901741431716601440210218652/10^30) (543000016158258557301601017683/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=13170199265221510501626612248200782260609588947034723375391856732905563644158407849567948241762123721375839808249918018520886348745096989115974913068469986189413294524298024306910060108896831379939834800813082077/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row00
namespace Row01
abbrev ζ : ℚ := 222222222222222222222222222222/10^30
def b0120 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0120.block Panels0120.accepted Panels0120.integerPanels Panels0120.aligned
    Panels0120.weightRows Panels0120.weights_checked ⟨1, by decide⟩
def b0121 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0121.block Panels0121.accepted Panels0121.integerPanels Panels0121.aligned
    Panels0121.weightRows Panels0121.weights_checked ⟨1, by decide⟩
def b0122 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0122.block Panels0122.accepted Panels0122.integerPanels Panels0122.aligned
    Panels0122.weightRows Panels0122.weights_checked ⟨1, by decide⟩
def b0123 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0123.block Panels0123.accepted Panels0123.integerPanels Panels0123.aligned
    Panels0123.weightRows Panels0123.weights_checked ⟨1, by decide⟩
def b0124 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0124.block Panels0124.accepted Panels0124.integerPanels Panels0124.aligned
    Panels0124.weightRows Panels0124.weights_checked ⟨1, by decide⟩
def b0125 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0125.block Panels0125.accepted Panels0125.integerPanels Panels0125.aligned
    Panels0125.weightRows Panels0125.weights_checked ⟨1, by decide⟩
def b0126 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0126.block Panels0126.accepted Panels0126.integerPanels Panels0126.aligned
    Panels0126.weightRows Panels0126.weights_checked ⟨1, by decide⟩
def b0127 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0127.block Panels0127.accepted Panels0127.integerPanels Panels0127.aligned
    Panels0127.weightRows Panels0127.weights_checked ⟨1, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0120, b0121, b0122, b0123, b0124, b0125, b0126, b0127]
theorem chain_checked : blockChainCheck (422901741431716601440210218652/10^30) (543000016158258557301601017683/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=51651330965948171582499889654523659014090645706071932186763697275048449939254352940836012483559336542072728312579711998311711162246978741050806365862847124822828654394407029888652508638685215839103699651103913493/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row01
namespace Row02
abbrev ζ : ℚ := 153846153846153846153846153846/10^30
def b0120 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0120.block Panels0120.accepted Panels0120.integerPanels Panels0120.aligned
    Panels0120.weightRows Panels0120.weights_checked ⟨2, by decide⟩
def b0121 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0121.block Panels0121.accepted Panels0121.integerPanels Panels0121.aligned
    Panels0121.weightRows Panels0121.weights_checked ⟨2, by decide⟩
def b0122 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0122.block Panels0122.accepted Panels0122.integerPanels Panels0122.aligned
    Panels0122.weightRows Panels0122.weights_checked ⟨2, by decide⟩
def b0123 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0123.block Panels0123.accepted Panels0123.integerPanels Panels0123.aligned
    Panels0123.weightRows Panels0123.weights_checked ⟨2, by decide⟩
def b0124 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0124.block Panels0124.accepted Panels0124.integerPanels Panels0124.aligned
    Panels0124.weightRows Panels0124.weights_checked ⟨2, by decide⟩
def b0125 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0125.block Panels0125.accepted Panels0125.integerPanels Panels0125.aligned
    Panels0125.weightRows Panels0125.weights_checked ⟨2, by decide⟩
def b0126 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0126.block Panels0126.accepted Panels0126.integerPanels Panels0126.aligned
    Panels0126.weightRows Panels0126.weights_checked ⟨2, by decide⟩
def b0127 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0127.block Panels0127.accepted Panels0127.integerPanels Panels0127.aligned
    Panels0127.weightRows Panels0127.weights_checked ⟨2, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0120, b0121, b0122, b0123, b0124, b0125, b0126, b0127]
theorem chain_checked : blockChainCheck (422901741431716601440210218652/10^30) (543000016158258557301601017683/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=165568119618025257559383075776944675823336240071808447379487062719352147295834842163065248458121385602362005275657119758719810409464195343629042547352194868587030671599398830695154856522389807954653630582766746181/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row02
namespace Row03
abbrev ζ : ℚ := 117647058823529411764705882352/10^30
def b0120 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0120.block Panels0120.accepted Panels0120.integerPanels Panels0120.aligned
    Panels0120.weightRows Panels0120.weights_checked ⟨3, by decide⟩
def b0121 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0121.block Panels0121.accepted Panels0121.integerPanels Panels0121.aligned
    Panels0121.weightRows Panels0121.weights_checked ⟨3, by decide⟩
def b0122 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0122.block Panels0122.accepted Panels0122.integerPanels Panels0122.aligned
    Panels0122.weightRows Panels0122.weights_checked ⟨3, by decide⟩
def b0123 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0123.block Panels0123.accepted Panels0123.integerPanels Panels0123.aligned
    Panels0123.weightRows Panels0123.weights_checked ⟨3, by decide⟩
def b0124 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0124.block Panels0124.accepted Panels0124.integerPanels Panels0124.aligned
    Panels0124.weightRows Panels0124.weights_checked ⟨3, by decide⟩
def b0125 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0125.block Panels0125.accepted Panels0125.integerPanels Panels0125.aligned
    Panels0125.weightRows Panels0125.weights_checked ⟨3, by decide⟩
def b0126 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0126.block Panels0126.accepted Panels0126.integerPanels Panels0126.aligned
    Panels0126.weightRows Panels0126.weights_checked ⟨3, by decide⟩
def b0127 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0127.block Panels0127.accepted Panels0127.integerPanels Panels0127.aligned
    Panels0127.weightRows Panels0127.weights_checked ⟨3, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0120, b0121, b0122, b0123, b0124, b0125, b0126, b0127]
theorem chain_checked : blockChainCheck (422901741431716601440210218652/10^30) (543000016158258557301601017683/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=280157872071598121813061547274835306813099770827168248652598412879061269859759142059345675985713731802625164905220142149443932242162527590009127949215767910753514960097989525024541973598489164367001110747568604573/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row03
namespace Row04
abbrev ζ : ℚ := 86956521739130434782608695652/10^30
def b0120 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0120.block Panels0120.accepted Panels0120.integerPanels Panels0120.aligned
    Panels0120.weightRows Panels0120.weights_checked ⟨4, by decide⟩
def b0121 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0121.block Panels0121.accepted Panels0121.integerPanels Panels0121.aligned
    Panels0121.weightRows Panels0121.weights_checked ⟨4, by decide⟩
def b0122 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0122.block Panels0122.accepted Panels0122.integerPanels Panels0122.aligned
    Panels0122.weightRows Panels0122.weights_checked ⟨4, by decide⟩
def b0123 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0123.block Panels0123.accepted Panels0123.integerPanels Panels0123.aligned
    Panels0123.weightRows Panels0123.weights_checked ⟨4, by decide⟩
def b0124 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0124.block Panels0124.accepted Panels0124.integerPanels Panels0124.aligned
    Panels0124.weightRows Panels0124.weights_checked ⟨4, by decide⟩
def b0125 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0125.block Panels0125.accepted Panels0125.integerPanels Panels0125.aligned
    Panels0125.weightRows Panels0125.weights_checked ⟨4, by decide⟩
def b0126 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0126.block Panels0126.accepted Panels0126.integerPanels Panels0126.aligned
    Panels0126.weightRows Panels0126.weights_checked ⟨4, by decide⟩
def b0127 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0127.block Panels0127.accepted Panels0127.integerPanels Panels0127.aligned
    Panels0127.weightRows Panels0127.weights_checked ⟨4, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0120, b0121, b0122, b0123, b0124, b0125, b0126, b0127]
theorem chain_checked : blockChainCheck (422901741431716601440210218652/10^30) (543000016158258557301601017683/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=421161540047896341853578433698315095245799438375024486245472853161424713408392398940038978090601367210306764396670734677800712926545056835554686204788211601332204026988642914888238812393203954147403683310035512373/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row04
namespace Row05
abbrev ζ : ℚ := 64516129032258064516129032258/10^30
def b0120 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0120.block Panels0120.accepted Panels0120.integerPanels Panels0120.aligned
    Panels0120.weightRows Panels0120.weights_checked ⟨5, by decide⟩
def b0121 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0121.block Panels0121.accepted Panels0121.integerPanels Panels0121.aligned
    Panels0121.weightRows Panels0121.weights_checked ⟨5, by decide⟩
def b0122 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0122.block Panels0122.accepted Panels0122.integerPanels Panels0122.aligned
    Panels0122.weightRows Panels0122.weights_checked ⟨5, by decide⟩
def b0123 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0123.block Panels0123.accepted Panels0123.integerPanels Panels0123.aligned
    Panels0123.weightRows Panels0123.weights_checked ⟨5, by decide⟩
def b0124 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0124.block Panels0124.accepted Panels0124.integerPanels Panels0124.aligned
    Panels0124.weightRows Panels0124.weights_checked ⟨5, by decide⟩
def b0125 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0125.block Panels0125.accepted Panels0125.integerPanels Panels0125.aligned
    Panels0125.weightRows Panels0125.weights_checked ⟨5, by decide⟩
def b0126 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0126.block Panels0126.accepted Panels0126.integerPanels Panels0126.aligned
    Panels0126.weightRows Panels0126.weights_checked ⟨5, by decide⟩
def b0127 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0127.block Panels0127.accepted Panels0127.integerPanels Panels0127.aligned
    Panels0127.weightRows Panels0127.weights_checked ⟨5, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0120, b0121, b0122, b0123, b0124, b0125, b0126, b0127]
theorem chain_checked : blockChainCheck (422901741431716601440210218652/10^30) (543000016158258557301601017683/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=556660560505605786670425797880003845661553978525406650212772378479474432880970814888666584739850023790227210603835944596143403745460189848258721866768705117815409412301893632432466539961043918966251528209792971645/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row05
namespace Row06
abbrev ζ : ℚ := 46511627906976744186046511627/10^30
def b0120 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0120.block Panels0120.accepted Panels0120.integerPanels Panels0120.aligned
    Panels0120.weightRows Panels0120.weights_checked ⟨6, by decide⟩
def b0121 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0121.block Panels0121.accepted Panels0121.integerPanels Panels0121.aligned
    Panels0121.weightRows Panels0121.weights_checked ⟨6, by decide⟩
def b0122 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0122.block Panels0122.accepted Panels0122.integerPanels Panels0122.aligned
    Panels0122.weightRows Panels0122.weights_checked ⟨6, by decide⟩
def b0123 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0123.block Panels0123.accepted Panels0123.integerPanels Panels0123.aligned
    Panels0123.weightRows Panels0123.weights_checked ⟨6, by decide⟩
def b0124 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0124.block Panels0124.accepted Panels0124.integerPanels Panels0124.aligned
    Panels0124.weightRows Panels0124.weights_checked ⟨6, by decide⟩
def b0125 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0125.block Panels0125.accepted Panels0125.integerPanels Panels0125.aligned
    Panels0125.weightRows Panels0125.weights_checked ⟨6, by decide⟩
def b0126 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0126.block Panels0126.accepted Panels0126.integerPanels Panels0126.aligned
    Panels0126.weightRows Panels0126.weights_checked ⟨6, by decide⟩
def b0127 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0127.block Panels0127.accepted Panels0127.integerPanels Panels0127.aligned
    Panels0127.weightRows Panels0127.weights_checked ⟨6, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0120, b0121, b0122, b0123, b0124, b0125, b0126, b0127]
theorem chain_checked : blockChainCheck (422901741431716601440210218652/10^30) (543000016158258557301601017683/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=689046687267133166371250729930779042270239228982303243373117865016954363598962129460843087592154028571442571248544286837538808323097784058257580838253337310614227533830785232861786653688180622269013974338477501723/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row06
namespace Row07
abbrev ζ : ℚ := 33898305084745762711864406779/10^30
def b0120 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0120.block Panels0120.accepted Panels0120.integerPanels Panels0120.aligned
    Panels0120.weightRows Panels0120.weights_checked ⟨7, by decide⟩
def b0121 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0121.block Panels0121.accepted Panels0121.integerPanels Panels0121.aligned
    Panels0121.weightRows Panels0121.weights_checked ⟨7, by decide⟩
def b0122 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0122.block Panels0122.accepted Panels0122.integerPanels Panels0122.aligned
    Panels0122.weightRows Panels0122.weights_checked ⟨7, by decide⟩
def b0123 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0123.block Panels0123.accepted Panels0123.integerPanels Panels0123.aligned
    Panels0123.weightRows Panels0123.weights_checked ⟨7, by decide⟩
def b0124 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0124.block Panels0124.accepted Panels0124.integerPanels Panels0124.aligned
    Panels0124.weightRows Panels0124.weights_checked ⟨7, by decide⟩
def b0125 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0125.block Panels0125.accepted Panels0125.integerPanels Panels0125.aligned
    Panels0125.weightRows Panels0125.weights_checked ⟨7, by decide⟩
def b0126 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0126.block Panels0126.accepted Panels0126.integerPanels Panels0126.aligned
    Panels0126.weightRows Panels0126.weights_checked ⟨7, by decide⟩
def b0127 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0127.block Panels0127.accepted Panels0127.integerPanels Panels0127.aligned
    Panels0127.weightRows Panels0127.weights_checked ⟨7, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0120, b0121, b0122, b0123, b0124, b0125, b0126, b0127]
theorem chain_checked : blockChainCheck (422901741431716601440210218652/10^30) (543000016158258557301601017683/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=796050612430656054442830101595090712754778312720032342855649509998651698464675727042102189225637896153082542141075834447705863764967597643216704237542250354140474713866247583223981069878722391050659963827555836667/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row07
namespace Row08
abbrev ζ : ℚ := 25316455696202531645569620253/10^30
def b0120 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0120.block Panels0120.accepted Panels0120.integerPanels Panels0120.aligned
    Panels0120.weightRows Panels0120.weights_checked ⟨8, by decide⟩
def b0121 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0121.block Panels0121.accepted Panels0121.integerPanels Panels0121.aligned
    Panels0121.weightRows Panels0121.weights_checked ⟨8, by decide⟩
def b0122 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0122.block Panels0122.accepted Panels0122.integerPanels Panels0122.aligned
    Panels0122.weightRows Panels0122.weights_checked ⟨8, by decide⟩
def b0123 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0123.block Panels0123.accepted Panels0123.integerPanels Panels0123.aligned
    Panels0123.weightRows Panels0123.weights_checked ⟨8, by decide⟩
def b0124 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0124.block Panels0124.accepted Panels0124.integerPanels Panels0124.aligned
    Panels0124.weightRows Panels0124.weights_checked ⟨8, by decide⟩
def b0125 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0125.block Panels0125.accepted Panels0125.integerPanels Panels0125.aligned
    Panels0125.weightRows Panels0125.weights_checked ⟨8, by decide⟩
def b0126 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0126.block Panels0126.accepted Panels0126.integerPanels Panels0126.aligned
    Panels0126.weightRows Panels0126.weights_checked ⟨8, by decide⟩
def b0127 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0127.block Panels0127.accepted Panels0127.integerPanels Panels0127.aligned
    Panels0127.weightRows Panels0127.weights_checked ⟨8, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0120, b0121, b0122, b0123, b0124, b0125, b0126, b0127]
theorem chain_checked : blockChainCheck (422901741431716601440210218652/10^30) (543000016158258557301601017683/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=876208003971584079687719331783283765787296915526027119075255257987777509714544597514650551288921382123140489301721021510734895750986901828624869557931664501083108588031809739273814296349106115324276067914165186915/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row08
namespace Row09
abbrev ζ : ℚ := 18691588785046728971962616822/10^30
def b0120 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0120.block Panels0120.accepted Panels0120.integerPanels Panels0120.aligned
    Panels0120.weightRows Panels0120.weights_checked ⟨9, by decide⟩
def b0121 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0121.block Panels0121.accepted Panels0121.integerPanels Panels0121.aligned
    Panels0121.weightRows Panels0121.weights_checked ⟨9, by decide⟩
def b0122 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0122.block Panels0122.accepted Panels0122.integerPanels Panels0122.aligned
    Panels0122.weightRows Panels0122.weights_checked ⟨9, by decide⟩
def b0123 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0123.block Panels0123.accepted Panels0123.integerPanels Panels0123.aligned
    Panels0123.weightRows Panels0123.weights_checked ⟨9, by decide⟩
def b0124 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0124.block Panels0124.accepted Panels0124.integerPanels Panels0124.aligned
    Panels0124.weightRows Panels0124.weights_checked ⟨9, by decide⟩
def b0125 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0125.block Panels0125.accepted Panels0125.integerPanels Panels0125.aligned
    Panels0125.weightRows Panels0125.weights_checked ⟨9, by decide⟩
def b0126 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0126.block Panels0126.accepted Panels0126.integerPanels Panels0126.aligned
    Panels0126.weightRows Panels0126.weights_checked ⟨9, by decide⟩
def b0127 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0127.block Panels0127.accepted Panels0127.integerPanels Panels0127.aligned
    Panels0127.weightRows Panels0127.weights_checked ⟨9, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0120, b0121, b0122, b0123, b0124, b0125, b0126, b0127]
theorem chain_checked : blockChainCheck (422901741431716601440210218652/10^30) (543000016158258557301601017683/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=942424108506058554356055242021949453410999737749976248334588373808474962221126510040230093611605792055266112520071084819670154338455079719413179930310528318603043298595082720325288326211757880616054657339443297093/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row09
namespace Row10
abbrev ζ : ℚ := 13793103448275862068965517241/10^30
def b0120 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0120.block Panels0120.accepted Panels0120.integerPanels Panels0120.aligned
    Panels0120.weightRows Panels0120.weights_checked ⟨10, by decide⟩
def b0121 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0121.block Panels0121.accepted Panels0121.integerPanels Panels0121.aligned
    Panels0121.weightRows Panels0121.weights_checked ⟨10, by decide⟩
def b0122 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0122.block Panels0122.accepted Panels0122.integerPanels Panels0122.aligned
    Panels0122.weightRows Panels0122.weights_checked ⟨10, by decide⟩
def b0123 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0123.block Panels0123.accepted Panels0123.integerPanels Panels0123.aligned
    Panels0123.weightRows Panels0123.weights_checked ⟨10, by decide⟩
def b0124 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0124.block Panels0124.accepted Panels0124.integerPanels Panels0124.aligned
    Panels0124.weightRows Panels0124.weights_checked ⟨10, by decide⟩
def b0125 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0125.block Panels0125.accepted Panels0125.integerPanels Panels0125.aligned
    Panels0125.weightRows Panels0125.weights_checked ⟨10, by decide⟩
def b0126 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0126.block Panels0126.accepted Panels0126.integerPanels Panels0126.aligned
    Panels0126.weightRows Panels0126.weights_checked ⟨10, by decide⟩
def b0127 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0127.block Panels0127.accepted Panels0127.integerPanels Panels0127.aligned
    Panels0127.weightRows Panels0127.weights_checked ⟨10, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0120, b0121, b0122, b0123, b0124, b0125, b0126, b0127]
theorem chain_checked : blockChainCheck (422901741431716601440210218652/10^30) (543000016158258557301601017683/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=993926417338977540348111419670070173942011248841707550089442441077297006766359194004985290130921863925558967367063266769554297053791103745318797441294256621718679604885308221953097773374550011099083124047354561051/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row10
namespace Row11
abbrev ζ : ℚ := 10152284263959390862944162436/10^30
def b0120 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0120.block Panels0120.accepted Panels0120.integerPanels Panels0120.aligned
    Panels0120.weightRows Panels0120.weights_checked ⟨11, by decide⟩
def b0121 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0121.block Panels0121.accepted Panels0121.integerPanels Panels0121.aligned
    Panels0121.weightRows Panels0121.weights_checked ⟨11, by decide⟩
def b0122 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0122.block Panels0122.accepted Panels0122.integerPanels Panels0122.aligned
    Panels0122.weightRows Panels0122.weights_checked ⟨11, by decide⟩
def b0123 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0123.block Panels0123.accepted Panels0123.integerPanels Panels0123.aligned
    Panels0123.weightRows Panels0123.weights_checked ⟨11, by decide⟩
def b0124 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0124.block Panels0124.accepted Panels0124.integerPanels Panels0124.aligned
    Panels0124.weightRows Panels0124.weights_checked ⟨11, by decide⟩
def b0125 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0125.block Panels0125.accepted Panels0125.integerPanels Panels0125.aligned
    Panels0125.weightRows Panels0125.weights_checked ⟨11, by decide⟩
def b0126 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0126.block Panels0126.accepted Panels0126.integerPanels Panels0126.aligned
    Panels0126.weightRows Panels0126.weights_checked ⟨11, by decide⟩
def b0127 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0127.block Panels0127.accepted Panels0127.integerPanels Panels0127.aligned
    Panels0127.weightRows Panels0127.weights_checked ⟨11, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0120, b0121, b0122, b0123, b0124, b0125, b0126, b0127]
theorem chain_checked : blockChainCheck (422901741431716601440210218652/10^30) (543000016158258557301601017683/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=1033652958154514022597107580100085331130529354908910606066945834087626552535034816645103970313960819649592656812095255921267419857630440212690151730951848725218148490730929040450341830966175472990706830155061839221/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row11
namespace Row12
abbrev ζ : ℚ := 9950248756218905472636815920/10^30
def b0120 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0120.block Panels0120.accepted Panels0120.integerPanels Panels0120.aligned
    Panels0120.weightRows Panels0120.weights_checked ⟨12, by decide⟩
def b0121 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0121.block Panels0121.accepted Panels0121.integerPanels Panels0121.aligned
    Panels0121.weightRows Panels0121.weights_checked ⟨12, by decide⟩
def b0122 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0122.block Panels0122.accepted Panels0122.integerPanels Panels0122.aligned
    Panels0122.weightRows Panels0122.weights_checked ⟨12, by decide⟩
def b0123 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0123.block Panels0123.accepted Panels0123.integerPanels Panels0123.aligned
    Panels0123.weightRows Panels0123.weights_checked ⟨12, by decide⟩
def b0124 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0124.block Panels0124.accepted Panels0124.integerPanels Panels0124.aligned
    Panels0124.weightRows Panels0124.weights_checked ⟨12, by decide⟩
def b0125 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0125.block Panels0125.accepted Panels0125.integerPanels Panels0125.aligned
    Panels0125.weightRows Panels0125.weights_checked ⟨12, by decide⟩
def b0126 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0126.block Panels0126.accepted Panels0126.integerPanels Panels0126.aligned
    Panels0126.weightRows Panels0126.weights_checked ⟨12, by decide⟩
def b0127 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0127.block Panels0127.accepted Panels0127.integerPanels Panels0127.aligned
    Panels0127.weightRows Panels0127.weights_checked ⟨12, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0120, b0121, b0122, b0123, b0124, b0125, b0126, b0127]
theorem chain_checked : blockChainCheck (422901741431716601440210218652/10^30) (543000016158258557301601017683/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=1035894289368209537017482394465438143188852131405452281590296525765674659273634881609572142632864319315932394305502547751403491740066935687921930894959103967693741925427683945381398347117295560911612522538728120349/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row12
#print axioms Row12.segment
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments015
