import BecknerOnofri.EntropyHeatCheckedWeights
import BecknerOnofri.EntropyHeatSegments
import BecknerOnofri.EntropyHeatCertificate.Panels0232
import BecknerOnofri.EntropyHeatCertificate.Panels0233
import BecknerOnofri.EntropyHeatCertificate.Panels0234
import BecknerOnofri.EntropyHeatCertificate.Panels0235
import BecknerOnofri.EntropyHeatCertificate.Panels0236
import BecknerOnofri.EntropyHeatCertificate.Panels0237
import BecknerOnofri.EntropyHeatCertificate.Panels0238
import BecknerOnofri.EntropyHeatCertificate.Panels0239
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments029
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace Row00
abbrev ζ : ℚ := 285714285714285714285714285714/10^30
def b0232 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0232.block Panels0232.accepted Panels0232.integerPanels Panels0232.aligned
    Panels0232.weightRows Panels0232.weights_checked ⟨0, by decide⟩
def b0233 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0233.block Panels0233.accepted Panels0233.integerPanels Panels0233.aligned
    Panels0233.weightRows Panels0233.weights_checked ⟨0, by decide⟩
def b0234 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0234.block Panels0234.accepted Panels0234.integerPanels Panels0234.aligned
    Panels0234.weightRows Panels0234.weights_checked ⟨0, by decide⟩
def b0235 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0235.block Panels0235.accepted Panels0235.integerPanels Panels0235.aligned
    Panels0235.weightRows Panels0235.weights_checked ⟨0, by decide⟩
def b0236 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0236.block Panels0236.accepted Panels0236.integerPanels Panels0236.aligned
    Panels0236.weightRows Panels0236.weights_checked ⟨0, by decide⟩
def b0237 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0237.block Panels0237.accepted Panels0237.integerPanels Panels0237.aligned
    Panels0237.weightRows Panels0237.weights_checked ⟨0, by decide⟩
def b0238 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0238.block Panels0238.accepted Panels0238.integerPanels Panels0238.aligned
    Panels0238.weightRows Panels0238.weights_checked ⟨0, by decide⟩
def b0239 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0239.block Panels0239.accepted Panels0239.integerPanels Panels0239.aligned
    Panels0239.weightRows Panels0239.weights_checked ⟨0, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0232, b0233, b0234, b0235, b0236, b0237, b0238, b0239]
theorem chain_checked : blockChainCheck (13998601149824155699700021888720/10^30) (17974011232050837835132378248720/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=9280909037939493717733562449165365883043585560405349963538440767876696906342974094924498675512561184423999084378345207913555118095112999389699394510546346632675990114321857325865644734924138396/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row00
namespace Row01
abbrev ζ : ℚ := 222222222222222222222222222222/10^30
def b0232 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0232.block Panels0232.accepted Panels0232.integerPanels Panels0232.aligned
    Panels0232.weightRows Panels0232.weights_checked ⟨1, by decide⟩
def b0233 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0233.block Panels0233.accepted Panels0233.integerPanels Panels0233.aligned
    Panels0233.weightRows Panels0233.weights_checked ⟨1, by decide⟩
def b0234 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0234.block Panels0234.accepted Panels0234.integerPanels Panels0234.aligned
    Panels0234.weightRows Panels0234.weights_checked ⟨1, by decide⟩
def b0235 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0235.block Panels0235.accepted Panels0235.integerPanels Panels0235.aligned
    Panels0235.weightRows Panels0235.weights_checked ⟨1, by decide⟩
def b0236 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0236.block Panels0236.accepted Panels0236.integerPanels Panels0236.aligned
    Panels0236.weightRows Panels0236.weights_checked ⟨1, by decide⟩
def b0237 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0237.block Panels0237.accepted Panels0237.integerPanels Panels0237.aligned
    Panels0237.weightRows Panels0237.weights_checked ⟨1, by decide⟩
def b0238 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0238.block Panels0238.accepted Panels0238.integerPanels Panels0238.aligned
    Panels0238.weightRows Panels0238.weights_checked ⟨1, by decide⟩
def b0239 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0239.block Panels0239.accepted Panels0239.integerPanels Panels0239.aligned
    Panels0239.weightRows Panels0239.weights_checked ⟨1, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0232, b0233, b0234, b0235, b0236, b0237, b0238, b0239]
theorem chain_checked : blockChainCheck (13998601149824155699700021888720/10^30) (17974011232050837835132378248720/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=9493557469090001681371047460416482358698628007233621067100071073491465280384158946325037847484587358623590807369057394512709963368819118357735381842240467717406204645749308732473393090324343804/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row01
namespace Row02
abbrev ζ : ℚ := 153846153846153846153846153846/10^30
def b0232 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0232.block Panels0232.accepted Panels0232.integerPanels Panels0232.aligned
    Panels0232.weightRows Panels0232.weights_checked ⟨2, by decide⟩
def b0233 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0233.block Panels0233.accepted Panels0233.integerPanels Panels0233.aligned
    Panels0233.weightRows Panels0233.weights_checked ⟨2, by decide⟩
def b0234 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0234.block Panels0234.accepted Panels0234.integerPanels Panels0234.aligned
    Panels0234.weightRows Panels0234.weights_checked ⟨2, by decide⟩
def b0235 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0235.block Panels0235.accepted Panels0235.integerPanels Panels0235.aligned
    Panels0235.weightRows Panels0235.weights_checked ⟨2, by decide⟩
def b0236 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0236.block Panels0236.accepted Panels0236.integerPanels Panels0236.aligned
    Panels0236.weightRows Panels0236.weights_checked ⟨2, by decide⟩
def b0237 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0237.block Panels0237.accepted Panels0237.integerPanels Panels0237.aligned
    Panels0237.weightRows Panels0237.weights_checked ⟨2, by decide⟩
def b0238 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0238.block Panels0238.accepted Panels0238.integerPanels Panels0238.aligned
    Panels0238.weightRows Panels0238.weights_checked ⟨2, by decide⟩
def b0239 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0239.block Panels0239.accepted Panels0239.integerPanels Panels0239.aligned
    Panels0239.weightRows Panels0239.weights_checked ⟨2, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0232, b0233, b0234, b0235, b0236, b0237, b0238, b0239]
theorem chain_checked : blockChainCheck (13998601149824155699700021888720/10^30) (17974011232050837835132378248720/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=9726905825649606802968031237614962731857043861972610545764896525053435671781906656974260584223439982196985674443279094007462982023470727544492342051797130780739008271266667618386760257285734588/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row02
namespace Row03
abbrev ζ : ℚ := 117647058823529411764705882352/10^30
def b0232 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0232.block Panels0232.accepted Panels0232.integerPanels Panels0232.aligned
    Panels0232.weightRows Panels0232.weights_checked ⟨3, by decide⟩
def b0233 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0233.block Panels0233.accepted Panels0233.integerPanels Panels0233.aligned
    Panels0233.weightRows Panels0233.weights_checked ⟨3, by decide⟩
def b0234 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0234.block Panels0234.accepted Panels0234.integerPanels Panels0234.aligned
    Panels0234.weightRows Panels0234.weights_checked ⟨3, by decide⟩
def b0235 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0235.block Panels0235.accepted Panels0235.integerPanels Panels0235.aligned
    Panels0235.weightRows Panels0235.weights_checked ⟨3, by decide⟩
def b0236 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0236.block Panels0236.accepted Panels0236.integerPanels Panels0236.aligned
    Panels0236.weightRows Panels0236.weights_checked ⟨3, by decide⟩
def b0237 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0237.block Panels0237.accepted Panels0237.integerPanels Panels0237.aligned
    Panels0237.weightRows Panels0237.weights_checked ⟨3, by decide⟩
def b0238 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0238.block Panels0238.accepted Panels0238.integerPanels Panels0238.aligned
    Panels0238.weightRows Panels0238.weights_checked ⟨3, by decide⟩
def b0239 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0239.block Panels0239.accepted Panels0239.integerPanels Panels0239.aligned
    Panels0239.weightRows Panels0239.weights_checked ⟨3, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0232, b0233, b0234, b0235, b0236, b0237, b0238, b0239]
theorem chain_checked : blockChainCheck (13998601149824155699700021888720/10^30) (17974011232050837835132378248720/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=9852288186218391599474475613001817714631826427458863741858275747130853637163643789454502348050202000329424828117088131653513333156356734624637738439813856285899228383494529350826351111110168444/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row03
namespace Row04
abbrev ζ : ℚ := 86956521739130434782608695652/10^30
def b0232 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0232.block Panels0232.accepted Panels0232.integerPanels Panels0232.aligned
    Panels0232.weightRows Panels0232.weights_checked ⟨4, by decide⟩
def b0233 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0233.block Panels0233.accepted Panels0233.integerPanels Panels0233.aligned
    Panels0233.weightRows Panels0233.weights_checked ⟨4, by decide⟩
def b0234 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0234.block Panels0234.accepted Panels0234.integerPanels Panels0234.aligned
    Panels0234.weightRows Panels0234.weights_checked ⟨4, by decide⟩
def b0235 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0235.block Panels0235.accepted Panels0235.integerPanels Panels0235.aligned
    Panels0235.weightRows Panels0235.weights_checked ⟨4, by decide⟩
def b0236 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0236.block Panels0236.accepted Panels0236.integerPanels Panels0236.aligned
    Panels0236.weightRows Panels0236.weights_checked ⟨4, by decide⟩
def b0237 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0237.block Panels0237.accepted Panels0237.integerPanels Panels0237.aligned
    Panels0237.weightRows Panels0237.weights_checked ⟨4, by decide⟩
def b0238 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0238.block Panels0238.accepted Panels0238.integerPanels Panels0238.aligned
    Panels0238.weightRows Panels0238.weights_checked ⟨4, by decide⟩
def b0239 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0239.block Panels0239.accepted Panels0239.integerPanels Panels0239.aligned
    Panels0239.weightRows Panels0239.weights_checked ⟨4, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0232, b0233, b0234, b0235, b0236, b0237, b0238, b0239]
theorem chain_checked : blockChainCheck (13998601149824155699700021888720/10^30) (17974011232050837835132378248720/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=9959600786963510867838074897169345342218521483160411638864133636334517283644696803550615701940924588828567069529035728254744825302078682691411871603514767358902588838096645727286161671991930844/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row04
namespace Row05
abbrev ζ : ℚ := 64516129032258064516129032258/10^30
def b0232 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0232.block Panels0232.accepted Panels0232.integerPanels Panels0232.aligned
    Panels0232.weightRows Panels0232.weights_checked ⟨5, by decide⟩
def b0233 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0233.block Panels0233.accepted Panels0233.integerPanels Panels0233.aligned
    Panels0233.weightRows Panels0233.weights_checked ⟨5, by decide⟩
def b0234 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0234.block Panels0234.accepted Panels0234.integerPanels Panels0234.aligned
    Panels0234.weightRows Panels0234.weights_checked ⟨5, by decide⟩
def b0235 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0235.block Panels0235.accepted Panels0235.integerPanels Panels0235.aligned
    Panels0235.weightRows Panels0235.weights_checked ⟨5, by decide⟩
def b0236 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0236.block Panels0236.accepted Panels0236.integerPanels Panels0236.aligned
    Panels0236.weightRows Panels0236.weights_checked ⟨5, by decide⟩
def b0237 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0237.block Panels0237.accepted Panels0237.integerPanels Panels0237.aligned
    Panels0237.weightRows Panels0237.weights_checked ⟨5, by decide⟩
def b0238 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0238.block Panels0238.accepted Panels0238.integerPanels Panels0238.aligned
    Panels0238.weightRows Panels0238.weights_checked ⟨5, by decide⟩
def b0239 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0239.block Panels0239.accepted Panels0239.integerPanels Panels0239.aligned
    Panels0239.weightRows Panels0239.weights_checked ⟨5, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0232, b0233, b0234, b0235, b0236, b0237, b0238, b0239]
theorem chain_checked : blockChainCheck (13998601149824155699700021888720/10^30) (17974011232050837835132378248720/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=10038656315847481449420331517585893896321006620830533842210835028606920336696278250956682695894516980341007572563623311702833532477261505431111800289739601444252800737501739874500222586615660060/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row05
namespace Row06
abbrev ζ : ℚ := 46511627906976744186046511627/10^30
def b0232 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0232.block Panels0232.accepted Panels0232.integerPanels Panels0232.aligned
    Panels0232.weightRows Panels0232.weights_checked ⟨6, by decide⟩
def b0233 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0233.block Panels0233.accepted Panels0233.integerPanels Panels0233.aligned
    Panels0233.weightRows Panels0233.weights_checked ⟨6, by decide⟩
def b0234 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0234.block Panels0234.accepted Panels0234.integerPanels Panels0234.aligned
    Panels0234.weightRows Panels0234.weights_checked ⟨6, by decide⟩
def b0235 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0235.block Panels0235.accepted Panels0235.integerPanels Panels0235.aligned
    Panels0235.weightRows Panels0235.weights_checked ⟨6, by decide⟩
def b0236 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0236.block Panels0236.accepted Panels0236.integerPanels Panels0236.aligned
    Panels0236.weightRows Panels0236.weights_checked ⟨6, by decide⟩
def b0237 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0237.block Panels0237.accepted Panels0237.integerPanels Panels0237.aligned
    Panels0237.weightRows Panels0237.weights_checked ⟨6, by decide⟩
def b0238 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0238.block Panels0238.accepted Panels0238.integerPanels Panels0238.aligned
    Panels0238.weightRows Panels0238.weights_checked ⟨6, by decide⟩
def b0239 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0239.block Panels0239.accepted Panels0239.integerPanels Panels0239.aligned
    Panels0239.weightRows Panels0239.weights_checked ⟨6, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0232, b0233, b0234, b0235, b0236, b0237, b0238, b0239]
theorem chain_checked : blockChainCheck (13998601149824155699700021888720/10^30) (17974011232050837835132378248720/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=10102446992816742219673215003628604107047120402399088322513203378521983558664579112122124148221101970151214673108955053589284718006046826021517123374963444769875845263573268707363924466990245644/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row06
namespace Row07
abbrev ζ : ℚ := 33898305084745762711864406779/10^30
def b0232 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0232.block Panels0232.accepted Panels0232.integerPanels Panels0232.aligned
    Panels0232.weightRows Panels0232.weights_checked ⟨7, by decide⟩
def b0233 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0233.block Panels0233.accepted Panels0233.integerPanels Panels0233.aligned
    Panels0233.weightRows Panels0233.weights_checked ⟨7, by decide⟩
def b0234 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0234.block Panels0234.accepted Panels0234.integerPanels Panels0234.aligned
    Panels0234.weightRows Panels0234.weights_checked ⟨7, by decide⟩
def b0235 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0235.block Panels0235.accepted Panels0235.integerPanels Panels0235.aligned
    Panels0235.weightRows Panels0235.weights_checked ⟨7, by decide⟩
def b0236 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0236.block Panels0236.accepted Panels0236.integerPanels Panels0236.aligned
    Panels0236.weightRows Panels0236.weights_checked ⟨7, by decide⟩
def b0237 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0237.block Panels0237.accepted Panels0237.integerPanels Panels0237.aligned
    Panels0237.weightRows Panels0237.weights_checked ⟨7, by decide⟩
def b0238 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0238.block Panels0238.accepted Panels0238.integerPanels Panels0238.aligned
    Panels0238.weightRows Panels0238.weights_checked ⟨7, by decide⟩
def b0239 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0239.block Panels0239.accepted Panels0239.integerPanels Panels0239.aligned
    Panels0239.weightRows Panels0239.weights_checked ⟨7, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0232, b0233, b0234, b0235, b0236, b0237, b0238, b0239]
theorem chain_checked : blockChainCheck (13998601149824155699700021888720/10^30) (17974011232050837835132378248720/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=10147329425303555709536930075619951304031865314589158442774292871136880369553169776166187876223429445787308034452694628002665130395216621039062947991963072719744863251953817734333245700907618316/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row07
namespace Row08
abbrev ζ : ℚ := 25316455696202531645569620253/10^30
def b0232 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0232.block Panels0232.accepted Panels0232.integerPanels Panels0232.aligned
    Panels0232.weightRows Panels0232.weights_checked ⟨8, by decide⟩
def b0233 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0233.block Panels0233.accepted Panels0233.integerPanels Panels0233.aligned
    Panels0233.weightRows Panels0233.weights_checked ⟨8, by decide⟩
def b0234 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0234.block Panels0234.accepted Panels0234.integerPanels Panels0234.aligned
    Panels0234.weightRows Panels0234.weights_checked ⟨8, by decide⟩
def b0235 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0235.block Panels0235.accepted Panels0235.integerPanels Panels0235.aligned
    Panels0235.weightRows Panels0235.weights_checked ⟨8, by decide⟩
def b0236 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0236.block Panels0236.accepted Panels0236.integerPanels Panels0236.aligned
    Panels0236.weightRows Panels0236.weights_checked ⟨8, by decide⟩
def b0237 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0237.block Panels0237.accepted Panels0237.integerPanels Panels0237.aligned
    Panels0237.weightRows Panels0237.weights_checked ⟨8, by decide⟩
def b0238 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0238.block Panels0238.accepted Panels0238.integerPanels Panels0238.aligned
    Panels0238.weightRows Panels0238.weights_checked ⟨8, by decide⟩
def b0239 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0239.block Panels0239.accepted Panels0239.integerPanels Panels0239.aligned
    Panels0239.weightRows Panels0239.weights_checked ⟨8, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0232, b0233, b0234, b0235, b0236, b0237, b0238, b0239]
theorem chain_checked : blockChainCheck (13998601149824155699700021888720/10^30) (17974011232050837835132378248720/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=10177957637480098291695020137983389717418951220317287406503238698697432938690928845350037117067928523600854686043517127886129804452333271269393133308727437588472711376342005038047171271785177820/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row08
namespace Row09
abbrev ζ : ℚ := 18691588785046728971962616822/10^30
def b0232 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0232.block Panels0232.accepted Panels0232.integerPanels Panels0232.aligned
    Panels0232.weightRows Panels0232.weights_checked ⟨9, by decide⟩
def b0233 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0233.block Panels0233.accepted Panels0233.integerPanels Panels0233.aligned
    Panels0233.weightRows Panels0233.weights_checked ⟨9, by decide⟩
def b0234 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0234.block Panels0234.accepted Panels0234.integerPanels Panels0234.aligned
    Panels0234.weightRows Panels0234.weights_checked ⟨9, by decide⟩
def b0235 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0235.block Panels0235.accepted Panels0235.integerPanels Panels0235.aligned
    Panels0235.weightRows Panels0235.weights_checked ⟨9, by decide⟩
def b0236 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0236.block Panels0236.accepted Panels0236.integerPanels Panels0236.aligned
    Panels0236.weightRows Panels0236.weights_checked ⟨9, by decide⟩
def b0237 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0237.block Panels0237.accepted Panels0237.integerPanels Panels0237.aligned
    Panels0237.weightRows Panels0237.weights_checked ⟨9, by decide⟩
def b0238 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0238.block Panels0238.accepted Panels0238.integerPanels Panels0238.aligned
    Panels0238.weightRows Panels0238.weights_checked ⟨9, by decide⟩
def b0239 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0239.block Panels0239.accepted Panels0239.integerPanels Panels0239.aligned
    Panels0239.weightRows Panels0239.weights_checked ⟨9, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0232, b0233, b0234, b0235, b0236, b0237, b0238, b0239]
theorem chain_checked : blockChainCheck (13998601149824155699700021888720/10^30) (17974011232050837835132378248720/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=10201652034929280379336926556645262754312182867335553164496023723875500756521587488256870220010238096400480676447596286436997788502465269094861494112220247305288795392571241318215579160552252604/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row09
namespace Row10
abbrev ζ : ℚ := 13793103448275862068965517241/10^30
def b0232 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0232.block Panels0232.accepted Panels0232.integerPanels Panels0232.aligned
    Panels0232.weightRows Panels0232.weights_checked ⟨10, by decide⟩
def b0233 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0233.block Panels0233.accepted Panels0233.integerPanels Panels0233.aligned
    Panels0233.weightRows Panels0233.weights_checked ⟨10, by decide⟩
def b0234 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0234.block Panels0234.accepted Panels0234.integerPanels Panels0234.aligned
    Panels0234.weightRows Panels0234.weights_checked ⟨10, by decide⟩
def b0235 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0235.block Panels0235.accepted Panels0235.integerPanels Panels0235.aligned
    Panels0235.weightRows Panels0235.weights_checked ⟨10, by decide⟩
def b0236 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0236.block Panels0236.accepted Panels0236.integerPanels Panels0236.aligned
    Panels0236.weightRows Panels0236.weights_checked ⟨10, by decide⟩
def b0237 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0237.block Panels0237.accepted Panels0237.integerPanels Panels0237.aligned
    Panels0237.weightRows Panels0237.weights_checked ⟨10, by decide⟩
def b0238 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0238.block Panels0238.accepted Panels0238.integerPanels Panels0238.aligned
    Panels0238.weightRows Panels0238.weights_checked ⟨10, by decide⟩
def b0239 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0239.block Panels0239.accepted Panels0239.integerPanels Panels0239.aligned
    Panels0239.weightRows Panels0239.weights_checked ⟨10, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0232, b0233, b0234, b0235, b0236, b0237, b0238, b0239]
theorem chain_checked : blockChainCheck (13998601149824155699700021888720/10^30) (17974011232050837835132378248720/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=10219200253266974029922841789490275844177990511423921110399723834544983020144925620666878641605301886633860694653606696012782300524537755861900595369497236613573463390605115267206005606230712348/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row10
namespace Row11
abbrev ζ : ℚ := 10152284263959390862944162436/10^30
def b0232 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0232.block Panels0232.accepted Panels0232.integerPanels Panels0232.aligned
    Panels0232.weightRows Panels0232.weights_checked ⟨11, by decide⟩
def b0233 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0233.block Panels0233.accepted Panels0233.integerPanels Panels0233.aligned
    Panels0233.weightRows Panels0233.weights_checked ⟨11, by decide⟩
def b0234 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0234.block Panels0234.accepted Panels0234.integerPanels Panels0234.aligned
    Panels0234.weightRows Panels0234.weights_checked ⟨11, by decide⟩
def b0235 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0235.block Panels0235.accepted Panels0235.integerPanels Panels0235.aligned
    Panels0235.weightRows Panels0235.weights_checked ⟨11, by decide⟩
def b0236 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0236.block Panels0236.accepted Panels0236.integerPanels Panels0236.aligned
    Panels0236.weightRows Panels0236.weights_checked ⟨11, by decide⟩
def b0237 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0237.block Panels0237.accepted Panels0237.integerPanels Panels0237.aligned
    Panels0237.weightRows Panels0237.weights_checked ⟨11, by decide⟩
def b0238 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0238.block Panels0238.accepted Panels0238.integerPanels Panels0238.aligned
    Panels0238.weightRows Panels0238.weights_checked ⟨11, by decide⟩
def b0239 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0239.block Panels0239.accepted Panels0239.integerPanels Panels0239.aligned
    Panels0239.weightRows Panels0239.weights_checked ⟨11, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0232, b0233, b0234, b0235, b0236, b0237, b0238, b0239]
theorem chain_checked : blockChainCheck (13998601149824155699700021888720/10^30) (17974011232050837835132378248720/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=10232258680841336841068251439524022311839701459957927617210258702582409542316463450401165438112373830056697109420315545613900791208551857163049847712053285098362264940147831788708536208790028508/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row11
namespace Row12
abbrev ζ : ℚ := 9950248756218905472636815920/10^30
def b0232 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0232.block Panels0232.accepted Panels0232.integerPanels Panels0232.aligned
    Panels0232.weightRows Panels0232.weights_checked ⟨12, by decide⟩
def b0233 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0233.block Panels0233.accepted Panels0233.integerPanels Panels0233.aligned
    Panels0233.weightRows Panels0233.weights_checked ⟨12, by decide⟩
def b0234 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0234.block Panels0234.accepted Panels0234.integerPanels Panels0234.aligned
    Panels0234.weightRows Panels0234.weights_checked ⟨12, by decide⟩
def b0235 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0235.block Panels0235.accepted Panels0235.integerPanels Panels0235.aligned
    Panels0235.weightRows Panels0235.weights_checked ⟨12, by decide⟩
def b0236 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0236.block Panels0236.accepted Panels0236.integerPanels Panels0236.aligned
    Panels0236.weightRows Panels0236.weights_checked ⟨12, by decide⟩
def b0237 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0237.block Panels0237.accepted Panels0237.integerPanels Panels0237.aligned
    Panels0237.weightRows Panels0237.weights_checked ⟨12, by decide⟩
def b0238 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0238.block Panels0238.accepted Panels0238.integerPanels Panels0238.aligned
    Panels0238.weightRows Panels0238.weights_checked ⟨12, by decide⟩
def b0239 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0239.block Panels0239.accepted Panels0239.integerPanels Panels0239.aligned
    Panels0239.weightRows Panels0239.weights_checked ⟨12, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0232, b0233, b0234, b0235, b0236, b0237, b0238, b0239]
theorem chain_checked : blockChainCheck (13998601149824155699700021888720/10^30) (17974011232050837835132378248720/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=10232983707003587821316265245673507520181795944550389344930507152310913964381422860506122380330216845324223201386745740946276861048986473750779655683227552046023832908758340485757714206334943612/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row12
#print axioms Row12.segment
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments029
