import BecknerOnofri.EntropyHeatCheckedWeights
import BecknerOnofri.EntropyHeatSegments
import BecknerOnofri.EntropyHeatCertificate.Panels0208
import BecknerOnofri.EntropyHeatCertificate.Panels0209
import BecknerOnofri.EntropyHeatCertificate.Panels0210
import BecknerOnofri.EntropyHeatCertificate.Panels0211
import BecknerOnofri.EntropyHeatCertificate.Panels0212
import BecknerOnofri.EntropyHeatCertificate.Panels0213
import BecknerOnofri.EntropyHeatCertificate.Panels0214
import BecknerOnofri.EntropyHeatCertificate.Panels0215
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments026
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace Row00
abbrev ζ : ℚ := 285714285714285714285714285714/10^30
def b0208 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0208.block Panels0208.accepted Panels0208.integerPanels Panels0208.aligned
    Panels0208.weightRows Panels0208.weights_checked ⟨0, by decide⟩
def b0209 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0209.block Panels0209.accepted Panels0209.integerPanels Panels0209.aligned
    Panels0209.weightRows Panels0209.weights_checked ⟨0, by decide⟩
def b0210 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0210.block Panels0210.accepted Panels0210.integerPanels Panels0210.aligned
    Panels0210.weightRows Panels0210.weights_checked ⟨0, by decide⟩
def b0211 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0211.block Panels0211.accepted Panels0211.integerPanels Panels0211.aligned
    Panels0211.weightRows Panels0211.weights_checked ⟨0, by decide⟩
def b0212 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0212.block Panels0212.accepted Panels0212.integerPanels Panels0212.aligned
    Panels0212.weightRows Panels0212.weights_checked ⟨0, by decide⟩
def b0213 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0213.block Panels0213.accepted Panels0213.integerPanels Panels0213.aligned
    Panels0213.weightRows Panels0213.weights_checked ⟨0, by decide⟩
def b0214 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0214.block Panels0214.accepted Panels0214.integerPanels Panels0214.aligned
    Panels0214.weightRows Panels0214.weights_checked ⟨0, by decide⟩
def b0215 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0215.block Panels0215.accepted Panels0215.integerPanels Panels0215.aligned
    Panels0215.weightRows Panels0215.weights_checked ⟨0, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0208, b0209, b0210, b0211, b0212, b0213, b0214, b0215]
theorem chain_checked : blockChainCheck (6613076287325882991783239235141/10^30) (8491098945861286002391423129665/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=1498621999257601562707847701313401878389359959622130737801455260633719928724455825782518375724064183128285135767679899676741250734200129478466990153164380376050899398546112124787793767931285536156707490536/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row00
namespace Row01
abbrev ζ : ℚ := 222222222222222222222222222222/10^30
def b0208 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0208.block Panels0208.accepted Panels0208.integerPanels Panels0208.aligned
    Panels0208.weightRows Panels0208.weights_checked ⟨1, by decide⟩
def b0209 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0209.block Panels0209.accepted Panels0209.integerPanels Panels0209.aligned
    Panels0209.weightRows Panels0209.weights_checked ⟨1, by decide⟩
def b0210 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0210.block Panels0210.accepted Panels0210.integerPanels Panels0210.aligned
    Panels0210.weightRows Panels0210.weights_checked ⟨1, by decide⟩
def b0211 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0211.block Panels0211.accepted Panels0211.integerPanels Panels0211.aligned
    Panels0211.weightRows Panels0211.weights_checked ⟨1, by decide⟩
def b0212 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0212.block Panels0212.accepted Panels0212.integerPanels Panels0212.aligned
    Panels0212.weightRows Panels0212.weights_checked ⟨1, by decide⟩
def b0213 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0213.block Panels0213.accepted Panels0213.integerPanels Panels0213.aligned
    Panels0213.weightRows Panels0213.weights_checked ⟨1, by decide⟩
def b0214 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0214.block Panels0214.accepted Panels0214.integerPanels Panels0214.aligned
    Panels0214.weightRows Panels0214.weights_checked ⟨1, by decide⟩
def b0215 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0215.block Panels0215.accepted Panels0215.integerPanels Panels0215.aligned
    Panels0215.weightRows Panels0215.weights_checked ⟨1, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0208, b0209, b0210, b0211, b0212, b0213, b0214, b0215]
theorem chain_checked : blockChainCheck (6613076287325882991783239235141/10^30) (8491098945861286002391423129665/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=1571931303469130465417808378981972076307557411017811012373852719185133349795709197243436031218807399194312159479699115854202956307847945788912749310877411730244588872997465383198562630450618683739751170184/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row01
namespace Row02
abbrev ζ : ℚ := 153846153846153846153846153846/10^30
def b0208 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0208.block Panels0208.accepted Panels0208.integerPanels Panels0208.aligned
    Panels0208.weightRows Panels0208.weights_checked ⟨2, by decide⟩
def b0209 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0209.block Panels0209.accepted Panels0209.integerPanels Panels0209.aligned
    Panels0209.weightRows Panels0209.weights_checked ⟨2, by decide⟩
def b0210 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0210.block Panels0210.accepted Panels0210.integerPanels Panels0210.aligned
    Panels0210.weightRows Panels0210.weights_checked ⟨2, by decide⟩
def b0211 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0211.block Panels0211.accepted Panels0211.integerPanels Panels0211.aligned
    Panels0211.weightRows Panels0211.weights_checked ⟨2, by decide⟩
def b0212 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0212.block Panels0212.accepted Panels0212.integerPanels Panels0212.aligned
    Panels0212.weightRows Panels0212.weights_checked ⟨2, by decide⟩
def b0213 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0213.block Panels0213.accepted Panels0213.integerPanels Panels0213.aligned
    Panels0213.weightRows Panels0213.weights_checked ⟨2, by decide⟩
def b0214 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0214.block Panels0214.accepted Panels0214.integerPanels Panels0214.aligned
    Panels0214.weightRows Panels0214.weights_checked ⟨2, by decide⟩
def b0215 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0215.block Panels0215.accepted Panels0215.integerPanels Panels0215.aligned
    Panels0215.weightRows Panels0215.weights_checked ⟨2, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0208, b0209, b0210, b0211, b0212, b0213, b0214, b0215]
theorem chain_checked : blockChainCheck (6613076287325882991783239235141/10^30) (8491098945861286002391423129665/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=1654065059587709817916776203446273880728510732467346719526434412617993347774512990734938363818490893200380101901662808543834354689990088337423529267180971279308467994222843403941985634243513381400223903048/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row02
namespace Row03
abbrev ζ : ℚ := 117647058823529411764705882352/10^30
def b0208 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0208.block Panels0208.accepted Panels0208.integerPanels Panels0208.aligned
    Panels0208.weightRows Panels0208.weights_checked ⟨3, by decide⟩
def b0209 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0209.block Panels0209.accepted Panels0209.integerPanels Panels0209.aligned
    Panels0209.weightRows Panels0209.weights_checked ⟨3, by decide⟩
def b0210 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0210.block Panels0210.accepted Panels0210.integerPanels Panels0210.aligned
    Panels0210.weightRows Panels0210.weights_checked ⟨3, by decide⟩
def b0211 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0211.block Panels0211.accepted Panels0211.integerPanels Panels0211.aligned
    Panels0211.weightRows Panels0211.weights_checked ⟨3, by decide⟩
def b0212 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0212.block Panels0212.accepted Panels0212.integerPanels Panels0212.aligned
    Panels0212.weightRows Panels0212.weights_checked ⟨3, by decide⟩
def b0213 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0213.block Panels0213.accepted Panels0213.integerPanels Panels0213.aligned
    Panels0213.weightRows Panels0213.weights_checked ⟨3, by decide⟩
def b0214 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0214.block Panels0214.accepted Panels0214.integerPanels Panels0214.aligned
    Panels0214.weightRows Panels0214.weights_checked ⟨3, by decide⟩
def b0215 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0215.block Panels0215.accepted Panels0215.integerPanels Panels0215.aligned
    Panels0215.weightRows Panels0215.weights_checked ⟨3, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0208, b0209, b0210, b0211, b0212, b0213, b0214, b0215]
theorem chain_checked : blockChainCheck (6613076287325882991783239235141/10^30) (8491098945861286002391423129665/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=1698918950193359025475284754036392534428340150438530158247359282730909304450772601688343452918645543110815100646463007615549448289394682574410428584221041020762213412259819103236249222531409262626429923224/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row03
namespace Row04
abbrev ζ : ℚ := 86956521739130434782608695652/10^30
def b0208 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0208.block Panels0208.accepted Panels0208.integerPanels Panels0208.aligned
    Panels0208.weightRows Panels0208.weights_checked ⟨4, by decide⟩
def b0209 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0209.block Panels0209.accepted Panels0209.integerPanels Panels0209.aligned
    Panels0209.weightRows Panels0209.weights_checked ⟨4, by decide⟩
def b0210 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0210.block Panels0210.accepted Panels0210.integerPanels Panels0210.aligned
    Panels0210.weightRows Panels0210.weights_checked ⟨4, by decide⟩
def b0211 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0211.block Panels0211.accepted Panels0211.integerPanels Panels0211.aligned
    Panels0211.weightRows Panels0211.weights_checked ⟨4, by decide⟩
def b0212 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0212.block Panels0212.accepted Panels0212.integerPanels Panels0212.aligned
    Panels0212.weightRows Panels0212.weights_checked ⟨4, by decide⟩
def b0213 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0213.block Panels0213.accepted Panels0213.integerPanels Panels0213.aligned
    Panels0213.weightRows Panels0213.weights_checked ⟨4, by decide⟩
def b0214 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0214.block Panels0214.accepted Panels0214.integerPanels Panels0214.aligned
    Panels0214.weightRows Panels0214.weights_checked ⟨4, by decide⟩
def b0215 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0215.block Panels0215.accepted Panels0215.integerPanels Panels0215.aligned
    Panels0215.weightRows Panels0215.weights_checked ⟨4, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0208, b0209, b0210, b0211, b0212, b0213, b0214, b0215]
theorem chain_checked : blockChainCheck (6613076287325882991783239235141/10^30) (8491098945861286002391423129665/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=1737705974707089025228421599792956594329375512029042589768048556830514436360531034414934157864183685763826965173683917963419780183063108885827323792951033457374296188274787136997405691633513457671529029624/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row04
namespace Row05
abbrev ζ : ℚ := 64516129032258064516129032258/10^30
def b0208 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0208.block Panels0208.accepted Panels0208.integerPanels Panels0208.aligned
    Panels0208.weightRows Panels0208.weights_checked ⟨5, by decide⟩
def b0209 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0209.block Panels0209.accepted Panels0209.integerPanels Panels0209.aligned
    Panels0209.weightRows Panels0209.weights_checked ⟨5, by decide⟩
def b0210 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0210.block Panels0210.accepted Panels0210.integerPanels Panels0210.aligned
    Panels0210.weightRows Panels0210.weights_checked ⟨5, by decide⟩
def b0211 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0211.block Panels0211.accepted Panels0211.integerPanels Panels0211.aligned
    Panels0211.weightRows Panels0211.weights_checked ⟨5, by decide⟩
def b0212 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0212.block Panels0212.accepted Panels0212.integerPanels Panels0212.aligned
    Panels0212.weightRows Panels0212.weights_checked ⟨5, by decide⟩
def b0213 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0213.block Panels0213.accepted Panels0213.integerPanels Panels0213.aligned
    Panels0213.weightRows Panels0213.weights_checked ⟨5, by decide⟩
def b0214 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0214.block Panels0214.accepted Panels0214.integerPanels Panels0214.aligned
    Panels0214.weightRows Panels0214.weights_checked ⟨5, by decide⟩
def b0215 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0215.block Panels0215.accepted Panels0215.integerPanels Panels0215.aligned
    Panels0215.weightRows Panels0215.weights_checked ⟨5, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0208, b0209, b0210, b0211, b0212, b0213, b0214, b0215]
theorem chain_checked : blockChainCheck (6613076287325882991783239235141/10^30) (8491098945861286002391423129665/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=1766512882406556519765344842603693642508567646492339561027220053000018215169586266948697924492078214240485202384167600200226121925703921234143163345507232932159084346722448074085650499408746258028368665960/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row05
namespace Row06
abbrev ζ : ℚ := 46511627906976744186046511627/10^30
def b0208 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0208.block Panels0208.accepted Panels0208.integerPanels Panels0208.aligned
    Panels0208.weightRows Panels0208.weights_checked ⟨6, by decide⟩
def b0209 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0209.block Panels0209.accepted Panels0209.integerPanels Panels0209.aligned
    Panels0209.weightRows Panels0209.weights_checked ⟨6, by decide⟩
def b0210 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0210.block Panels0210.accepted Panels0210.integerPanels Panels0210.aligned
    Panels0210.weightRows Panels0210.weights_checked ⟨6, by decide⟩
def b0211 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0211.block Panels0211.accepted Panels0211.integerPanels Panels0211.aligned
    Panels0211.weightRows Panels0211.weights_checked ⟨6, by decide⟩
def b0212 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0212.block Panels0212.accepted Panels0212.integerPanels Panels0212.aligned
    Panels0212.weightRows Panels0212.weights_checked ⟨6, by decide⟩
def b0213 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0213.block Panels0213.accepted Panels0213.integerPanels Panels0213.aligned
    Panels0213.weightRows Panels0213.weights_checked ⟨6, by decide⟩
def b0214 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0214.block Panels0214.accepted Panels0214.integerPanels Panels0214.aligned
    Panels0214.weightRows Panels0214.weights_checked ⟨6, by decide⟩
def b0215 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0215.block Panels0215.accepted Panels0215.integerPanels Panels0215.aligned
    Panels0215.weightRows Panels0215.weights_checked ⟨6, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0208, b0209, b0210, b0211, b0212, b0213, b0214, b0215]
theorem chain_checked : blockChainCheck (6613076287325882991783239235141/10^30) (8491098945861286002391423129665/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=1789900971312127531553218576653530306997067164422774211367854446305450794558323973205810451095894813047674925775546623283060591194560441777701496314237849445669121497716053639409789863961207558476724432424/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row06
namespace Row07
abbrev ζ : ℚ := 33898305084745762711864406779/10^30
def b0208 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0208.block Panels0208.accepted Panels0208.integerPanels Panels0208.aligned
    Panels0208.weightRows Panels0208.weights_checked ⟨7, by decide⟩
def b0209 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0209.block Panels0209.accepted Panels0209.integerPanels Panels0209.aligned
    Panels0209.weightRows Panels0209.weights_checked ⟨7, by decide⟩
def b0210 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0210.block Panels0210.accepted Panels0210.integerPanels Panels0210.aligned
    Panels0210.weightRows Panels0210.weights_checked ⟨7, by decide⟩
def b0211 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0211.block Panels0211.accepted Panels0211.integerPanels Panels0211.aligned
    Panels0211.weightRows Panels0211.weights_checked ⟨7, by decide⟩
def b0212 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0212.block Panels0212.accepted Panels0212.integerPanels Panels0212.aligned
    Panels0212.weightRows Panels0212.weights_checked ⟨7, by decide⟩
def b0213 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0213.block Panels0213.accepted Panels0213.integerPanels Panels0213.aligned
    Panels0213.weightRows Panels0213.weights_checked ⟨7, by decide⟩
def b0214 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0214.block Panels0214.accepted Panels0214.integerPanels Panels0214.aligned
    Panels0214.weightRows Panels0214.weights_checked ⟨7, by decide⟩
def b0215 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0215.block Panels0215.accepted Panels0215.integerPanels Panels0215.aligned
    Panels0215.weightRows Panels0215.weights_checked ⟨7, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0208, b0209, b0210, b0211, b0212, b0213, b0214, b0215]
theorem chain_checked : blockChainCheck (6613076287325882991783239235141/10^30) (8491098945861286002391423129665/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=1806433135297073816258052427601009866814420865265093278601980071083200667753447932945450202466283220729318158213092044229304035026684948304446183921009449344984899620072768672013645133572645258550105937256/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row07
namespace Row08
abbrev ζ : ℚ := 25316455696202531645569620253/10^30
def b0208 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0208.block Panels0208.accepted Panels0208.integerPanels Panels0208.aligned
    Panels0208.weightRows Panels0208.weights_checked ⟨8, by decide⟩
def b0209 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0209.block Panels0209.accepted Panels0209.integerPanels Panels0209.aligned
    Panels0209.weightRows Panels0209.weights_checked ⟨8, by decide⟩
def b0210 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0210.block Panels0210.accepted Panels0210.integerPanels Panels0210.aligned
    Panels0210.weightRows Panels0210.weights_checked ⟨8, by decide⟩
def b0211 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0211.block Panels0211.accepted Panels0211.integerPanels Panels0211.aligned
    Panels0211.weightRows Panels0211.weights_checked ⟨8, by decide⟩
def b0212 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0212.block Panels0212.accepted Panels0212.integerPanels Panels0212.aligned
    Panels0212.weightRows Panels0212.weights_checked ⟨8, by decide⟩
def b0213 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0213.block Panels0213.accepted Panels0213.integerPanels Panels0213.aligned
    Panels0213.weightRows Panels0213.weights_checked ⟨8, by decide⟩
def b0214 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0214.block Panels0214.accepted Panels0214.integerPanels Panels0214.aligned
    Panels0214.weightRows Panels0214.weights_checked ⟨8, by decide⟩
def b0215 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0215.block Panels0215.accepted Panels0215.integerPanels Panels0215.aligned
    Panels0215.weightRows Panels0215.weights_checked ⟨8, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0208, b0209, b0210, b0211, b0212, b0213, b0214, b0215]
theorem chain_checked : blockChainCheck (6613076287325882991783239235141/10^30) (8491098945861286002391423129665/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=1817751055224666086296512132465945114591591921732833747938282887893289053148771911406912314802432534150381994303239393053103501000484596747975552973574371262075573877255517612260827863744704632348419503520/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row08
namespace Row09
abbrev ζ : ℚ := 18691588785046728971962616822/10^30
def b0208 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0208.block Panels0208.accepted Panels0208.integerPanels Panels0208.aligned
    Panels0208.weightRows Panels0208.weights_checked ⟨9, by decide⟩
def b0209 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0209.block Panels0209.accepted Panels0209.integerPanels Panels0209.aligned
    Panels0209.weightRows Panels0209.weights_checked ⟨9, by decide⟩
def b0210 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0210.block Panels0210.accepted Panels0210.integerPanels Panels0210.aligned
    Panels0210.weightRows Panels0210.weights_checked ⟨9, by decide⟩
def b0211 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0211.block Panels0211.accepted Panels0211.integerPanels Panels0211.aligned
    Panels0211.weightRows Panels0211.weights_checked ⟨9, by decide⟩
def b0212 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0212.block Panels0212.accepted Panels0212.integerPanels Panels0212.aligned
    Panels0212.weightRows Panels0212.weights_checked ⟨9, by decide⟩
def b0213 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0213.block Panels0213.accepted Panels0213.integerPanels Panels0213.aligned
    Panels0213.weightRows Panels0213.weights_checked ⟨9, by decide⟩
def b0214 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0214.block Panels0214.accepted Panels0214.integerPanels Panels0214.aligned
    Panels0214.weightRows Panels0214.weights_checked ⟨9, by decide⟩
def b0215 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0215.block Panels0215.accepted Panels0215.integerPanels Panels0215.aligned
    Panels0215.weightRows Panels0215.weights_checked ⟨9, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0208, b0209, b0210, b0211, b0212, b0213, b0214, b0215]
theorem chain_checked : blockChainCheck (6613076287325882991783239235141/10^30) (8491098945861286002391423129665/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=1826526866136547848405638650226621247994313864158954708573126769073119819190902710075839469219017494215472671514840919361205613730363462746345437043068189014475089730187880019815021257900721034865675206984/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row09
namespace Row10
abbrev ζ : ℚ := 13793103448275862068965517241/10^30
def b0208 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0208.block Panels0208.accepted Panels0208.integerPanels Panels0208.aligned
    Panels0208.weightRows Panels0208.weights_checked ⟨10, by decide⟩
def b0209 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0209.block Panels0209.accepted Panels0209.integerPanels Panels0209.aligned
    Panels0209.weightRows Panels0209.weights_checked ⟨10, by decide⟩
def b0210 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0210.block Panels0210.accepted Panels0210.integerPanels Panels0210.aligned
    Panels0210.weightRows Panels0210.weights_checked ⟨10, by decide⟩
def b0211 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0211.block Panels0211.accepted Panels0211.integerPanels Panels0211.aligned
    Panels0211.weightRows Panels0211.weights_checked ⟨10, by decide⟩
def b0212 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0212.block Panels0212.accepted Panels0212.integerPanels Panels0212.aligned
    Panels0212.weightRows Panels0212.weights_checked ⟨10, by decide⟩
def b0213 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0213.block Panels0213.accepted Panels0213.integerPanels Panels0213.aligned
    Panels0213.weightRows Panels0213.weights_checked ⟨10, by decide⟩
def b0214 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0214.block Panels0214.accepted Panels0214.integerPanels Panels0214.aligned
    Panels0214.weightRows Panels0214.weights_checked ⟨10, by decide⟩
def b0215 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0215.block Panels0215.accepted Panels0215.integerPanels Panels0215.aligned
    Panels0215.weightRows Panels0215.weights_checked ⟨10, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0208, b0209, b0210, b0211, b0212, b0213, b0214, b0215]
theorem chain_checked : blockChainCheck (6613076287325882991783239235141/10^30) (8491098945861286002391423129665/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=1833037582290757608350824449198894001198158992378089460282489776172210351629348032681344855203513933872529454387917151430449432148237002905033117002185144694993547659149389103223172102502196455658981290608/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row10
namespace Row11
abbrev ζ : ℚ := 10152284263959390862944162436/10^30
def b0208 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0208.block Panels0208.accepted Panels0208.integerPanels Panels0208.aligned
    Panels0208.weightRows Panels0208.weights_checked ⟨11, by decide⟩
def b0209 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0209.block Panels0209.accepted Panels0209.integerPanels Panels0209.aligned
    Panels0209.weightRows Panels0209.weights_checked ⟨11, by decide⟩
def b0210 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0210.block Panels0210.accepted Panels0210.integerPanels Panels0210.aligned
    Panels0210.weightRows Panels0210.weights_checked ⟨11, by decide⟩
def b0211 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0211.block Panels0211.accepted Panels0211.integerPanels Panels0211.aligned
    Panels0211.weightRows Panels0211.weights_checked ⟨11, by decide⟩
def b0212 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0212.block Panels0212.accepted Panels0212.integerPanels Panels0212.aligned
    Panels0212.weightRows Panels0212.weights_checked ⟨11, by decide⟩
def b0213 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0213.block Panels0213.accepted Panels0213.integerPanels Panels0213.aligned
    Panels0213.weightRows Panels0213.weights_checked ⟨11, by decide⟩
def b0214 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0214.block Panels0214.accepted Panels0214.integerPanels Panels0214.aligned
    Panels0214.weightRows Panels0214.weights_checked ⟨11, by decide⟩
def b0215 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0215.block Panels0215.accepted Panels0215.integerPanels Panels0215.aligned
    Panels0215.weightRows Panels0215.weights_checked ⟨11, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0208, b0209, b0210, b0211, b0212, b0213, b0214, b0215]
theorem chain_checked : blockChainCheck (6613076287325882991783239235141/10^30) (8491098945861286002391423129665/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=1837888734311049265663476826112040317983646563355718300722344651697227899080379979517261362912640534821432321251558916616238293121820615282994732189059165149157175321666023243560099081006560290372686840568/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row11
namespace Row12
abbrev ζ : ℚ := 9950248756218905472636815920/10^30
def b0208 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0208.block Panels0208.accepted Panels0208.integerPanels Panels0208.aligned
    Panels0208.weightRows Panels0208.weights_checked ⟨12, by decide⟩
def b0209 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0209.block Panels0209.accepted Panels0209.integerPanels Panels0209.aligned
    Panels0209.weightRows Panels0209.weights_checked ⟨12, by decide⟩
def b0210 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0210.block Panels0210.accepted Panels0210.integerPanels Panels0210.aligned
    Panels0210.weightRows Panels0210.weights_checked ⟨12, by decide⟩
def b0211 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0211.block Panels0211.accepted Panels0211.integerPanels Panels0211.aligned
    Panels0211.weightRows Panels0211.weights_checked ⟨12, by decide⟩
def b0212 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0212.block Panels0212.accepted Panels0212.integerPanels Panels0212.aligned
    Panels0212.weightRows Panels0212.weights_checked ⟨12, by decide⟩
def b0213 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0213.block Panels0213.accepted Panels0213.integerPanels Panels0213.aligned
    Panels0213.weightRows Panels0213.weights_checked ⟨12, by decide⟩
def b0214 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0214.block Panels0214.accepted Panels0214.integerPanels Panels0214.aligned
    Panels0214.weightRows Panels0214.weights_checked ⟨12, by decide⟩
def b0215 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0215.block Panels0215.accepted Panels0215.integerPanels Panels0215.aligned
    Panels0215.weightRows Panels0215.weights_checked ⟨12, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0208, b0209, b0210, b0211, b0212, b0213, b0214, b0215]
theorem chain_checked : blockChainCheck (6613076287325882991783239235141/10^30) (8491098945861286002391423129665/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=1838158234275758173489687326364424871005393917173485739900121735973252143093781346865675106856539898792720554717622647849602935711189149548581934735105809885660863493515434263970361710855360362715282484632/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row12
#print axioms Row12.segment
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments026
