import BecknerOnofri.EntropyHeatCheckedWeights
import BecknerOnofri.EntropyHeatSegments
import BecknerOnofri.EntropyHeatCertificate.Panels0144
import BecknerOnofri.EntropyHeatCertificate.Panels0145
import BecknerOnofri.EntropyHeatCertificate.Panels0146
import BecknerOnofri.EntropyHeatCertificate.Panels0147
import BecknerOnofri.EntropyHeatCertificate.Panels0148
import BecknerOnofri.EntropyHeatCertificate.Panels0149
import BecknerOnofri.EntropyHeatCertificate.Panels0150
import BecknerOnofri.EntropyHeatCertificate.Panels0151
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments018
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace Row00
abbrev ζ : ℚ := 285714285714285714285714285714/10^30
def b0144 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0144.block Panels0144.accepted Panels0144.integerPanels Panels0144.aligned
    Panels0144.weightRows Panels0144.weights_checked ⟨0, by decide⟩
def b0145 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0145.block Panels0145.accepted Panels0145.integerPanels Panels0145.aligned
    Panels0145.weightRows Panels0145.weights_checked ⟨0, by decide⟩
def b0146 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0146.block Panels0146.accepted Panels0146.integerPanels Panels0146.aligned
    Panels0146.weightRows Panels0146.weights_checked ⟨0, by decide⟩
def b0147 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0147.block Panels0147.accepted Panels0147.integerPanels Panels0147.aligned
    Panels0147.weightRows Panels0147.weights_checked ⟨0, by decide⟩
def b0148 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0148.block Panels0148.accepted Panels0148.integerPanels Panels0148.aligned
    Panels0148.weightRows Panels0148.weights_checked ⟨0, by decide⟩
def b0149 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0149.block Panels0149.accepted Panels0149.integerPanels Panels0149.aligned
    Panels0149.weightRows Panels0149.weights_checked ⟨0, by decide⟩
def b0150 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0150.block Panels0150.accepted Panels0150.integerPanels Panels0150.aligned
    Panels0150.weightRows Panels0150.weights_checked ⟨0, by decide⟩
def b0151 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0151.block Panels0151.accepted Panels0151.integerPanels Panels0151.aligned
    Panels0151.weightRows Panels0151.weights_checked ⟨0, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0144, b0145, b0146, b0147, b0148, b0149, b0150, b0151]
theorem chain_checked : blockChainCheck (895201045119432327478050281094/10^30) (1149425822459585220641394231371/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=58018287653695963833468768951355853846457157042378606631925758119098273279088802963311404602489641045332709104398416657153776899704141523848610639220775388885156597781152419317835272582029245744765433496954675356/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row00
namespace Row01
abbrev ζ : ℚ := 222222222222222222222222222222/10^30
def b0144 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0144.block Panels0144.accepted Panels0144.integerPanels Panels0144.aligned
    Panels0144.weightRows Panels0144.weights_checked ⟨1, by decide⟩
def b0145 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0145.block Panels0145.accepted Panels0145.integerPanels Panels0145.aligned
    Panels0145.weightRows Panels0145.weights_checked ⟨1, by decide⟩
def b0146 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0146.block Panels0146.accepted Panels0146.integerPanels Panels0146.aligned
    Panels0146.weightRows Panels0146.weights_checked ⟨1, by decide⟩
def b0147 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0147.block Panels0147.accepted Panels0147.integerPanels Panels0147.aligned
    Panels0147.weightRows Panels0147.weights_checked ⟨1, by decide⟩
def b0148 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0148.block Panels0148.accepted Panels0148.integerPanels Panels0148.aligned
    Panels0148.weightRows Panels0148.weights_checked ⟨1, by decide⟩
def b0149 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0149.block Panels0149.accepted Panels0149.integerPanels Panels0149.aligned
    Panels0149.weightRows Panels0149.weights_checked ⟨1, by decide⟩
def b0150 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0150.block Panels0150.accepted Panels0150.integerPanels Panels0150.aligned
    Panels0150.weightRows Panels0150.weights_checked ⟨1, by decide⟩
def b0151 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0151.block Panels0151.accepted Panels0151.integerPanels Panels0151.aligned
    Panels0151.weightRows Panels0151.weights_checked ⟨1, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0144, b0145, b0146, b0147, b0148, b0149, b0150, b0151]
theorem chain_checked : blockChainCheck (895201045119432327478050281094/10^30) (1149425822459585220641394231371/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=88698811369022760450680453971597068323975770026731336601899791330361313606300174474997792797593760939428904302792831322439000255227472580855531603659913462095439659721063635309097017265555461464771451702719117164/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row01
namespace Row02
abbrev ζ : ℚ := 153846153846153846153846153846/10^30
def b0144 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0144.block Panels0144.accepted Panels0144.integerPanels Panels0144.aligned
    Panels0144.weightRows Panels0144.weights_checked ⟨2, by decide⟩
def b0145 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0145.block Panels0145.accepted Panels0145.integerPanels Panels0145.aligned
    Panels0145.weightRows Panels0145.weights_checked ⟨2, by decide⟩
def b0146 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0146.block Panels0146.accepted Panels0146.integerPanels Panels0146.aligned
    Panels0146.weightRows Panels0146.weights_checked ⟨2, by decide⟩
def b0147 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0147.block Panels0147.accepted Panels0147.integerPanels Panels0147.aligned
    Panels0147.weightRows Panels0147.weights_checked ⟨2, by decide⟩
def b0148 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0148.block Panels0148.accepted Panels0148.integerPanels Panels0148.aligned
    Panels0148.weightRows Panels0148.weights_checked ⟨2, by decide⟩
def b0149 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0149.block Panels0149.accepted Panels0149.integerPanels Panels0149.aligned
    Panels0149.weightRows Panels0149.weights_checked ⟨2, by decide⟩
def b0150 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0150.block Panels0150.accepted Panels0150.integerPanels Panels0150.aligned
    Panels0150.weightRows Panels0150.weights_checked ⟨2, by decide⟩
def b0151 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0151.block Panels0151.accepted Panels0151.integerPanels Panels0151.aligned
    Panels0151.weightRows Panels0151.weights_checked ⟨2, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0144, b0145, b0146, b0147, b0148, b0149, b0150, b0151]
theorem chain_checked : blockChainCheck (895201045119432327478050281094/10^30) (1149425822459585220641394231371/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=135164803463812155934724928204310588866321310044072459752766210366525888204906433329914160693358697272850160069383280725817072056879805514667925212872424847281534264641533391405387474149137494382770524068227871948/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row02
namespace Row03
abbrev ζ : ℚ := 117647058823529411764705882352/10^30
def b0144 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0144.block Panels0144.accepted Panels0144.integerPanels Panels0144.aligned
    Panels0144.weightRows Panels0144.weights_checked ⟨3, by decide⟩
def b0145 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0145.block Panels0145.accepted Panels0145.integerPanels Panels0145.aligned
    Panels0145.weightRows Panels0145.weights_checked ⟨3, by decide⟩
def b0146 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0146.block Panels0146.accepted Panels0146.integerPanels Panels0146.aligned
    Panels0146.weightRows Panels0146.weights_checked ⟨3, by decide⟩
def b0147 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0147.block Panels0147.accepted Panels0147.integerPanels Panels0147.aligned
    Panels0147.weightRows Panels0147.weights_checked ⟨3, by decide⟩
def b0148 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0148.block Panels0148.accepted Panels0148.integerPanels Panels0148.aligned
    Panels0148.weightRows Panels0148.weights_checked ⟨3, by decide⟩
def b0149 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0149.block Panels0149.accepted Panels0149.integerPanels Panels0149.aligned
    Panels0149.weightRows Panels0149.weights_checked ⟨3, by decide⟩
def b0150 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0150.block Panels0150.accepted Panels0150.integerPanels Panels0150.aligned
    Panels0150.weightRows Panels0150.weights_checked ⟨3, by decide⟩
def b0151 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0151.block Panels0151.accepted Panels0151.integerPanels Panels0151.aligned
    Panels0151.weightRows Panels0151.weights_checked ⟨3, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0144, b0145, b0146, b0147, b0148, b0149, b0150, b0151]
theorem chain_checked : blockChainCheck (895201045119432327478050281094/10^30) (1149425822459585220641394231371/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=166716112725362832588523523411162935543435561848607908547698817489389322156688353093731079225516971798426454028232103953276572959449839082794200853606786843329965781654625698396706598675926098653177305104878758004/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row03
namespace Row04
abbrev ζ : ℚ := 86956521739130434782608695652/10^30
def b0144 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0144.block Panels0144.accepted Panels0144.integerPanels Panels0144.aligned
    Panels0144.weightRows Panels0144.weights_checked ⟨4, by decide⟩
def b0145 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0145.block Panels0145.accepted Panels0145.integerPanels Panels0145.aligned
    Panels0145.weightRows Panels0145.weights_checked ⟨4, by decide⟩
def b0146 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0146.block Panels0146.accepted Panels0146.integerPanels Panels0146.aligned
    Panels0146.weightRows Panels0146.weights_checked ⟨4, by decide⟩
def b0147 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0147.block Panels0147.accepted Panels0147.integerPanels Panels0147.aligned
    Panels0147.weightRows Panels0147.weights_checked ⟨4, by decide⟩
def b0148 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0148.block Panels0148.accepted Panels0148.integerPanels Panels0148.aligned
    Panels0148.weightRows Panels0148.weights_checked ⟨4, by decide⟩
def b0149 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0149.block Panels0149.accepted Panels0149.integerPanels Panels0149.aligned
    Panels0149.weightRows Panels0149.weights_checked ⟨4, by decide⟩
def b0150 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0150.block Panels0150.accepted Panels0150.integerPanels Panels0150.aligned
    Panels0150.weightRows Panels0150.weights_checked ⟨4, by decide⟩
def b0151 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0151.block Panels0151.accepted Panels0151.integerPanels Panels0151.aligned
    Panels0151.weightRows Panels0151.weights_checked ⟨4, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0144, b0145, b0146, b0147, b0148, b0149, b0150, b0151]
theorem chain_checked : blockChainCheck (895201045119432327478050281094/10^30) (1149425822459585220641394231371/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=197884334001367695806528912797778426985152121405939546561612169055904298844682721618603525749399272733073681891310509857510328111130107237655576359773659541991931510394730491138329439028458451182375227306816842404/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row04
namespace Row05
abbrev ζ : ℚ := 64516129032258064516129032258/10^30
def b0144 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0144.block Panels0144.accepted Panels0144.integerPanels Panels0144.aligned
    Panels0144.weightRows Panels0144.weights_checked ⟨5, by decide⟩
def b0145 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0145.block Panels0145.accepted Panels0145.integerPanels Panels0145.aligned
    Panels0145.weightRows Panels0145.weights_checked ⟨5, by decide⟩
def b0146 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0146.block Panels0146.accepted Panels0146.integerPanels Panels0146.aligned
    Panels0146.weightRows Panels0146.weights_checked ⟨5, by decide⟩
def b0147 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0147.block Panels0147.accepted Panels0147.integerPanels Panels0147.aligned
    Panels0147.weightRows Panels0147.weights_checked ⟨5, by decide⟩
def b0148 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0148.block Panels0148.accepted Panels0148.integerPanels Panels0148.aligned
    Panels0148.weightRows Panels0148.weights_checked ⟨5, by decide⟩
def b0149 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0149.block Panels0149.accepted Panels0149.integerPanels Panels0149.aligned
    Panels0149.weightRows Panels0149.weights_checked ⟨5, by decide⟩
def b0150 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0150.block Panels0150.accepted Panels0150.integerPanels Panels0150.aligned
    Panels0150.weightRows Panels0150.weights_checked ⟨5, by decide⟩
def b0151 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0151.block Panels0151.accepted Panels0151.integerPanels Panels0151.aligned
    Panels0151.weightRows Panels0151.weights_checked ⟨5, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0144, b0145, b0146, b0147, b0148, b0149, b0150, b0151]
theorem chain_checked : blockChainCheck (895201045119432327478050281094/10^30) (1149425822459585220641394231371/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=223512552519476157769452813986018365763401302893084577553200205707601797621224398223233638853382438943737208756826890646091354492173049320154919011223002235800186934320837062370176736656213629035122824791568720860/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row05
namespace Row06
abbrev ζ : ℚ := 46511627906976744186046511627/10^30
def b0144 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0144.block Panels0144.accepted Panels0144.integerPanels Panels0144.aligned
    Panels0144.weightRows Panels0144.weights_checked ⟨6, by decide⟩
def b0145 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0145.block Panels0145.accepted Panels0145.integerPanels Panels0145.aligned
    Panels0145.weightRows Panels0145.weights_checked ⟨6, by decide⟩
def b0146 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0146.block Panels0146.accepted Panels0146.integerPanels Panels0146.aligned
    Panels0146.weightRows Panels0146.weights_checked ⟨6, by decide⟩
def b0147 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0147.block Panels0147.accepted Panels0147.integerPanels Panels0147.aligned
    Panels0147.weightRows Panels0147.weights_checked ⟨6, by decide⟩
def b0148 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0148.block Panels0148.accepted Panels0148.integerPanels Panels0148.aligned
    Panels0148.weightRows Panels0148.weights_checked ⟨6, by decide⟩
def b0149 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0149.block Panels0149.accepted Panels0149.integerPanels Panels0149.aligned
    Panels0149.weightRows Panels0149.weights_checked ⟨6, by decide⟩
def b0150 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0150.block Panels0150.accepted Panels0150.integerPanels Panels0150.aligned
    Panels0150.weightRows Panels0150.weights_checked ⟨6, by decide⟩
def b0151 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0151.block Panels0151.accepted Panels0151.integerPanels Panels0151.aligned
    Panels0151.weightRows Panels0151.weights_checked ⟨6, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0144, b0145, b0146, b0147, b0148, b0149, b0150, b0151]
theorem chain_checked : blockChainCheck (895201045119432327478050281094/10^30) (1149425822459585220641394231371/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=245949161853734617461736154103567462802337451141720938233502141921313565881557122695857017692678447237463949773273743936480938502590238233707099515455875226546541287221712848884286580009228469792095236771821801204/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row06
namespace Row07
abbrev ζ : ℚ := 33898305084745762711864406779/10^30
def b0144 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0144.block Panels0144.accepted Panels0144.integerPanels Panels0144.aligned
    Panels0144.weightRows Panels0144.weights_checked ⟨7, by decide⟩
def b0145 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0145.block Panels0145.accepted Panels0145.integerPanels Panels0145.aligned
    Panels0145.weightRows Panels0145.weights_checked ⟨7, by decide⟩
def b0146 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0146.block Panels0146.accepted Panels0146.integerPanels Panels0146.aligned
    Panels0146.weightRows Panels0146.weights_checked ⟨7, by decide⟩
def b0147 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0147.block Panels0147.accepted Panels0147.integerPanels Panels0147.aligned
    Panels0147.weightRows Panels0147.weights_checked ⟨7, by decide⟩
def b0148 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0148.block Panels0148.accepted Panels0148.integerPanels Panels0148.aligned
    Panels0148.weightRows Panels0148.weights_checked ⟨7, by decide⟩
def b0149 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0149.block Panels0149.accepted Panels0149.integerPanels Panels0149.aligned
    Panels0149.weightRows Panels0149.weights_checked ⟨7, by decide⟩
def b0150 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0150.block Panels0150.accepted Panels0150.integerPanels Panels0150.aligned
    Panels0150.weightRows Panels0150.weights_checked ⟨7, by decide⟩
def b0151 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0151.block Panels0151.accepted Panels0151.integerPanels Panels0151.aligned
    Panels0151.weightRows Panels0151.weights_checked ⟨7, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0144, b0145, b0146, b0147, b0148, b0149, b0150, b0151]
theorem chain_checked : blockChainCheck (895201045119432327478050281094/10^30) (1149425822459585220641394231371/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=262719857217284379152846522125936756528374457603733235874296578953576623349405948175880076524494381615664355208888996355024954378157247000569538814472615132262744931639042709396539844807394224519503756306642599476/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row07
namespace Row08
abbrev ζ : ℚ := 25316455696202531645569620253/10^30
def b0144 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0144.block Panels0144.accepted Panels0144.integerPanels Panels0144.aligned
    Panels0144.weightRows Panels0144.weights_checked ⟨8, by decide⟩
def b0145 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0145.block Panels0145.accepted Panels0145.integerPanels Panels0145.aligned
    Panels0145.weightRows Panels0145.weights_checked ⟨8, by decide⟩
def b0146 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0146.block Panels0146.accepted Panels0146.integerPanels Panels0146.aligned
    Panels0146.weightRows Panels0146.weights_checked ⟨8, by decide⟩
def b0147 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0147.block Panels0147.accepted Panels0147.integerPanels Panels0147.aligned
    Panels0147.weightRows Panels0147.weights_checked ⟨8, by decide⟩
def b0148 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0148.block Panels0148.accepted Panels0148.integerPanels Panels0148.aligned
    Panels0148.weightRows Panels0148.weights_checked ⟨8, by decide⟩
def b0149 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0149.block Panels0149.accepted Panels0149.integerPanels Panels0149.aligned
    Panels0149.weightRows Panels0149.weights_checked ⟨8, by decide⟩
def b0150 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0150.block Panels0150.accepted Panels0150.integerPanels Panels0150.aligned
    Panels0150.weightRows Panels0150.weights_checked ⟨8, by decide⟩
def b0151 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0151.block Panels0151.accepted Panels0151.integerPanels Panels0151.aligned
    Panels0151.weightRows Panels0151.weights_checked ⟨8, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0144, b0145, b0146, b0147, b0148, b0149, b0150, b0151]
theorem chain_checked : blockChainCheck (895201045119432327478050281094/10^30) (1149425822459585220641394231371/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=274646934298600215920454206449726778894357100867242136730958250719291635085438804623296211703705969418385663834009466764134765156321802220454416728116789031059531970777192606394558238022747488467226310875591449020/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row08
namespace Row09
abbrev ζ : ℚ := 18691588785046728971962616822/10^30
def b0144 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0144.block Panels0144.accepted Panels0144.integerPanels Panels0144.aligned
    Panels0144.weightRows Panels0144.weights_checked ⟨9, by decide⟩
def b0145 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0145.block Panels0145.accepted Panels0145.integerPanels Panels0145.aligned
    Panels0145.weightRows Panels0145.weights_checked ⟨9, by decide⟩
def b0146 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0146.block Panels0146.accepted Panels0146.integerPanels Panels0146.aligned
    Panels0146.weightRows Panels0146.weights_checked ⟨9, by decide⟩
def b0147 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0147.block Panels0147.accepted Panels0147.integerPanels Panels0147.aligned
    Panels0147.weightRows Panels0147.weights_checked ⟨9, by decide⟩
def b0148 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0148.block Panels0148.accepted Panels0148.integerPanels Panels0148.aligned
    Panels0148.weightRows Panels0148.weights_checked ⟨9, by decide⟩
def b0149 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0149.block Panels0149.accepted Panels0149.integerPanels Panels0149.aligned
    Panels0149.weightRows Panels0149.weights_checked ⟨9, by decide⟩
def b0150 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0150.block Panels0150.accepted Panels0150.integerPanels Panels0150.aligned
    Panels0150.weightRows Panels0150.weights_checked ⟨9, by decide⟩
def b0151 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0151.block Panels0151.accepted Panels0151.integerPanels Panels0151.aligned
    Panels0151.weightRows Panels0151.weights_checked ⟨9, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0144, b0145, b0146, b0147, b0148, b0149, b0150, b0151]
theorem chain_checked : blockChainCheck (895201045119432327478050281094/10^30) (1149425822459585220641394231371/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=284148775689070932905027602417147736606291233082562724329476935941583397574649517142328773817463183118153711615565000511971630118113366790294847527659823470972880773918492583937285812624530472869853850255686069964/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row09
namespace Row10
abbrev ζ : ℚ := 13793103448275862068965517241/10^30
def b0144 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0144.block Panels0144.accepted Panels0144.integerPanels Panels0144.aligned
    Panels0144.weightRows Panels0144.weights_checked ⟨10, by decide⟩
def b0145 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0145.block Panels0145.accepted Panels0145.integerPanels Panels0145.aligned
    Panels0145.weightRows Panels0145.weights_checked ⟨10, by decide⟩
def b0146 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0146.block Panels0146.accepted Panels0146.integerPanels Panels0146.aligned
    Panels0146.weightRows Panels0146.weights_checked ⟨10, by decide⟩
def b0147 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0147.block Panels0147.accepted Panels0147.integerPanels Panels0147.aligned
    Panels0147.weightRows Panels0147.weights_checked ⟨10, by decide⟩
def b0148 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0148.block Panels0148.accepted Panels0148.integerPanels Panels0148.aligned
    Panels0148.weightRows Panels0148.weights_checked ⟨10, by decide⟩
def b0149 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0149.block Panels0149.accepted Panels0149.integerPanels Panels0149.aligned
    Panels0149.weightRows Panels0149.weights_checked ⟨10, by decide⟩
def b0150 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0150.block Panels0150.accepted Panels0150.integerPanels Panels0150.aligned
    Panels0150.weightRows Panels0150.weights_checked ⟨10, by decide⟩
def b0151 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0151.block Panels0151.accepted Panels0151.integerPanels Panels0151.aligned
    Panels0151.weightRows Panels0151.weights_checked ⟨10, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0144, b0145, b0146, b0147, b0148, b0149, b0150, b0151]
theorem chain_checked : blockChainCheck (895201045119432327478050281094/10^30) (1149425822459585220641394231371/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=291343057607085704723770759100301434423465090233201176901799863093911506165301156043935449803767448587647500774440082835651620268402136562260584439897179660468203508918945361130122183714269581975226711811087738508/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row10
namespace Row11
abbrev ζ : ℚ := 10152284263959390862944162436/10^30
def b0144 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0144.block Panels0144.accepted Panels0144.integerPanels Panels0144.aligned
    Panels0144.weightRows Panels0144.weights_checked ⟨11, by decide⟩
def b0145 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0145.block Panels0145.accepted Panels0145.integerPanels Panels0145.aligned
    Panels0145.weightRows Panels0145.weights_checked ⟨11, by decide⟩
def b0146 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0146.block Panels0146.accepted Panels0146.integerPanels Panels0146.aligned
    Panels0146.weightRows Panels0146.weights_checked ⟨11, by decide⟩
def b0147 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0147.block Panels0147.accepted Panels0147.integerPanels Panels0147.aligned
    Panels0147.weightRows Panels0147.weights_checked ⟨11, by decide⟩
def b0148 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0148.block Panels0148.accepted Panels0148.integerPanels Panels0148.aligned
    Panels0148.weightRows Panels0148.weights_checked ⟨11, by decide⟩
def b0149 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0149.block Panels0149.accepted Panels0149.integerPanels Panels0149.aligned
    Panels0149.weightRows Panels0149.weights_checked ⟨11, by decide⟩
def b0150 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0150.block Panels0150.accepted Panels0150.integerPanels Panels0150.aligned
    Panels0150.weightRows Panels0150.weights_checked ⟨11, by decide⟩
def b0151 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0151.block Panels0151.accepted Panels0151.integerPanels Panels0151.aligned
    Panels0151.weightRows Panels0151.weights_checked ⟨11, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0144, b0145, b0146, b0147, b0148, b0149, b0150, b0151]
theorem chain_checked : blockChainCheck (895201045119432327478050281094/10^30) (1149425822459585220641394231371/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=296784526692472107200154724322785205362046621149145986082755223050220157743215035216750454322191996238500284541836922618232499227421331088924794457278543051332653608150082423707046688007734335511671447551803154468/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row11
namespace Row12
abbrev ζ : ℚ := 9950248756218905472636815920/10^30
def b0144 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0144.block Panels0144.accepted Panels0144.integerPanels Panels0144.aligned
    Panels0144.weightRows Panels0144.weights_checked ⟨12, by decide⟩
def b0145 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0145.block Panels0145.accepted Panels0145.integerPanels Panels0145.aligned
    Panels0145.weightRows Panels0145.weights_checked ⟨12, by decide⟩
def b0146 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0146.block Panels0146.accepted Panels0146.integerPanels Panels0146.aligned
    Panels0146.weightRows Panels0146.weights_checked ⟨12, by decide⟩
def b0147 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0147.block Panels0147.accepted Panels0147.integerPanels Panels0147.aligned
    Panels0147.weightRows Panels0147.weights_checked ⟨12, by decide⟩
def b0148 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0148.block Panels0148.accepted Panels0148.integerPanels Panels0148.aligned
    Panels0148.weightRows Panels0148.weights_checked ⟨12, by decide⟩
def b0149 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0149.block Panels0149.accepted Panels0149.integerPanels Panels0149.aligned
    Panels0149.weightRows Panels0149.weights_checked ⟨12, by decide⟩
def b0150 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0150.block Panels0150.accepted Panels0150.integerPanels Panels0150.aligned
    Panels0150.weightRows Panels0150.weights_checked ⟨12, by decide⟩
def b0151 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0151.block Panels0151.accepted Panels0151.integerPanels Panels0151.aligned
    Panels0151.weightRows Panels0151.weights_checked ⟨12, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0144, b0145, b0146, b0147, b0148, b0149, b0150, b0151]
theorem chain_checked : blockChainCheck (895201045119432327478050281094/10^30) (1149425822459585220641394231371/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=297088859319060297663689301048017625526564001254801977281796783192583674670103273648585384524778757756945056994608805564986166736146682184402489622184366686411543616344982060486807910687693406336711925500275023732/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row12
#print axioms Row12.segment
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments018
