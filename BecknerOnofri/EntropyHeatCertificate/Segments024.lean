import BecknerOnofri.EntropyHeatCheckedWeights
import BecknerOnofri.EntropyHeatSegments
import BecknerOnofri.EntropyHeatCertificate.Panels0192
import BecknerOnofri.EntropyHeatCertificate.Panels0193
import BecknerOnofri.EntropyHeatCertificate.Panels0194
import BecknerOnofri.EntropyHeatCertificate.Panels0195
import BecknerOnofri.EntropyHeatCertificate.Panels0196
import BecknerOnofri.EntropyHeatCertificate.Panels0197
import BecknerOnofri.EntropyHeatCertificate.Panels0198
import BecknerOnofri.EntropyHeatCertificate.Panels0199
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments024
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace Row00
abbrev ζ : ℚ := 285714285714285714285714285714/10^30
def b0192 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0192.block Panels0192.accepted Panels0192.integerPanels Panels0192.aligned
    Panels0192.weightRows Panels0192.weights_checked ⟨0, by decide⟩
def b0193 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0193.block Panels0193.accepted Panels0193.integerPanels Panels0193.aligned
    Panels0193.weightRows Panels0193.weights_checked ⟨0, by decide⟩
def b0194 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0194.block Panels0194.accepted Panels0194.integerPanels Panels0194.aligned
    Panels0194.weightRows Panels0194.weights_checked ⟨0, by decide⟩
def b0195 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0195.block Panels0195.accepted Panels0195.integerPanels Panels0195.aligned
    Panels0195.weightRows Panels0195.weights_checked ⟨0, by decide⟩
def b0196 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0196.block Panels0196.accepted Panels0196.integerPanels Panels0196.aligned
    Panels0196.weightRows Panels0196.weights_checked ⟨0, by decide⟩
def b0197 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0197.block Panels0197.accepted Panels0197.integerPanels Panels0197.aligned
    Panels0197.weightRows Panels0197.weights_checked ⟨0, by decide⟩
def b0198 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0198.block Panels0198.accepted Panels0198.integerPanels Panels0198.aligned
    Panels0198.weightRows Panels0198.weights_checked ⟨0, by decide⟩
def b0199 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0199.block Panels0199.accepted Panels0199.integerPanels Panels0199.aligned
    Panels0199.weightRows Panels0199.weights_checked ⟨0, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0192, b0193, b0194, b0195, b0196, b0197, b0198, b0199]
theorem chain_checked : blockChainCheck (4011278304969667087671142319973/10^30) (5150426141637181757933211818553/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=5240850418868393764091536916700754316539523825044545106864976803174808449033199853532177501192840388781589303543526800051779858633075130680179653402762564426094239818564388122483279401054730989403587993537830/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row00
namespace Row01
abbrev ζ : ℚ := 222222222222222222222222222222/10^30
def b0192 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0192.block Panels0192.accepted Panels0192.integerPanels Panels0192.aligned
    Panels0192.weightRows Panels0192.weights_checked ⟨1, by decide⟩
def b0193 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0193.block Panels0193.accepted Panels0193.integerPanels Panels0193.aligned
    Panels0193.weightRows Panels0193.weights_checked ⟨1, by decide⟩
def b0194 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0194.block Panels0194.accepted Panels0194.integerPanels Panels0194.aligned
    Panels0194.weightRows Panels0194.weights_checked ⟨1, by decide⟩
def b0195 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0195.block Panels0195.accepted Panels0195.integerPanels Panels0195.aligned
    Panels0195.weightRows Panels0195.weights_checked ⟨1, by decide⟩
def b0196 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0196.block Panels0196.accepted Panels0196.integerPanels Panels0196.aligned
    Panels0196.weightRows Panels0196.weights_checked ⟨1, by decide⟩
def b0197 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0197.block Panels0197.accepted Panels0197.integerPanels Panels0197.aligned
    Panels0197.weightRows Panels0197.weights_checked ⟨1, by decide⟩
def b0198 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0198.block Panels0198.accepted Panels0198.integerPanels Panels0198.aligned
    Panels0198.weightRows Panels0198.weights_checked ⟨1, by decide⟩
def b0199 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0199.block Panels0199.accepted Panels0199.integerPanels Panels0199.aligned
    Panels0199.weightRows Panels0199.weights_checked ⟨1, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0192, b0193, b0194, b0195, b0196, b0197, b0198, b0199]
theorem chain_checked : blockChainCheck (4011278304969667087671142319973/10^30) (5150426141637181757933211818553/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=5670057546381496942202994437802005730630273745878232050954409928556487223001902537384398287013210040608030521528827085805769335769432873133123455600369195352214025066686364865056217201897973602026699653057990/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row01
namespace Row02
abbrev ζ : ℚ := 153846153846153846153846153846/10^30
def b0192 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0192.block Panels0192.accepted Panels0192.integerPanels Panels0192.aligned
    Panels0192.weightRows Panels0192.weights_checked ⟨2, by decide⟩
def b0193 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0193.block Panels0193.accepted Panels0193.integerPanels Panels0193.aligned
    Panels0193.weightRows Panels0193.weights_checked ⟨2, by decide⟩
def b0194 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0194.block Panels0194.accepted Panels0194.integerPanels Panels0194.aligned
    Panels0194.weightRows Panels0194.weights_checked ⟨2, by decide⟩
def b0195 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0195.block Panels0195.accepted Panels0195.integerPanels Panels0195.aligned
    Panels0195.weightRows Panels0195.weights_checked ⟨2, by decide⟩
def b0196 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0196.block Panels0196.accepted Panels0196.integerPanels Panels0196.aligned
    Panels0196.weightRows Panels0196.weights_checked ⟨2, by decide⟩
def b0197 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0197.block Panels0197.accepted Panels0197.integerPanels Panels0197.aligned
    Panels0197.weightRows Panels0197.weights_checked ⟨2, by decide⟩
def b0198 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0198.block Panels0198.accepted Panels0198.integerPanels Panels0198.aligned
    Panels0198.weightRows Panels0198.weights_checked ⟨2, by decide⟩
def b0199 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0199.block Panels0199.accepted Panels0199.integerPanels Panels0199.aligned
    Panels0199.weightRows Panels0199.weights_checked ⟨2, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0192, b0193, b0194, b0195, b0196, b0197, b0198, b0199]
theorem chain_checked : blockChainCheck (4011278304969667087671142319973/10^30) (5150426141637181757933211818553/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=6163376465201512114824607191399755987349604610351830968390759197949087190153066422950109321123742546596002675918286375330121816630023833794110085189153019858521349899029265003903594068076728246897397937401030/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row02
namespace Row03
abbrev ζ : ℚ := 117647058823529411764705882352/10^30
def b0192 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0192.block Panels0192.accepted Panels0192.integerPanels Panels0192.aligned
    Panels0192.weightRows Panels0192.weights_checked ⟨3, by decide⟩
def b0193 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0193.block Panels0193.accepted Panels0193.integerPanels Panels0193.aligned
    Panels0193.weightRows Panels0193.weights_checked ⟨3, by decide⟩
def b0194 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0194.block Panels0194.accepted Panels0194.integerPanels Panels0194.aligned
    Panels0194.weightRows Panels0194.weights_checked ⟨3, by decide⟩
def b0195 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0195.block Panels0195.accepted Panels0195.integerPanels Panels0195.aligned
    Panels0195.weightRows Panels0195.weights_checked ⟨3, by decide⟩
def b0196 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0196.block Panels0196.accepted Panels0196.integerPanels Panels0196.aligned
    Panels0196.weightRows Panels0196.weights_checked ⟨3, by decide⟩
def b0197 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0197.block Panels0197.accepted Panels0197.integerPanels Panels0197.aligned
    Panels0197.weightRows Panels0197.weights_checked ⟨3, by decide⟩
def b0198 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0198.block Panels0198.accepted Panels0198.integerPanels Panels0198.aligned
    Panels0198.weightRows Panels0198.weights_checked ⟨3, by decide⟩
def b0199 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0199.block Panels0199.accepted Panels0199.integerPanels Panels0199.aligned
    Panels0199.weightRows Panels0199.weights_checked ⟨3, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0192, b0193, b0194, b0195, b0196, b0197, b0198, b0199]
theorem chain_checked : blockChainCheck (4011278304969667087671142319973/10^30) (5150426141637181757933211818553/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=6438150671284557378903573182265546915133311748496691450656233846673575867159079344297133110992219826523084244270822350452552658182892389508630534222704958370508445980766454738740688921718061442819167306952590/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row03
namespace Row04
abbrev ζ : ℚ := 86956521739130434782608695652/10^30
def b0192 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0192.block Panels0192.accepted Panels0192.integerPanels Panels0192.aligned
    Panels0192.weightRows Panels0192.weights_checked ⟨4, by decide⟩
def b0193 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0193.block Panels0193.accepted Panels0193.integerPanels Panels0193.aligned
    Panels0193.weightRows Panels0193.weights_checked ⟨4, by decide⟩
def b0194 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0194.block Panels0194.accepted Panels0194.integerPanels Panels0194.aligned
    Panels0194.weightRows Panels0194.weights_checked ⟨4, by decide⟩
def b0195 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0195.block Panels0195.accepted Panels0195.integerPanels Panels0195.aligned
    Panels0195.weightRows Panels0195.weights_checked ⟨4, by decide⟩
def b0196 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0196.block Panels0196.accepted Panels0196.integerPanels Panels0196.aligned
    Panels0196.weightRows Panels0196.weights_checked ⟨4, by decide⟩
def b0197 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0197.block Panels0197.accepted Panels0197.integerPanels Panels0197.aligned
    Panels0197.weightRows Panels0197.weights_checked ⟨4, by decide⟩
def b0198 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0198.block Panels0198.accepted Panels0198.integerPanels Panels0198.aligned
    Panels0198.weightRows Panels0198.weights_checked ⟨4, by decide⟩
def b0199 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0199.block Panels0199.accepted Panels0199.integerPanels Panels0199.aligned
    Panels0199.weightRows Panels0199.weights_checked ⟨4, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0192, b0193, b0194, b0195, b0196, b0197, b0198, b0199]
theorem chain_checked : blockChainCheck (4011278304969667087671142319973/10^30) (5150426141637181757933211818553/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=6678735583662529487201759046248697663059370258992169137057542305224718578724579072127748776466460255337722673279178491572866728592161437791958614884797706515979619866756239421660328698796000135658155912808590/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row04
namespace Row05
abbrev ζ : ℚ := 64516129032258064516129032258/10^30
def b0192 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0192.block Panels0192.accepted Panels0192.integerPanels Panels0192.aligned
    Panels0192.weightRows Panels0192.weights_checked ⟨5, by decide⟩
def b0193 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0193.block Panels0193.accepted Panels0193.integerPanels Panels0193.aligned
    Panels0193.weightRows Panels0193.weights_checked ⟨5, by decide⟩
def b0194 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0194.block Panels0194.accepted Panels0194.integerPanels Panels0194.aligned
    Panels0194.weightRows Panels0194.weights_checked ⟨5, by decide⟩
def b0195 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0195.block Panels0195.accepted Panels0195.integerPanels Panels0195.aligned
    Panels0195.weightRows Panels0195.weights_checked ⟨5, by decide⟩
def b0196 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0196.block Panels0196.accepted Panels0196.integerPanels Panels0196.aligned
    Panels0196.weightRows Panels0196.weights_checked ⟨5, by decide⟩
def b0197 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0197.block Panels0197.accepted Panels0197.integerPanels Panels0197.aligned
    Panels0197.weightRows Panels0197.weights_checked ⟨5, by decide⟩
def b0198 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0198.block Panels0198.accepted Panels0198.integerPanels Panels0198.aligned
    Panels0198.weightRows Panels0198.weights_checked ⟨5, by decide⟩
def b0199 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0199.block Panels0199.accepted Panels0199.integerPanels Panels0199.aligned
    Panels0199.weightRows Panels0199.weights_checked ⟨5, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0192, b0193, b0194, b0195, b0196, b0197, b0198, b0199]
theorem chain_checked : blockChainCheck (4011278304969667087671142319973/10^30) (5150426141637181757933211818553/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=6859171313718502255843559160119975050066008976008604600561243061926084561332559433247384385867873721487252080473178168125520977621546066388738913479839466045989228214273071107680681409439951017403573822115110/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row05
namespace Row06
abbrev ζ : ℚ := 46511627906976744186046511627/10^30
def b0192 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0192.block Panels0192.accepted Panels0192.integerPanels Panels0192.aligned
    Panels0192.weightRows Panels0192.weights_checked ⟨6, by decide⟩
def b0193 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0193.block Panels0193.accepted Panels0193.integerPanels Panels0193.aligned
    Panels0193.weightRows Panels0193.weights_checked ⟨6, by decide⟩
def b0194 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0194.block Panels0194.accepted Panels0194.integerPanels Panels0194.aligned
    Panels0194.weightRows Panels0194.weights_checked ⟨6, by decide⟩
def b0195 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0195.block Panels0195.accepted Panels0195.integerPanels Panels0195.aligned
    Panels0195.weightRows Panels0195.weights_checked ⟨6, by decide⟩
def b0196 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0196.block Panels0196.accepted Panels0196.integerPanels Panels0196.aligned
    Panels0196.weightRows Panels0196.weights_checked ⟨6, by decide⟩
def b0197 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0197.block Panels0197.accepted Panels0197.integerPanels Panels0197.aligned
    Panels0197.weightRows Panels0197.weights_checked ⟨6, by decide⟩
def b0198 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0198.block Panels0198.accepted Panels0198.integerPanels Panels0198.aligned
    Panels0198.weightRows Panels0198.weights_checked ⟨6, by decide⟩
def b0199 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0199.block Panels0199.accepted Panels0199.integerPanels Panels0199.aligned
    Panels0199.weightRows Panels0199.weights_checked ⟨6, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0192, b0193, b0194, b0195, b0196, b0197, b0198, b0199]
theorem chain_checked : blockChainCheck (4011278304969667087671142319973/10^30) (5150426141637181757933211818553/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=7006750069314214255061491766714134512946358218038385979671254700059380220479303552155979289378816734589721436970576107637015055363982695722194736536717322530555145021156310244468003480820842323074929563508090/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row06
namespace Row07
abbrev ζ : ℚ := 33898305084745762711864406779/10^30
def b0192 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0192.block Panels0192.accepted Panels0192.integerPanels Panels0192.aligned
    Panels0192.weightRows Panels0192.weights_checked ⟨7, by decide⟩
def b0193 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0193.block Panels0193.accepted Panels0193.integerPanels Panels0193.aligned
    Panels0193.weightRows Panels0193.weights_checked ⟨7, by decide⟩
def b0194 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0194.block Panels0194.accepted Panels0194.integerPanels Panels0194.aligned
    Panels0194.weightRows Panels0194.weights_checked ⟨7, by decide⟩
def b0195 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0195.block Panels0195.accepted Panels0195.integerPanels Panels0195.aligned
    Panels0195.weightRows Panels0195.weights_checked ⟨7, by decide⟩
def b0196 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0196.block Panels0196.accepted Panels0196.integerPanels Panels0196.aligned
    Panels0196.weightRows Panels0196.weights_checked ⟨7, by decide⟩
def b0197 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0197.block Panels0197.accepted Panels0197.integerPanels Panels0197.aligned
    Panels0197.weightRows Panels0197.weights_checked ⟨7, by decide⟩
def b0198 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0198.block Panels0198.accepted Panels0198.integerPanels Panels0198.aligned
    Panels0198.weightRows Panels0198.weights_checked ⟨7, by decide⟩
def b0199 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0199.block Panels0199.accepted Panels0199.integerPanels Panels0199.aligned
    Panels0199.weightRows Panels0199.weights_checked ⟨7, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0192, b0193, b0194, b0195, b0196, b0197, b0198, b0199]
theorem chain_checked : blockChainCheck (4011278304969667087671142319973/10^30) (5150426141637181757933211818553/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=7111648075091568532951275451838921917446046974902488701339981986927749545487896807070880397018884635792962194066366623134312028150435272190571593674570292488224162726988437847339189407049809846876047327883130/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row07
namespace Row08
abbrev ζ : ℚ := 25316455696202531645569620253/10^30
def b0192 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0192.block Panels0192.accepted Panels0192.integerPanels Panels0192.aligned
    Panels0192.weightRows Panels0192.weights_checked ⟨8, by decide⟩
def b0193 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0193.block Panels0193.accepted Panels0193.integerPanels Panels0193.aligned
    Panels0193.weightRows Panels0193.weights_checked ⟨8, by decide⟩
def b0194 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0194.block Panels0194.accepted Panels0194.integerPanels Panels0194.aligned
    Panels0194.weightRows Panels0194.weights_checked ⟨8, by decide⟩
def b0195 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0195.block Panels0195.accepted Panels0195.integerPanels Panels0195.aligned
    Panels0195.weightRows Panels0195.weights_checked ⟨8, by decide⟩
def b0196 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0196.block Panels0196.accepted Panels0196.integerPanels Panels0196.aligned
    Panels0196.weightRows Panels0196.weights_checked ⟨8, by decide⟩
def b0197 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0197.block Panels0197.accepted Panels0197.integerPanels Panels0197.aligned
    Panels0197.weightRows Panels0197.weights_checked ⟨8, by decide⟩
def b0198 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0198.block Panels0198.accepted Panels0198.integerPanels Panels0198.aligned
    Panels0198.weightRows Panels0198.weights_checked ⟨8, by decide⟩
def b0199 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0199.block Panels0199.accepted Panels0199.integerPanels Panels0199.aligned
    Panels0199.weightRows Panels0199.weights_checked ⟨8, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0192, b0193, b0194, b0195, b0196, b0197, b0198, b0199]
theorem chain_checked : blockChainCheck (4011278304969667087671142319973/10^30) (5150426141637181757933211818553/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=7183736153514918948862364696974056461561153584290969675516592889072329250135806392952469208926725425176085177349127841452444998303081868725513493084307723170233776195577584984745977782872383241650139514726610/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row08
namespace Row09
abbrev ζ : ℚ := 18691588785046728971962616822/10^30
def b0192 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0192.block Panels0192.accepted Panels0192.integerPanels Panels0192.aligned
    Panels0192.weightRows Panels0192.weights_checked ⟨9, by decide⟩
def b0193 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0193.block Panels0193.accepted Panels0193.integerPanels Panels0193.aligned
    Panels0193.weightRows Panels0193.weights_checked ⟨9, by decide⟩
def b0194 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0194.block Panels0194.accepted Panels0194.integerPanels Panels0194.aligned
    Panels0194.weightRows Panels0194.weights_checked ⟨9, by decide⟩
def b0195 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0195.block Panels0195.accepted Panels0195.integerPanels Panels0195.aligned
    Panels0195.weightRows Panels0195.weights_checked ⟨9, by decide⟩
def b0196 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0196.block Panels0196.accepted Panels0196.integerPanels Panels0196.aligned
    Panels0196.weightRows Panels0196.weights_checked ⟨9, by decide⟩
def b0197 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0197.block Panels0197.accepted Panels0197.integerPanels Panels0197.aligned
    Panels0197.weightRows Panels0197.weights_checked ⟨9, by decide⟩
def b0198 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0198.block Panels0198.accepted Panels0198.integerPanels Panels0198.aligned
    Panels0198.weightRows Panels0198.weights_checked ⟨9, by decide⟩
def b0199 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0199.block Panels0199.accepted Panels0199.integerPanels Panels0199.aligned
    Panels0199.weightRows Panels0199.weights_checked ⟨9, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0192, b0193, b0194, b0195, b0196, b0197, b0198, b0199]
theorem chain_checked : blockChainCheck (4011278304969667087671142319973/10^30) (5150426141637181757933211818553/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=7239785523276799989409151670700690739715888862495650043326060628253496485390411882506530025518475211496833797525879350108284947487342134333027132634745374534615513606548005069624442725855745417919911548449990/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row09
namespace Row10
abbrev ζ : ℚ := 13793103448275862068965517241/10^30
def b0192 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0192.block Panels0192.accepted Panels0192.integerPanels Panels0192.aligned
    Panels0192.weightRows Panels0192.weights_checked ⟨10, by decide⟩
def b0193 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0193.block Panels0193.accepted Panels0193.integerPanels Panels0193.aligned
    Panels0193.weightRows Panels0193.weights_checked ⟨10, by decide⟩
def b0194 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0194.block Panels0194.accepted Panels0194.integerPanels Panels0194.aligned
    Panels0194.weightRows Panels0194.weights_checked ⟨10, by decide⟩
def b0195 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0195.block Panels0195.accepted Panels0195.integerPanels Panels0195.aligned
    Panels0195.weightRows Panels0195.weights_checked ⟨10, by decide⟩
def b0196 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0196.block Panels0196.accepted Panels0196.integerPanels Panels0196.aligned
    Panels0196.weightRows Panels0196.weights_checked ⟨10, by decide⟩
def b0197 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0197.block Panels0197.accepted Panels0197.integerPanels Panels0197.aligned
    Panels0197.weightRows Panels0197.weights_checked ⟨10, by decide⟩
def b0198 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0198.block Panels0198.accepted Panels0198.integerPanels Panels0198.aligned
    Panels0198.weightRows Panels0198.weights_checked ⟨10, by decide⟩
def b0199 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0199.block Panels0199.accepted Panels0199.integerPanels Panels0199.aligned
    Panels0199.weightRows Panels0199.weights_checked ⟨10, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0192, b0193, b0194, b0195, b0196, b0197, b0198, b0199]
theorem chain_checked : blockChainCheck (4011278304969667087671142319973/10^30) (5150426141637181757933211818553/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=7281454152536544331167725260188223523867904661330914418974958708988272441177805591583519226881081534542090471519433829616962398729041517470452666641072756618148759895574632383487778880593708565477920484370130/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row10
namespace Row11
abbrev ζ : ℚ := 10152284263959390862944162436/10^30
def b0192 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0192.block Panels0192.accepted Panels0192.integerPanels Panels0192.aligned
    Panels0192.weightRows Panels0192.weights_checked ⟨11, by decide⟩
def b0193 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0193.block Panels0193.accepted Panels0193.integerPanels Panels0193.aligned
    Panels0193.weightRows Panels0193.weights_checked ⟨11, by decide⟩
def b0194 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0194.block Panels0194.accepted Panels0194.integerPanels Panels0194.aligned
    Panels0194.weightRows Panels0194.weights_checked ⟨11, by decide⟩
def b0195 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0195.block Panels0195.accepted Panels0195.integerPanels Panels0195.aligned
    Panels0195.weightRows Panels0195.weights_checked ⟨11, by decide⟩
def b0196 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0196.block Panels0196.accepted Panels0196.integerPanels Panels0196.aligned
    Panels0196.weightRows Panels0196.weights_checked ⟨11, by decide⟩
def b0197 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0197.block Panels0197.accepted Panels0197.integerPanels Panels0197.aligned
    Panels0197.weightRows Panels0197.weights_checked ⟨11, by decide⟩
def b0198 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0198.block Panels0198.accepted Panels0198.integerPanels Panels0198.aligned
    Panels0198.weightRows Panels0198.weights_checked ⟨11, by decide⟩
def b0199 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0199.block Panels0199.accepted Panels0199.integerPanels Panels0199.aligned
    Panels0199.weightRows Panels0199.weights_checked ⟨11, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0192, b0193, b0194, b0195, b0196, b0197, b0198, b0199]
theorem chain_checked : blockChainCheck (4011278304969667087671142319973/10^30) (5150426141637181757933211818553/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=7312549027231874867918116400265704649937900519756729412251745965694467861614951585193134313644494016386230189120675577107695283388510141101932192154825062532838523628772100357150899177528782788313798247161230/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row11
namespace Row12
abbrev ζ : ℚ := 9950248756218905472636815920/10^30
def b0192 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0192.block Panels0192.accepted Panels0192.integerPanels Panels0192.aligned
    Panels0192.weightRows Panels0192.weights_checked ⟨12, by decide⟩
def b0193 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0193.block Panels0193.accepted Panels0193.integerPanels Panels0193.aligned
    Panels0193.weightRows Panels0193.weights_checked ⟨12, by decide⟩
def b0194 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0194.block Panels0194.accepted Panels0194.integerPanels Panels0194.aligned
    Panels0194.weightRows Panels0194.weights_checked ⟨12, by decide⟩
def b0195 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0195.block Panels0195.accepted Panels0195.integerPanels Panels0195.aligned
    Panels0195.weightRows Panels0195.weights_checked ⟨12, by decide⟩
def b0196 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0196.block Panels0196.accepted Panels0196.integerPanels Panels0196.aligned
    Panels0196.weightRows Panels0196.weights_checked ⟨12, by decide⟩
def b0197 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0197.block Panels0197.accepted Panels0197.integerPanels Panels0197.aligned
    Panels0197.weightRows Panels0197.weights_checked ⟨12, by decide⟩
def b0198 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0198.block Panels0198.accepted Panels0198.integerPanels Panels0198.aligned
    Panels0198.weightRows Panels0198.weights_checked ⟨12, by decide⟩
def b0199 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0199.block Panels0199.accepted Panels0199.integerPanels Panels0199.aligned
    Panels0199.weightRows Panels0199.weights_checked ⟨12, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0192, b0193, b0194, b0195, b0196, b0197, b0198, b0199]
theorem chain_checked : blockChainCheck (4011278304969667087671142319973/10^30) (5150426141637181757933211818553/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=7314277652300050143184546435991830396326831086054034645975011074109452512945706072983933413188810419836880996417426707336073053033174832898213329942588060754460794095015352351200174911056075613312814958984590/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row12
#print axioms Row12.segment
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments024
