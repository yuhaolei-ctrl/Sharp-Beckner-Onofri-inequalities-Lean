module

public import BecknerOnofri.EntropyHeatCheckedWeights
public import BecknerOnofri.EntropyHeatSegments
public import BecknerOnofri.EntropyHeatCertificate.Panels0216
public import BecknerOnofri.EntropyHeatCertificate.Panels0217
public import BecknerOnofri.EntropyHeatCertificate.Panels0218
public import BecknerOnofri.EntropyHeatCertificate.Panels0219
public import BecknerOnofri.EntropyHeatCertificate.Panels0220
public import BecknerOnofri.EntropyHeatCertificate.Panels0221
public import BecknerOnofri.EntropyHeatCertificate.Panels0222
public import BecknerOnofri.EntropyHeatCertificate.Panels0223

@[expose] public section
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments027
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace Row00
abbrev ζ : ℚ := 285714285714285714285714285714/10^30
def b0216 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0216.block Panels0216.accepted Panels0216.integerPanels Panels0216.aligned
    Panels0216.weightRows Panels0216.weights_checked ⟨0, by decide⟩
def b0217 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0217.block Panels0217.accepted Panels0217.integerPanels Panels0217.aligned
    Panels0217.weightRows Panels0217.weights_checked ⟨0, by decide⟩
def b0218 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0218.block Panels0218.accepted Panels0218.integerPanels Panels0218.aligned
    Panels0218.weightRows Panels0218.weights_checked ⟨0, by decide⟩
def b0219 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0219.block Panels0219.accepted Panels0219.integerPanels Panels0219.aligned
    Panels0219.weightRows Panels0219.weights_checked ⟨0, by decide⟩
def b0220 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0220.block Panels0220.accepted Panels0220.integerPanels Panels0220.aligned
    Panels0220.weightRows Panels0220.weights_checked ⟨0, by decide⟩
def b0221 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0221.block Panels0221.accepted Panels0221.integerPanels Panels0221.aligned
    Panels0221.weightRows Panels0221.weights_checked ⟨0, by decide⟩
def b0222 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0222.block Panels0222.accepted Panels0222.integerPanels Panels0222.aligned
    Panels0222.weightRows Panels0222.weights_checked ⟨0, by decide⟩
def b0223 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0223.block Panels0223.accepted Panels0223.integerPanels Panels0223.aligned
    Panels0223.weightRows Panels0223.weights_checked ⟨0, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0216, b0217, b0218, b0219, b0220, b0221, b0222, b0223]
theorem chain_checked : blockChainCheck (8491098945861286002391423129665/10^30) (10902454194666651963197333024984/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=2810091691544745991704838993835502450813237348952414982271092555260084736764190249214017431135345871993635966153286156353674196197804905433720808600126898435692379191456784842375500640110176535853078411/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row00
namespace Row01
abbrev ζ : ℚ := 222222222222222222222222222222/10^30
def b0216 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0216.block Panels0216.accepted Panels0216.integerPanels Panels0216.aligned
    Panels0216.weightRows Panels0216.weights_checked ⟨1, by decide⟩
def b0217 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0217.block Panels0217.accepted Panels0217.integerPanels Panels0217.aligned
    Panels0217.weightRows Panels0217.weights_checked ⟨1, by decide⟩
def b0218 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0218.block Panels0218.accepted Panels0218.integerPanels Panels0218.aligned
    Panels0218.weightRows Panels0218.weights_checked ⟨1, by decide⟩
def b0219 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0219.block Panels0219.accepted Panels0219.integerPanels Panels0219.aligned
    Panels0219.weightRows Panels0219.weights_checked ⟨1, by decide⟩
def b0220 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0220.block Panels0220.accepted Panels0220.integerPanels Panels0220.aligned
    Panels0220.weightRows Panels0220.weights_checked ⟨1, by decide⟩
def b0221 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0221.block Panels0221.accepted Panels0221.integerPanels Panels0221.aligned
    Panels0221.weightRows Panels0221.weights_checked ⟨1, by decide⟩
def b0222 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0222.block Panels0222.accepted Panels0222.integerPanels Panels0222.aligned
    Panels0222.weightRows Panels0222.weights_checked ⟨1, by decide⟩
def b0223 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0223.block Panels0223.accepted Panels0223.integerPanels Panels0223.aligned
    Panels0223.weightRows Panels0223.weights_checked ⟨1, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0216, b0217, b0218, b0219, b0220, b0221, b0222, b0223]
theorem chain_checked : blockChainCheck (8491098945861286002391423129665/10^30) (10902454194666651963197333024984/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=2916790201667472474357435308754702275741055204908387189862299210341720703906964841718197900241981587424456609627579701168090792014212945109204438069760823019779691753038485039845885802118054905277393107/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row01
namespace Row02
abbrev ζ : ℚ := 153846153846153846153846153846/10^30
def b0216 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0216.block Panels0216.accepted Panels0216.integerPanels Panels0216.aligned
    Panels0216.weightRows Panels0216.weights_checked ⟨2, by decide⟩
def b0217 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0217.block Panels0217.accepted Panels0217.integerPanels Panels0217.aligned
    Panels0217.weightRows Panels0217.weights_checked ⟨2, by decide⟩
def b0218 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0218.block Panels0218.accepted Panels0218.integerPanels Panels0218.aligned
    Panels0218.weightRows Panels0218.weights_checked ⟨2, by decide⟩
def b0219 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0219.block Panels0219.accepted Panels0219.integerPanels Panels0219.aligned
    Panels0219.weightRows Panels0219.weights_checked ⟨2, by decide⟩
def b0220 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0220.block Panels0220.accepted Panels0220.integerPanels Panels0220.aligned
    Panels0220.weightRows Panels0220.weights_checked ⟨2, by decide⟩
def b0221 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0221.block Panels0221.accepted Panels0221.integerPanels Panels0221.aligned
    Panels0221.weightRows Panels0221.weights_checked ⟨2, by decide⟩
def b0222 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0222.block Panels0222.accepted Panels0222.integerPanels Panels0222.aligned
    Panels0222.weightRows Panels0222.weights_checked ⟨2, by decide⟩
def b0223 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0223.block Panels0223.accepted Panels0223.integerPanels Panels0223.aligned
    Panels0223.weightRows Panels0223.weights_checked ⟨2, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0216, b0217, b0218, b0219, b0220, b0221, b0222, b0223]
theorem chain_checked : blockChainCheck (8491098945861286002391423129665/10^30) (10902454194666651963197333024984/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=3035299482989529986091448938036375964611281608569896165115023205058748162715020349555032833161358198023335572499244321235744416959348436223230549949498801344766109921500062283782987617722487591623472035/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row02
namespace Row03
abbrev ζ : ℚ := 117647058823529411764705882352/10^30
def b0216 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0216.block Panels0216.accepted Panels0216.integerPanels Panels0216.aligned
    Panels0216.weightRows Panels0216.weights_checked ⟨3, by decide⟩
def b0217 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0217.block Panels0217.accepted Panels0217.integerPanels Panels0217.aligned
    Panels0217.weightRows Panels0217.weights_checked ⟨3, by decide⟩
def b0218 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0218.block Panels0218.accepted Panels0218.integerPanels Panels0218.aligned
    Panels0218.weightRows Panels0218.weights_checked ⟨3, by decide⟩
def b0219 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0219.block Panels0219.accepted Panels0219.integerPanels Panels0219.aligned
    Panels0219.weightRows Panels0219.weights_checked ⟨3, by decide⟩
def b0220 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0220.block Panels0220.accepted Panels0220.integerPanels Panels0220.aligned
    Panels0220.weightRows Panels0220.weights_checked ⟨3, by decide⟩
def b0221 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0221.block Panels0221.accepted Panels0221.integerPanels Panels0221.aligned
    Panels0221.weightRows Panels0221.weights_checked ⟨3, by decide⟩
def b0222 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0222.block Panels0222.accepted Panels0222.integerPanels Panels0222.aligned
    Panels0222.weightRows Panels0222.weights_checked ⟨3, by decide⟩
def b0223 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0223.block Panels0223.accepted Panels0223.integerPanels Panels0223.aligned
    Panels0223.weightRows Panels0223.weights_checked ⟨3, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0216, b0217, b0218, b0219, b0220, b0221, b0222, b0223]
theorem chain_checked : blockChainCheck (8491098945861286002391423129665/10^30) (10902454194666651963197333024984/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=3099582417652279628754901939830510506711874722008040687132537102585873404422758361169714316363553406349610320265754772765738483141139398756657281062044212810860890063739850624564462898523077440096981387/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row03
namespace Row04
abbrev ζ : ℚ := 86956521739130434782608695652/10^30
def b0216 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0216.block Panels0216.accepted Panels0216.integerPanels Panels0216.aligned
    Panels0216.weightRows Panels0216.weights_checked ⟨4, by decide⟩
def b0217 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0217.block Panels0217.accepted Panels0217.integerPanels Panels0217.aligned
    Panels0217.weightRows Panels0217.weights_checked ⟨4, by decide⟩
def b0218 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0218.block Panels0218.accepted Panels0218.integerPanels Panels0218.aligned
    Panels0218.weightRows Panels0218.weights_checked ⟨4, by decide⟩
def b0219 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0219.block Panels0219.accepted Panels0219.integerPanels Panels0219.aligned
    Panels0219.weightRows Panels0219.weights_checked ⟨4, by decide⟩
def b0220 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0220.block Panels0220.accepted Panels0220.integerPanels Panels0220.aligned
    Panels0220.weightRows Panels0220.weights_checked ⟨4, by decide⟩
def b0221 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0221.block Panels0221.accepted Panels0221.integerPanels Panels0221.aligned
    Panels0221.weightRows Panels0221.weights_checked ⟨4, by decide⟩
def b0222 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0222.block Panels0222.accepted Panels0222.integerPanels Panels0222.aligned
    Panels0222.weightRows Panels0222.weights_checked ⟨4, by decide⟩
def b0223 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0223.block Panels0223.accepted Panels0223.integerPanels Panels0223.aligned
    Panels0223.weightRows Panels0223.weights_checked ⟨4, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0216, b0217, b0218, b0219, b0220, b0221, b0222, b0223]
theorem chain_checked : blockChainCheck (8491098945861286002391423129665/10^30) (10902454194666651963197333024984/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=3154933014316313943478168123993389552144522911171884407719281099308358479915114862746289830712283086766520391301790339261404284830137636161497176199663378186701036649573265855683014781038528759372451187/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row04
namespace Row05
abbrev ζ : ℚ := 64516129032258064516129032258/10^30
def b0216 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0216.block Panels0216.accepted Panels0216.integerPanels Panels0216.aligned
    Panels0216.weightRows Panels0216.weights_checked ⟨5, by decide⟩
def b0217 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0217.block Panels0217.accepted Panels0217.integerPanels Panels0217.aligned
    Panels0217.weightRows Panels0217.weights_checked ⟨5, by decide⟩
def b0218 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0218.block Panels0218.accepted Panels0218.integerPanels Panels0218.aligned
    Panels0218.weightRows Panels0218.weights_checked ⟨5, by decide⟩
def b0219 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0219.block Panels0219.accepted Panels0219.integerPanels Panels0219.aligned
    Panels0219.weightRows Panels0219.weights_checked ⟨5, by decide⟩
def b0220 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0220.block Panels0220.accepted Panels0220.integerPanels Panels0220.aligned
    Panels0220.weightRows Panels0220.weights_checked ⟨5, by decide⟩
def b0221 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0221.block Panels0221.accepted Panels0221.integerPanels Panels0221.aligned
    Panels0221.weightRows Panels0221.weights_checked ⟨5, by decide⟩
def b0222 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0222.block Panels0222.accepted Panels0222.integerPanels Panels0222.aligned
    Panels0222.weightRows Panels0222.weights_checked ⟨5, by decide⟩
def b0223 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0223.block Panels0223.accepted Panels0223.integerPanels Panels0223.aligned
    Panels0223.weightRows Panels0223.weights_checked ⟨5, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0216, b0217, b0218, b0219, b0220, b0221, b0222, b0223]
theorem chain_checked : blockChainCheck (8491098945861286002391423129665/10^30) (10902454194666651963197333024984/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=3195903117917172638500740630364382352257852320056964475831499116408561304729893314778890306164806249880426353914652130274435954670148818600231367398242308027459772514461252482879275732253879559228042219/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row05
namespace Row06
abbrev ζ : ℚ := 46511627906976744186046511627/10^30
def b0216 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0216.block Panels0216.accepted Panels0216.integerPanels Panels0216.aligned
    Panels0216.weightRows Panels0216.weights_checked ⟨6, by decide⟩
def b0217 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0217.block Panels0217.accepted Panels0217.integerPanels Panels0217.aligned
    Panels0217.weightRows Panels0217.weights_checked ⟨6, by decide⟩
def b0218 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0218.block Panels0218.accepted Panels0218.integerPanels Panels0218.aligned
    Panels0218.weightRows Panels0218.weights_checked ⟨6, by decide⟩
def b0219 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0219.block Panels0219.accepted Panels0219.integerPanels Panels0219.aligned
    Panels0219.weightRows Panels0219.weights_checked ⟨6, by decide⟩
def b0220 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0220.block Panels0220.accepted Panels0220.integerPanels Panels0220.aligned
    Panels0220.weightRows Panels0220.weights_checked ⟨6, by decide⟩
def b0221 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0221.block Panels0221.accepted Panels0221.integerPanels Panels0221.aligned
    Panels0221.weightRows Panels0221.weights_checked ⟨6, by decide⟩
def b0222 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0222.block Panels0222.accepted Panels0222.integerPanels Panels0222.aligned
    Panels0222.weightRows Panels0222.weights_checked ⟨6, by decide⟩
def b0223 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0223.block Panels0223.accepted Panels0223.integerPanels Panels0223.aligned
    Panels0223.weightRows Panels0223.weights_checked ⟨6, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0216, b0217, b0218, b0219, b0220, b0221, b0222, b0223]
theorem chain_checked : blockChainCheck (8491098945861286002391423129665/10^30) (10902454194666651963197333024984/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=3229081569773685042181508132471041157212946856845731640004117158176090701972965433314930182274024113009255033089827647212121754472642963142912998455214411325639711020935664730137911904375223279465677037/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row06
namespace Row07
abbrev ζ : ℚ := 33898305084745762711864406779/10^30
def b0216 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0216.block Panels0216.accepted Panels0216.integerPanels Panels0216.aligned
    Panels0216.weightRows Panels0216.weights_checked ⟨7, by decide⟩
def b0217 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0217.block Panels0217.accepted Panels0217.integerPanels Panels0217.aligned
    Panels0217.weightRows Panels0217.weights_checked ⟨7, by decide⟩
def b0218 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0218.block Panels0218.accepted Panels0218.integerPanels Panels0218.aligned
    Panels0218.weightRows Panels0218.weights_checked ⟨7, by decide⟩
def b0219 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0219.block Panels0219.accepted Panels0219.integerPanels Panels0219.aligned
    Panels0219.weightRows Panels0219.weights_checked ⟨7, by decide⟩
def b0220 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0220.block Panels0220.accepted Panels0220.integerPanels Panels0220.aligned
    Panels0220.weightRows Panels0220.weights_checked ⟨7, by decide⟩
def b0221 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0221.block Panels0221.accepted Panels0221.integerPanels Panels0221.aligned
    Panels0221.weightRows Panels0221.weights_checked ⟨7, by decide⟩
def b0222 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0222.block Panels0222.accepted Panels0222.integerPanels Panels0222.aligned
    Panels0222.weightRows Panels0222.weights_checked ⟨7, by decide⟩
def b0223 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0223.block Panels0223.accepted Panels0223.integerPanels Panels0223.aligned
    Panels0223.weightRows Panels0223.weights_checked ⟨7, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0216, b0217, b0218, b0219, b0220, b0221, b0222, b0223]
theorem chain_checked : blockChainCheck (8491098945861286002391423129665/10^30) (10902454194666651963197333024984/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=3252489090925865703002751156735144888158613881552338376718175247227948118415238480861394796993833768363447295156201915952286080064221604271808846820325801510490270857204090028644202113334262035862330701/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row07
namespace Row08
abbrev ζ : ℚ := 25316455696202531645569620253/10^30
def b0216 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0216.block Panels0216.accepted Panels0216.integerPanels Panels0216.aligned
    Panels0216.weightRows Panels0216.weights_checked ⟨8, by decide⟩
def b0217 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0217.block Panels0217.accepted Panels0217.integerPanels Panels0217.aligned
    Panels0217.weightRows Panels0217.weights_checked ⟨8, by decide⟩
def b0218 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0218.block Panels0218.accepted Panels0218.integerPanels Panels0218.aligned
    Panels0218.weightRows Panels0218.weights_checked ⟨8, by decide⟩
def b0219 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0219.block Panels0219.accepted Panels0219.integerPanels Panels0219.aligned
    Panels0219.weightRows Panels0219.weights_checked ⟨8, by decide⟩
def b0220 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0220.block Panels0220.accepted Panels0220.integerPanels Panels0220.aligned
    Panels0220.weightRows Panels0220.weights_checked ⟨8, by decide⟩
def b0221 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0221.block Panels0221.accepted Panels0221.integerPanels Panels0221.aligned
    Panels0221.weightRows Panels0221.weights_checked ⟨8, by decide⟩
def b0222 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0222.block Panels0222.accepted Panels0222.integerPanels Panels0222.aligned
    Panels0222.weightRows Panels0222.weights_checked ⟨8, by decide⟩
def b0223 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0223.block Panels0223.accepted Panels0223.integerPanels Panels0223.aligned
    Panels0223.weightRows Panels0223.weights_checked ⟨8, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0216, b0217, b0218, b0219, b0220, b0221, b0222, b0223]
theorem chain_checked : blockChainCheck (8491098945861286002391423129665/10^30) (10902454194666651963197333024984/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=3268492618967738348262252883068850299190031984784094126384211473524795711351024101444145113150804911457218098628421388663731463233867673803635869782448484837643880610943012306411057630913757511273648989/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row08
namespace Row09
abbrev ζ : ℚ := 18691588785046728971962616822/10^30
def b0216 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0216.block Panels0216.accepted Panels0216.integerPanels Panels0216.aligned
    Panels0216.weightRows Panels0216.weights_checked ⟨9, by decide⟩
def b0217 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0217.block Panels0217.accepted Panels0217.integerPanels Panels0217.aligned
    Panels0217.weightRows Panels0217.weights_checked ⟨9, by decide⟩
def b0218 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0218.block Panels0218.accepted Panels0218.integerPanels Panels0218.aligned
    Panels0218.weightRows Panels0218.weights_checked ⟨9, by decide⟩
def b0219 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0219.block Panels0219.accepted Panels0219.integerPanels Panels0219.aligned
    Panels0219.weightRows Panels0219.weights_checked ⟨9, by decide⟩
def b0220 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0220.block Panels0220.accepted Panels0220.integerPanels Panels0220.aligned
    Panels0220.weightRows Panels0220.weights_checked ⟨9, by decide⟩
def b0221 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0221.block Panels0221.accepted Panels0221.integerPanels Panels0221.aligned
    Panels0221.weightRows Panels0221.weights_checked ⟨9, by decide⟩
def b0222 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0222.block Panels0222.accepted Panels0222.integerPanels Panels0222.aligned
    Panels0222.weightRows Panels0222.weights_checked ⟨9, by decide⟩
def b0223 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0223.block Panels0223.accepted Panels0223.integerPanels Panels0223.aligned
    Panels0223.weightRows Panels0223.weights_checked ⟨9, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0216, b0217, b0218, b0219, b0220, b0221, b0222, b0223]
theorem chain_checked : blockChainCheck (8491098945861286002391423129665/10^30) (10902454194666651963197333024984/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=3280889818793382384255107558927555926655928833196156920807460992015145576653023728165246549949848088954765531174421960812373980427646834844772647715790007352741789055529050235326822080500802248772780707/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row09
namespace Row10
abbrev ζ : ℚ := 13793103448275862068965517241/10^30
def b0216 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0216.block Panels0216.accepted Panels0216.integerPanels Panels0216.aligned
    Panels0216.weightRows Panels0216.weights_checked ⟨10, by decide⟩
def b0217 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0217.block Panels0217.accepted Panels0217.integerPanels Panels0217.aligned
    Panels0217.weightRows Panels0217.weights_checked ⟨10, by decide⟩
def b0218 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0218.block Panels0218.accepted Panels0218.integerPanels Panels0218.aligned
    Panels0218.weightRows Panels0218.weights_checked ⟨10, by decide⟩
def b0219 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0219.block Panels0219.accepted Panels0219.integerPanels Panels0219.aligned
    Panels0219.weightRows Panels0219.weights_checked ⟨10, by decide⟩
def b0220 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0220.block Panels0220.accepted Panels0220.integerPanels Panels0220.aligned
    Panels0220.weightRows Panels0220.weights_checked ⟨10, by decide⟩
def b0221 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0221.block Panels0221.accepted Panels0221.integerPanels Panels0221.aligned
    Panels0221.weightRows Panels0221.weights_checked ⟨10, by decide⟩
def b0222 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0222.block Panels0222.accepted Panels0222.integerPanels Panels0222.aligned
    Panels0222.weightRows Panels0222.weights_checked ⟨10, by decide⟩
def b0223 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0223.block Panels0223.accepted Panels0223.integerPanels Panels0223.aligned
    Panels0223.weightRows Panels0223.weights_checked ⟨10, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0216, b0217, b0218, b0219, b0220, b0221, b0222, b0223]
theorem chain_checked : blockChainCheck (8491098945861286002391423129665/10^30) (10902454194666651963197333024984/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=3290080608917041679644374899073218154218751327425692517682844195963390098162540286137768947115791777340441267985320635892863192799524160901961274131544296427387720288975807018264770001081733581724439605/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row10
namespace Row11
abbrev ζ : ℚ := 10152284263959390862944162436/10^30
def b0216 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0216.block Panels0216.accepted Panels0216.integerPanels Panels0216.aligned
    Panels0216.weightRows Panels0216.weights_checked ⟨11, by decide⟩
def b0217 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0217.block Panels0217.accepted Panels0217.integerPanels Panels0217.aligned
    Panels0217.weightRows Panels0217.weights_checked ⟨11, by decide⟩
def b0218 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0218.block Panels0218.accepted Panels0218.integerPanels Panels0218.aligned
    Panels0218.weightRows Panels0218.weights_checked ⟨11, by decide⟩
def b0219 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0219.block Panels0219.accepted Panels0219.integerPanels Panels0219.aligned
    Panels0219.weightRows Panels0219.weights_checked ⟨11, by decide⟩
def b0220 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0220.block Panels0220.accepted Panels0220.integerPanels Panels0220.aligned
    Panels0220.weightRows Panels0220.weights_checked ⟨11, by decide⟩
def b0221 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0221.block Panels0221.accepted Panels0221.integerPanels Panels0221.aligned
    Panels0221.weightRows Panels0221.weights_checked ⟨11, by decide⟩
def b0222 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0222.block Panels0222.accepted Panels0222.integerPanels Panels0222.aligned
    Panels0222.weightRows Panels0222.weights_checked ⟨11, by decide⟩
def b0223 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0223.block Panels0223.accepted Panels0223.integerPanels Panels0223.aligned
    Panels0223.weightRows Panels0223.weights_checked ⟨11, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0216, b0217, b0218, b0219, b0220, b0221, b0222, b0223]
theorem chain_checked : blockChainCheck (8491098945861286002391423129665/10^30) (10902454194666651963197333024984/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=3296925048072009747949743763740016691159118363685162306996952199456108071364848441772368603123879505892436992660755410825938559189600098572820865301542458058883154263874325423316855197174989213413351475/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row11
namespace Row12
abbrev ζ : ℚ := 9950248756218905472636815920/10^30
def b0216 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0216.block Panels0216.accepted Panels0216.integerPanels Panels0216.aligned
    Panels0216.weightRows Panels0216.weights_checked ⟨12, by decide⟩
def b0217 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0217.block Panels0217.accepted Panels0217.integerPanels Panels0217.aligned
    Panels0217.weightRows Panels0217.weights_checked ⟨12, by decide⟩
def b0218 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0218.block Panels0218.accepted Panels0218.integerPanels Panels0218.aligned
    Panels0218.weightRows Panels0218.weights_checked ⟨12, by decide⟩
def b0219 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0219.block Panels0219.accepted Panels0219.integerPanels Panels0219.aligned
    Panels0219.weightRows Panels0219.weights_checked ⟨12, by decide⟩
def b0220 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0220.block Panels0220.accepted Panels0220.integerPanels Panels0220.aligned
    Panels0220.weightRows Panels0220.weights_checked ⟨12, by decide⟩
def b0221 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0221.block Panels0221.accepted Panels0221.integerPanels Panels0221.aligned
    Panels0221.weightRows Panels0221.weights_checked ⟨12, by decide⟩
def b0222 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0222.block Panels0222.accepted Panels0222.integerPanels Panels0222.aligned
    Panels0222.weightRows Panels0222.weights_checked ⟨12, by decide⟩
def b0223 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0223.block Panels0223.accepted Panels0223.integerPanels Panels0223.aligned
    Panels0223.weightRows Panels0223.weights_checked ⟨12, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0216, b0217, b0218, b0219, b0220, b0221, b0222, b0223]
theorem chain_checked : blockChainCheck (8491098945861286002391423129665/10^30) (10902454194666651963197333024984/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=3297305191767032391057974748943010807144201410702857889528195106535373224653620430547771818081502491831600931157433553018731006158662801841470768775802541787861763929184800705464575895261510701639651083/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row12
#print axioms Row12.segment
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments027
