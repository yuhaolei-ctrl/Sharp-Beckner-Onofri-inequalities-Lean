module

public import BecknerOnofri.EntropyHeatCheckedWeights
public import BecknerOnofri.EntropyHeatSegments
public import BecknerOnofri.EntropyHeatCertificate.Panels0128
public import BecknerOnofri.EntropyHeatCertificate.Panels0129
public import BecknerOnofri.EntropyHeatCertificate.Panels0130
public import BecknerOnofri.EntropyHeatCertificate.Panels0131
public import BecknerOnofri.EntropyHeatCertificate.Panels0132
public import BecknerOnofri.EntropyHeatCertificate.Panels0133
public import BecknerOnofri.EntropyHeatCertificate.Panels0134
public import BecknerOnofri.EntropyHeatCertificate.Panels0135

@[expose] public section
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments016
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace Row00
abbrev ζ : ℚ := 285714285714285714285714285714/10^30
def b0128 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0128.block Panels0128.accepted Panels0128.integerPanels Panels0128.aligned
    Panels0128.weightRows Panels0128.weights_checked ⟨0, by decide⟩
def b0129 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0129.block Panels0129.accepted Panels0129.integerPanels Panels0129.aligned
    Panels0129.weightRows Panels0129.weights_checked ⟨0, by decide⟩
def b0130 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0130.block Panels0130.accepted Panels0130.integerPanels Panels0130.aligned
    Panels0130.weightRows Panels0130.weights_checked ⟨0, by decide⟩
def b0131 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0131.block Panels0131.accepted Panels0131.integerPanels Panels0131.aligned
    Panels0131.weightRows Panels0131.weights_checked ⟨0, by decide⟩
def b0132 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0132.block Panels0132.accepted Panels0132.integerPanels Panels0132.aligned
    Panels0132.weightRows Panels0132.weights_checked ⟨0, by decide⟩
def b0133 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0133.block Panels0133.accepted Panels0133.integerPanels Panels0133.aligned
    Panels0133.weightRows Panels0133.weights_checked ⟨0, by decide⟩
def b0134 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0134.block Panels0134.accepted Panels0134.integerPanels Panels0134.aligned
    Panels0134.weightRows Panels0134.weights_checked ⟨0, by decide⟩
def b0135 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0135.block Panels0135.accepted Panels0135.integerPanels Panels0135.aligned
    Panels0135.weightRows Panels0135.weights_checked ⟨0, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0128, b0129, b0130, b0131, b0132, b0133, b0134, b0135]
theorem chain_checked : blockChainCheck (543000016158258557301601017683/10^30) (697204548152650608931256665441/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=39782108139714800761957267740333967282617382328644932566597891943320172932920470894529697069924901451956961664527301529267807366298876612171723814867569884549971818577137971529443094192857366590736023218331861984/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row00
namespace Row01
abbrev ζ : ℚ := 222222222222222222222222222222/10^30
def b0128 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0128.block Panels0128.accepted Panels0128.integerPanels Panels0128.aligned
    Panels0128.weightRows Panels0128.weights_checked ⟨1, by decide⟩
def b0129 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0129.block Panels0129.accepted Panels0129.integerPanels Panels0129.aligned
    Panels0129.weightRows Panels0129.weights_checked ⟨1, by decide⟩
def b0130 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0130.block Panels0130.accepted Panels0130.integerPanels Panels0130.aligned
    Panels0130.weightRows Panels0130.weights_checked ⟨1, by decide⟩
def b0131 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0131.block Panels0131.accepted Panels0131.integerPanels Panels0131.aligned
    Panels0131.weightRows Panels0131.weights_checked ⟨1, by decide⟩
def b0132 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0132.block Panels0132.accepted Panels0132.integerPanels Panels0132.aligned
    Panels0132.weightRows Panels0132.weights_checked ⟨1, by decide⟩
def b0133 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0133.block Panels0133.accepted Panels0133.integerPanels Panels0133.aligned
    Panels0133.weightRows Panels0133.weights_checked ⟨1, by decide⟩
def b0134 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0134.block Panels0134.accepted Panels0134.integerPanels Panels0134.aligned
    Panels0134.weightRows Panels0134.weights_checked ⟨1, by decide⟩
def b0135 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0135.block Panels0135.accepted Panels0135.integerPanels Panels0135.aligned
    Panels0135.weightRows Panels0135.weights_checked ⟨1, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0128, b0129, b0130, b0131, b0132, b0133, b0134, b0135]
theorem chain_checked : blockChainCheck (543000016158258557301601017683/10^30) (697204548152650608931256665441/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=95195124135712580462921329015985278265391644616380980924168888480593236776542113588994447020035416407253991335824487567696536863267041550668007722015023374764332438459075052518366464887073534119482553135080441792/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row01
namespace Row02
abbrev ζ : ℚ := 153846153846153846153846153846/10^30
def b0128 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0128.block Panels0128.accepted Panels0128.integerPanels Panels0128.aligned
    Panels0128.weightRows Panels0128.weights_checked ⟨2, by decide⟩
def b0129 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0129.block Panels0129.accepted Panels0129.integerPanels Panels0129.aligned
    Panels0129.weightRows Panels0129.weights_checked ⟨2, by decide⟩
def b0130 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0130.block Panels0130.accepted Panels0130.integerPanels Panels0130.aligned
    Panels0130.weightRows Panels0130.weights_checked ⟨2, by decide⟩
def b0131 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0131.block Panels0131.accepted Panels0131.integerPanels Panels0131.aligned
    Panels0131.weightRows Panels0131.weights_checked ⟨2, by decide⟩
def b0132 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0132.block Panels0132.accepted Panels0132.integerPanels Panels0132.aligned
    Panels0132.weightRows Panels0132.weights_checked ⟨2, by decide⟩
def b0133 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0133.block Panels0133.accepted Panels0133.integerPanels Panels0133.aligned
    Panels0133.weightRows Panels0133.weights_checked ⟨2, by decide⟩
def b0134 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0134.block Panels0134.accepted Panels0134.integerPanels Panels0134.aligned
    Panels0134.weightRows Panels0134.weights_checked ⟨2, by decide⟩
def b0135 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0135.block Panels0135.accepted Panels0135.integerPanels Panels0135.aligned
    Panels0135.weightRows Panels0135.weights_checked ⟨2, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0128, b0129, b0130, b0131, b0132, b0133, b0134, b0135]
theorem chain_checked : blockChainCheck (543000016158258557301601017683/10^30) (697204548152650608931256665441/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=212242014594764443461345964491092703450900510056030143933420944907793014493007195883430059481538587618749346979038746447799542376914674413118640421287853294939798984744359109857276999405091308965057599194856884736/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row02
namespace Row03
abbrev ζ : ℚ := 117647058823529411764705882352/10^30
def b0128 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0128.block Panels0128.accepted Panels0128.integerPanels Panels0128.aligned
    Panels0128.weightRows Panels0128.weights_checked ⟨3, by decide⟩
def b0129 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0129.block Panels0129.accepted Panels0129.integerPanels Panels0129.aligned
    Panels0129.weightRows Panels0129.weights_checked ⟨3, by decide⟩
def b0130 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0130.block Panels0130.accepted Panels0130.integerPanels Panels0130.aligned
    Panels0130.weightRows Panels0130.weights_checked ⟨3, by decide⟩
def b0131 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0131.block Panels0131.accepted Panels0131.integerPanels Panels0131.aligned
    Panels0131.weightRows Panels0131.weights_checked ⟨3, by decide⟩
def b0132 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0132.block Panels0132.accepted Panels0132.integerPanels Panels0132.aligned
    Panels0132.weightRows Panels0132.weights_checked ⟨3, by decide⟩
def b0133 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0133.block Panels0133.accepted Panels0133.integerPanels Panels0133.aligned
    Panels0133.weightRows Panels0133.weights_checked ⟨3, by decide⟩
def b0134 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0134.block Panels0134.accepted Panels0134.integerPanels Panels0134.aligned
    Panels0134.weightRows Panels0134.weights_checked ⟨3, by decide⟩
def b0135 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0135.block Panels0135.accepted Panels0135.integerPanels Panels0135.aligned
    Panels0135.weightRows Panels0135.weights_checked ⟨3, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0128, b0129, b0130, b0131, b0132, b0133, b0134, b0135]
theorem chain_checked : blockChainCheck (543000016158258557301601017683/10^30) (697204548152650608931256665441/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=310120011845703314007245695426688521102563366283560143553126952938530073826802686328900243080610030080951600330492785836810953931742613448577012934274764437255489921733142434538718079166700219309431713981292965232/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row03
namespace Row04
abbrev ζ : ℚ := 86956521739130434782608695652/10^30
def b0128 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0128.block Panels0128.accepted Panels0128.integerPanels Panels0128.aligned
    Panels0128.weightRows Panels0128.weights_checked ⟨4, by decide⟩
def b0129 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0129.block Panels0129.accepted Panels0129.integerPanels Panels0129.aligned
    Panels0129.weightRows Panels0129.weights_checked ⟨4, by decide⟩
def b0130 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0130.block Panels0130.accepted Panels0130.integerPanels Panels0130.aligned
    Panels0130.weightRows Panels0130.weights_checked ⟨4, by decide⟩
def b0131 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0131.block Panels0131.accepted Panels0131.integerPanels Panels0131.aligned
    Panels0131.weightRows Panels0131.weights_checked ⟨4, by decide⟩
def b0132 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0132.block Panels0132.accepted Panels0132.integerPanels Panels0132.aligned
    Panels0132.weightRows Panels0132.weights_checked ⟨4, by decide⟩
def b0133 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0133.block Panels0133.accepted Panels0133.integerPanels Panels0133.aligned
    Panels0133.weightRows Panels0133.weights_checked ⟨4, by decide⟩
def b0134 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0134.block Panels0134.accepted Panels0134.integerPanels Panels0134.aligned
    Panels0134.weightRows Panels0134.weights_checked ⟨4, by decide⟩
def b0135 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0135.block Panels0135.accepted Panels0135.integerPanels Panels0135.aligned
    Panels0135.weightRows Panels0135.weights_checked ⟨4, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0128, b0129, b0130, b0131, b0132, b0133, b0134, b0135]
theorem chain_checked : blockChainCheck (543000016158258557301601017683/10^30) (697204548152650608931256665441/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=419060487477412785062247822068404169146736380882353415831344355252171092681213242825479784937143716731512323162124503428114284630600937358754941874130609288994036945910390519745268395460780197855750378660297375632/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row04
namespace Row05
abbrev ζ : ℚ := 64516129032258064516129032258/10^30
def b0128 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0128.block Panels0128.accepted Panels0128.integerPanels Panels0128.aligned
    Panels0128.weightRows Panels0128.weights_checked ⟨5, by decide⟩
def b0129 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0129.block Panels0129.accepted Panels0129.integerPanels Panels0129.aligned
    Panels0129.weightRows Panels0129.weights_checked ⟨5, by decide⟩
def b0130 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0130.block Panels0130.accepted Panels0130.integerPanels Panels0130.aligned
    Panels0130.weightRows Panels0130.weights_checked ⟨5, by decide⟩
def b0131 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0131.block Panels0131.accepted Panels0131.integerPanels Panels0131.aligned
    Panels0131.weightRows Panels0131.weights_checked ⟨5, by decide⟩
def b0132 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0132.block Panels0132.accepted Panels0132.integerPanels Panels0132.aligned
    Panels0132.weightRows Panels0132.weights_checked ⟨5, by decide⟩
def b0133 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0133.block Panels0133.accepted Panels0133.integerPanels Panels0133.aligned
    Panels0133.weightRows Panels0133.weights_checked ⟨5, by decide⟩
def b0134 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0134.block Panels0134.accepted Panels0134.integerPanels Panels0134.aligned
    Panels0134.weightRows Panels0134.weights_checked ⟨5, by decide⟩
def b0135 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0135.block Panels0135.accepted Panels0135.integerPanels Panels0135.aligned
    Panels0135.weightRows Panels0135.weights_checked ⟨5, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0128, b0129, b0130, b0131, b0132, b0133, b0134, b0135]
theorem chain_checked : blockChainCheck (543000016158258557301601017683/10^30) (697204548152650608931256665441/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=516721300030488946863999135485995218149174775609667311712487881716641548003381796235469587888278371143351748186521763967916755254961099362441424641628058458077366681831573668745731692898370596715374318414103262048/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row05
namespace Row06
abbrev ζ : ℚ := 46511627906976744186046511627/10^30
def b0128 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0128.block Panels0128.accepted Panels0128.integerPanels Panels0128.aligned
    Panels0128.weightRows Panels0128.weights_checked ⟨6, by decide⟩
def b0129 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0129.block Panels0129.accepted Panels0129.integerPanels Panels0129.aligned
    Panels0129.weightRows Panels0129.weights_checked ⟨6, by decide⟩
def b0130 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0130.block Panels0130.accepted Panels0130.integerPanels Panels0130.aligned
    Panels0130.weightRows Panels0130.weights_checked ⟨6, by decide⟩
def b0131 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0131.block Panels0131.accepted Panels0131.integerPanels Panels0131.aligned
    Panels0131.weightRows Panels0131.weights_checked ⟨6, by decide⟩
def b0132 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0132.block Panels0132.accepted Panels0132.integerPanels Panels0132.aligned
    Panels0132.weightRows Panels0132.weights_checked ⟨6, by decide⟩
def b0133 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0133.block Panels0133.accepted Panels0133.integerPanels Panels0133.aligned
    Panels0133.weightRows Panels0133.weights_checked ⟨6, by decide⟩
def b0134 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0134.block Panels0134.accepted Panels0134.integerPanels Panels0134.aligned
    Panels0134.weightRows Panels0134.weights_checked ⟨6, by decide⟩
def b0135 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0135.block Panels0135.accepted Panels0135.integerPanels Panels0135.aligned
    Panels0135.weightRows Panels0135.weights_checked ⟨6, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0128, b0129, b0130, b0131, b0132, b0133, b0134, b0135]
theorem chain_checked : blockChainCheck (543000016158258557301601017683/10^30) (697204548152650608931256665441/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=607656936371386947653905124983077281853567765934335091061847191912454201286096073832789921834778961530060458784906037641645043963902178916479793822705002192615983941685459776235560362227687489225363945930743311432/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row06
namespace Row07
abbrev ζ : ℚ := 33898305084745762711864406779/10^30
def b0128 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0128.block Panels0128.accepted Panels0128.integerPanels Panels0128.aligned
    Panels0128.weightRows Panels0128.weights_checked ⟨7, by decide⟩
def b0129 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0129.block Panels0129.accepted Panels0129.integerPanels Panels0129.aligned
    Panels0129.weightRows Panels0129.weights_checked ⟨7, by decide⟩
def b0130 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0130.block Panels0130.accepted Panels0130.integerPanels Panels0130.aligned
    Panels0130.weightRows Panels0130.weights_checked ⟨7, by decide⟩
def b0131 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0131.block Panels0131.accepted Panels0131.integerPanels Panels0131.aligned
    Panels0131.weightRows Panels0131.weights_checked ⟨7, by decide⟩
def b0132 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0132.block Panels0132.accepted Panels0132.integerPanels Panels0132.aligned
    Panels0132.weightRows Panels0132.weights_checked ⟨7, by decide⟩
def b0133 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0133.block Panels0133.accepted Panels0133.integerPanels Panels0133.aligned
    Panels0133.weightRows Panels0133.weights_checked ⟨7, by decide⟩
def b0134 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0134.block Panels0134.accepted Panels0134.integerPanels Panels0134.aligned
    Panels0134.weightRows Panels0134.weights_checked ⟨7, by decide⟩
def b0135 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0135.block Panels0135.accepted Panels0135.integerPanels Panels0135.aligned
    Panels0135.weightRows Panels0135.weights_checked ⟨7, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0128, b0129, b0130, b0131, b0132, b0133, b0134, b0135]
theorem chain_checked : blockChainCheck (543000016158258557301601017683/10^30) (697204548152650608931256665441/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=678712185546781782238912018464892311771191376272749326050822102247574177593888612957156104967147845231650743158648086480335516629104237457474040466714985131516415043757257938391240073447468142546375299236510386504/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row07
namespace Row08
abbrev ζ : ℚ := 25316455696202531645569620253/10^30
def b0128 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0128.block Panels0128.accepted Panels0128.integerPanels Panels0128.aligned
    Panels0128.weightRows Panels0128.weights_checked ⟨8, by decide⟩
def b0129 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0129.block Panels0129.accepted Panels0129.integerPanels Panels0129.aligned
    Panels0129.weightRows Panels0129.weights_checked ⟨8, by decide⟩
def b0130 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0130.block Panels0130.accepted Panels0130.integerPanels Panels0130.aligned
    Panels0130.weightRows Panels0130.weights_checked ⟨8, by decide⟩
def b0131 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0131.block Panels0131.accepted Panels0131.integerPanels Panels0131.aligned
    Panels0131.weightRows Panels0131.weights_checked ⟨8, by decide⟩
def b0132 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0132.block Panels0132.accepted Panels0132.integerPanels Panels0132.aligned
    Panels0132.weightRows Panels0132.weights_checked ⟨8, by decide⟩
def b0133 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0133.block Panels0133.accepted Panels0133.integerPanels Panels0133.aligned
    Panels0133.weightRows Panels0133.weights_checked ⟨8, by decide⟩
def b0134 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0134.block Panels0134.accepted Panels0134.integerPanels Panels0134.aligned
    Panels0134.weightRows Panels0134.weights_checked ⟨8, by decide⟩
def b0135 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0135.block Panels0135.accepted Panels0135.integerPanels Panels0135.aligned
    Panels0135.weightRows Panels0135.weights_checked ⟨8, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0128, b0129, b0130, b0131, b0132, b0133, b0134, b0135]
theorem chain_checked : blockChainCheck (543000016158258557301601017683/10^30) (697204548152650608931256665441/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=730767227866610061645674195729838963642056179993551973549521453511658273112975368827839417216701058633714798730555590888098706632847333943989697929535240400199469361886365381182357967092736048552952241482600240008/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row08
namespace Row09
abbrev ζ : ℚ := 18691588785046728971962616822/10^30
def b0128 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0128.block Panels0128.accepted Panels0128.integerPanels Panels0128.aligned
    Panels0128.weightRows Panels0128.weights_checked ⟨9, by decide⟩
def b0129 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0129.block Panels0129.accepted Panels0129.integerPanels Panels0129.aligned
    Panels0129.weightRows Panels0129.weights_checked ⟨9, by decide⟩
def b0130 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0130.block Panels0130.accepted Panels0130.integerPanels Panels0130.aligned
    Panels0130.weightRows Panels0130.weights_checked ⟨9, by decide⟩
def b0131 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0131.block Panels0131.accepted Panels0131.integerPanels Panels0131.aligned
    Panels0131.weightRows Panels0131.weights_checked ⟨9, by decide⟩
def b0132 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0132.block Panels0132.accepted Panels0132.integerPanels Panels0132.aligned
    Panels0132.weightRows Panels0132.weights_checked ⟨9, by decide⟩
def b0133 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0133.block Panels0133.accepted Panels0133.integerPanels Panels0133.aligned
    Panels0133.weightRows Panels0133.weights_checked ⟨9, by decide⟩
def b0134 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0134.block Panels0134.accepted Panels0134.integerPanels Panels0134.aligned
    Panels0134.weightRows Panels0134.weights_checked ⟨9, by decide⟩
def b0135 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0135.block Panels0135.accepted Panels0135.integerPanels Panels0135.aligned
    Panels0135.weightRows Panels0135.weights_checked ⟨9, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0128, b0129, b0130, b0131, b0132, b0133, b0134, b0135]
theorem chain_checked : blockChainCheck (543000016158258557301601017683/10^30) (697204548152650608931256665441/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=773108849225099542682527296916600478986732883140858243221613017735192422897809840145474087515036556650488152725338122092439753090203616324413097342056797344353558140257514412799827460889869480323456382770629166592/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row09
namespace Row10
abbrev ζ : ℚ := 13793103448275862068965517241/10^30
def b0128 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0128.block Panels0128.accepted Panels0128.integerPanels Panels0128.aligned
    Panels0128.weightRows Panels0128.weights_checked ⟨10, by decide⟩
def b0129 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0129.block Panels0129.accepted Panels0129.integerPanels Panels0129.aligned
    Panels0129.weightRows Panels0129.weights_checked ⟨10, by decide⟩
def b0130 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0130.block Panels0130.accepted Panels0130.integerPanels Panels0130.aligned
    Panels0130.weightRows Panels0130.weights_checked ⟨10, by decide⟩
def b0131 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0131.block Panels0131.accepted Panels0131.integerPanels Panels0131.aligned
    Panels0131.weightRows Panels0131.weights_checked ⟨10, by decide⟩
def b0132 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0132.block Panels0132.accepted Panels0132.integerPanels Panels0132.aligned
    Panels0132.weightRows Panels0132.weights_checked ⟨10, by decide⟩
def b0133 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0133.block Panels0133.accepted Panels0133.integerPanels Panels0133.aligned
    Panels0133.weightRows Panels0133.weights_checked ⟨10, by decide⟩
def b0134 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0134.block Panels0134.accepted Panels0134.integerPanels Panels0134.aligned
    Panels0134.weightRows Panels0134.weights_checked ⟨10, by decide⟩
def b0135 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0135.block Panels0135.accepted Panels0135.integerPanels Panels0135.aligned
    Panels0135.weightRows Panels0135.weights_checked ⟨10, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0128, b0129, b0130, b0131, b0132, b0133, b0134, b0135]
theorem chain_checked : blockChainCheck (543000016158258557301601017683/10^30) (697204548152650608931256665441/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=805667748356521035072027592682737257782339759468332502544893870717043337623667357286012116592972476629476136523109727999170615845714063385652111575544370690121943778023842479338696434148346061046308924673161642696/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row10
namespace Row11
abbrev ζ : ℚ := 10152284263959390862944162436/10^30
def b0128 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0128.block Panels0128.accepted Panels0128.integerPanels Panels0128.aligned
    Panels0128.weightRows Panels0128.weights_checked ⟨11, by decide⟩
def b0129 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0129.block Panels0129.accepted Panels0129.integerPanels Panels0129.aligned
    Panels0129.weightRows Panels0129.weights_checked ⟨11, by decide⟩
def b0130 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0130.block Panels0130.accepted Panels0130.integerPanels Panels0130.aligned
    Panels0130.weightRows Panels0130.weights_checked ⟨11, by decide⟩
def b0131 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0131.block Panels0131.accepted Panels0131.integerPanels Panels0131.aligned
    Panels0131.weightRows Panels0131.weights_checked ⟨11, by decide⟩
def b0132 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0132.block Panels0132.accepted Panels0132.integerPanels Panels0132.aligned
    Panels0132.weightRows Panels0132.weights_checked ⟨11, by decide⟩
def b0133 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0133.block Panels0133.accepted Panels0133.integerPanels Panels0133.aligned
    Panels0133.weightRows Panels0133.weights_checked ⟨11, by decide⟩
def b0134 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0134.block Panels0134.accepted Panels0134.integerPanels Panels0134.aligned
    Panels0134.weightRows Panels0134.weights_checked ⟨11, by decide⟩
def b0135 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0135.block Panels0135.accepted Panels0135.integerPanels Panels0135.aligned
    Panels0135.weightRows Panels0135.weights_checked ⟨11, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0128, b0129, b0130, b0131, b0132, b0133, b0134, b0135]
theorem chain_checked : blockChainCheck (543000016158258557301601017683/10^30) (697204548152650608931256665441/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=830574403597122081212971786518977684402264011132568361162768870199329498203605729954906153025834793209280275160524385567537801663230288466840493685822420592297395829892168804629817595349574974220250143714847271056/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row11
namespace Row12
abbrev ζ : ℚ := 9950248756218905472636815920/10^30
def b0128 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0128.block Panels0128.accepted Panels0128.integerPanels Panels0128.aligned
    Panels0128.weightRows Panels0128.weights_checked ⟨12, by decide⟩
def b0129 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0129.block Panels0129.accepted Panels0129.integerPanels Panels0129.aligned
    Panels0129.weightRows Panels0129.weights_checked ⟨12, by decide⟩
def b0130 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0130.block Panels0130.accepted Panels0130.integerPanels Panels0130.aligned
    Panels0130.weightRows Panels0130.weights_checked ⟨12, by decide⟩
def b0131 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0131.block Panels0131.accepted Panels0131.integerPanels Panels0131.aligned
    Panels0131.weightRows Panels0131.weights_checked ⟨12, by decide⟩
def b0132 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0132.block Panels0132.accepted Panels0132.integerPanels Panels0132.aligned
    Panels0132.weightRows Panels0132.weights_checked ⟨12, by decide⟩
def b0133 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0133.block Panels0133.accepted Panels0133.integerPanels Panels0133.aligned
    Panels0133.weightRows Panels0133.weights_checked ⟨12, by decide⟩
def b0134 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0134.block Panels0134.accepted Panels0134.integerPanels Panels0134.aligned
    Panels0134.weightRows Panels0134.weights_checked ⟨12, by decide⟩
def b0135 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0135.block Panels0135.accepted Panels0135.integerPanels Panels0135.aligned
    Panels0135.weightRows Panels0135.weights_checked ⟨12, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0128, b0129, b0130, b0131, b0132, b0133, b0134, b0135]
theorem chain_checked : blockChainCheck (543000016158258557301601017683/10^30) (697204548152650608931256665441/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=831974439342872173040749371719884214884738093297884215169040224897774486496057431668791906167837375386305772866662623216815776533412982520168200849106183181118993346412357315596905055711198163769086152232882980720/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row12
#print axioms Row12.segment
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments016
