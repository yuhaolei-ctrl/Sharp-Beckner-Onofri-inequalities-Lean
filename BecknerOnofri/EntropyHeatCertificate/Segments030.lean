module

public import BecknerOnofri.EntropyHeatCheckedWeights
public import BecknerOnofri.EntropyHeatSegments
public import BecknerOnofri.EntropyHeatCertificate.Panels0240
public import BecknerOnofri.EntropyHeatCertificate.Panels0241
public import BecknerOnofri.EntropyHeatCertificate.Panels0242
public import BecknerOnofri.EntropyHeatCertificate.Panels0243

@[expose] public section
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments030
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace Row00
abbrev ζ : ℚ := 285714285714285714285714285714/10^30
def b0240 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0240.block Panels0240.accepted Panels0240.integerPanels Panels0240.aligned
    Panels0240.weightRows Panels0240.weights_checked ⟨0, by decide⟩
def b0241 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0241.block Panels0241.accepted Panels0241.integerPanels Panels0241.aligned
    Panels0241.weightRows Panels0241.weights_checked ⟨0, by decide⟩
def b0242 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0242.block Panels0242.accepted Panels0242.integerPanels Panels0242.aligned
    Panels0242.weightRows Panels0242.weights_checked ⟨0, by decide⟩
def b0243 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0243.block Panels0243.accepted Panels0243.integerPanels Panels0243.aligned
    Panels0243.weightRows Panels0243.weights_checked ⟨0, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0240, b0241, b0242, b0243]
theorem chain_checked : blockChainCheck (17974011232050837835132378248720/10^30) (20000000000000000000000000000000/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=57129720930145758219818565898749631858390695669315057578202351937662646156136449144281994701331545692710621366821956616127474852849374818721872241289837523665031842675718757273033797260433/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row00
namespace Row01
abbrev ζ : ℚ := 222222222222222222222222222222/10^30
def b0240 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0240.block Panels0240.accepted Panels0240.integerPanels Panels0240.aligned
    Panels0240.weightRows Panels0240.weights_checked ⟨1, by decide⟩
def b0241 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0241.block Panels0241.accepted Panels0241.integerPanels Panels0241.aligned
    Panels0241.weightRows Panels0241.weights_checked ⟨1, by decide⟩
def b0242 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0242.block Panels0242.accepted Panels0242.integerPanels Panels0242.aligned
    Panels0242.weightRows Panels0242.weights_checked ⟨1, by decide⟩
def b0243 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0243.block Panels0243.accepted Panels0243.integerPanels Panels0243.aligned
    Panels0243.weightRows Panels0243.weights_checked ⟨1, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0240, b0241, b0242, b0243]
theorem chain_checked : blockChainCheck (17974011232050837835132378248720/10^30) (20000000000000000000000000000000/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=58103291824182174048091375947394308126642459373235953704540750687362143362096973410978460161525158305572005104388279898311502349004873033369086179863236404647715715092298636616420947854041/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row01
namespace Row02
abbrev ζ : ℚ := 153846153846153846153846153846/10^30
def b0240 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0240.block Panels0240.accepted Panels0240.integerPanels Panels0240.aligned
    Panels0240.weightRows Panels0240.weights_checked ⟨2, by decide⟩
def b0241 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0241.block Panels0241.accepted Panels0241.integerPanels Panels0241.aligned
    Panels0241.weightRows Panels0241.weights_checked ⟨2, by decide⟩
def b0242 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0242.block Panels0242.accepted Panels0242.integerPanels Panels0242.aligned
    Panels0242.weightRows Panels0242.weights_checked ⟨2, by decide⟩
def b0243 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0243.block Panels0243.accepted Panels0243.integerPanels Panels0243.aligned
    Panels0243.weightRows Panels0243.weights_checked ⟨2, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0240, b0241, b0242, b0243]
theorem chain_checked : blockChainCheck (17974011232050837835132378248720/10^30) (20000000000000000000000000000000/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=59166564844308185444626256929253201166938608728105346141950526245774163439642350631062219831453748203009052611001946152240814580392853717018900614974167785490427277782832394446238115050985/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row02
namespace Row03
abbrev ζ : ℚ := 117647058823529411764705882352/10^30
def b0240 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0240.block Panels0240.accepted Panels0240.integerPanels Panels0240.aligned
    Panels0240.weightRows Panels0240.weights_checked ⟨3, by decide⟩
def b0241 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0241.block Panels0241.accepted Panels0241.integerPanels Panels0241.aligned
    Panels0241.weightRows Panels0241.weights_checked ⟨3, by decide⟩
def b0242 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0242.block Panels0242.accepted Panels0242.integerPanels Panels0242.aligned
    Panels0242.weightRows Panels0242.weights_checked ⟨3, by decide⟩
def b0243 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0243.block Panels0243.accepted Panels0243.integerPanels Panels0243.aligned
    Panels0243.weightRows Panels0243.weights_checked ⟨3, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0240, b0241, b0242, b0243]
theorem chain_checked : blockChainCheck (17974011232050837835132378248720/10^30) (20000000000000000000000000000000/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=59735748559663076555090661697090841568212558171140052439146478157524900686641300027232353493752309591613725737221799509255426108358248499167915914251207547202864065130691913115165019139081/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row03
namespace Row04
abbrev ζ : ℚ := 86956521739130434782608695652/10^30
def b0240 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0240.block Panels0240.accepted Panels0240.integerPanels Panels0240.aligned
    Panels0240.weightRows Panels0240.weights_checked ⟨4, by decide⟩
def b0241 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0241.block Panels0241.accepted Panels0241.integerPanels Panels0241.aligned
    Panels0241.weightRows Panels0241.weights_checked ⟨4, by decide⟩
def b0242 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0242.block Panels0242.accepted Panels0242.integerPanels Panels0242.aligned
    Panels0242.weightRows Panels0242.weights_checked ⟨4, by decide⟩
def b0243 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0243.block Panels0243.accepted Panels0243.integerPanels Panels0243.aligned
    Panels0243.weightRows Panels0243.weights_checked ⟨4, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0240, b0241, b0242, b0243]
theorem chain_checked : blockChainCheck (17974011232050837835132378248720/10^30) (20000000000000000000000000000000/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=60221744468419588222918950620140644928728377611406885473235052343766290360533340315807503758591791698714286078949408366079699213536209777909204104347750156126641696152550274405279352750481/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row04
namespace Row05
abbrev ζ : ℚ := 64516129032258064516129032258/10^30
def b0240 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0240.block Panels0240.accepted Panels0240.integerPanels Panels0240.aligned
    Panels0240.weightRows Panels0240.weights_checked ⟨5, by decide⟩
def b0241 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0241.block Panels0241.accepted Panels0241.integerPanels Panels0241.aligned
    Panels0241.weightRows Panels0241.weights_checked ⟨5, by decide⟩
def b0242 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0242.block Panels0242.accepted Panels0242.integerPanels Panels0242.aligned
    Panels0242.weightRows Panels0242.weights_checked ⟨5, by decide⟩
def b0243 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0243.block Panels0243.accepted Panels0243.integerPanels Panels0243.aligned
    Panels0243.weightRows Panels0243.weights_checked ⟨5, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0240, b0241, b0242, b0243]
theorem chain_checked : blockChainCheck (17974011232050837835132378248720/10^30) (20000000000000000000000000000000/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=60579096153506988158456169264670156287260636676665710656167043563291581589595805902926202544388908940230065584259676713657560112214342655219471426262634435752948223384993615742885841099377/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row05
namespace Row06
abbrev ζ : ℚ := 46511627906976744186046511627/10^30
def b0240 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0240.block Panels0240.accepted Panels0240.integerPanels Panels0240.aligned
    Panels0240.weightRows Panels0240.weights_checked ⟨6, by decide⟩
def b0241 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0241.block Panels0241.accepted Panels0241.integerPanels Panels0241.aligned
    Panels0241.weightRows Panels0241.weights_checked ⟨6, by decide⟩
def b0242 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0242.block Panels0242.accepted Panels0242.integerPanels Panels0242.aligned
    Panels0242.weightRows Panels0242.weights_checked ⟨6, by decide⟩
def b0243 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0243.block Panels0243.accepted Panels0243.integerPanels Panels0243.aligned
    Panels0243.weightRows Panels0243.weights_checked ⟨6, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0240, b0241, b0242, b0243]
theorem chain_checked : blockChainCheck (17974011232050837835132378248720/10^30) (20000000000000000000000000000000/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=60867034561788158359504698545700328361149364260444456216419752833099367554183713712578601546434441862177077251825931794977180236514820093879621621210031803435264186722126835426925272607031/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row06
namespace Row07
abbrev ζ : ℚ := 33898305084745762711864406779/10^30
def b0240 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0240.block Panels0240.accepted Panels0240.integerPanels Panels0240.aligned
    Panels0240.weightRows Panels0240.weights_checked ⟨7, by decide⟩
def b0241 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0241.block Panels0241.accepted Panels0241.integerPanels Panels0241.aligned
    Panels0241.weightRows Panels0241.weights_checked ⟨7, by decide⟩
def b0242 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0242.block Panels0242.accepted Panels0242.integerPanels Panels0242.aligned
    Panels0242.weightRows Panels0242.weights_checked ⟨7, by decide⟩
def b0243 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0243.block Panels0243.accepted Panels0243.integerPanels Panels0243.aligned
    Panels0243.weightRows Panels0243.weights_checked ⟨7, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0240, b0241, b0242, b0243]
theorem chain_checked : blockChainCheck (17974011232050837835132378248720/10^30) (20000000000000000000000000000000/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=61069406156971075667256406138101118740132609866598516829562263671419357744426925916867699660055232673373366478644115134032491006059270695239055971074631297983855594499235519845833063049303/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row07
namespace Row08
abbrev ζ : ℚ := 25316455696202531645569620253/10^30
def b0240 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0240.block Panels0240.accepted Panels0240.integerPanels Panels0240.aligned
    Panels0240.weightRows Panels0240.weights_checked ⟨8, by decide⟩
def b0241 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0241.block Panels0241.accepted Panels0241.integerPanels Panels0241.aligned
    Panels0241.weightRows Panels0241.weights_checked ⟨8, by decide⟩
def b0242 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0242.block Panels0242.accepted Panels0242.integerPanels Panels0242.aligned
    Panels0242.weightRows Panels0242.weights_checked ⟨8, by decide⟩
def b0243 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0243.block Panels0243.accepted Panels0243.integerPanels Panels0243.aligned
    Panels0243.weightRows Panels0243.weights_checked ⟨8, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0240, b0241, b0242, b0243]
theorem chain_checked : blockChainCheck (17974011232050837835132378248720/10^30) (20000000000000000000000000000000/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=61207403429507618043257014812080224420541977133015869976355336379183912709527812287156691427847028394390778360381318127893976662967908268344495418726017279478270648047668118327218288258887/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row08
namespace Row09
abbrev ζ : ℚ := 18691588785046728971962616822/10^30
def b0240 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0240.block Panels0240.accepted Panels0240.integerPanels Panels0240.aligned
    Panels0240.weightRows Panels0240.weights_checked ⟨9, by decide⟩
def b0241 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0241.block Panels0241.accepted Panels0241.integerPanels Panels0241.aligned
    Panels0241.weightRows Panels0241.weights_checked ⟨9, by decide⟩
def b0242 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0242.block Panels0242.accepted Panels0242.integerPanels Panels0242.aligned
    Panels0242.weightRows Panels0242.weights_checked ⟨9, by decide⟩
def b0243 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0243.block Panels0243.accepted Panels0243.integerPanels Panels0243.aligned
    Panels0243.weightRows Panels0243.weights_checked ⟨9, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0240, b0241, b0242, b0243]
theorem chain_checked : blockChainCheck (17974011232050837835132378248720/10^30) (20000000000000000000000000000000/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=61314102856850732272945276780418491598017614120195927077556290537972891986698000988079422693815200830141881943882371015424247333700173737204670682030394083561102645662357313912461137860841/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row09
namespace Row10
abbrev ζ : ℚ := 13793103448275862068965517241/10^30
def b0240 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0240.block Panels0240.accepted Panels0240.integerPanels Panels0240.aligned
    Panels0240.weightRows Panels0240.weights_checked ⟨10, by decide⟩
def b0241 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0241.block Panels0241.accepted Panels0241.integerPanels Panels0241.aligned
    Panels0241.weightRows Panels0241.weights_checked ⟨10, by decide⟩
def b0242 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0242.block Panels0242.accepted Panels0242.integerPanels Panels0242.aligned
    Panels0242.weightRows Panels0242.weights_checked ⟨10, by decide⟩
def b0243 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0243.block Panels0243.accepted Panels0243.integerPanels Panels0243.aligned
    Panels0243.weightRows Panels0243.weights_checked ⟨10, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0240, b0241, b0242, b0243]
theorem chain_checked : blockChainCheck (17974011232050837835132378248720/10^30) (20000000000000000000000000000000/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=61393093101097399621308206069904471027432130822342520423993748407602228183327237853361774724012238269759105079448769712331915282170863755663003700115422397221223899808099428902796189788495/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row10
namespace Row11
abbrev ζ : ℚ := 10152284263959390862944162436/10^30
def b0240 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0240.block Panels0240.accepted Panels0240.integerPanels Panels0240.aligned
    Panels0240.weightRows Panels0240.weights_checked ⟨11, by decide⟩
def b0241 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0241.block Panels0241.accepted Panels0241.integerPanels Panels0241.aligned
    Panels0241.weightRows Panels0241.weights_checked ⟨11, by decide⟩
def b0242 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0242.block Panels0242.accepted Panels0242.integerPanels Panels0242.aligned
    Panels0242.weightRows Panels0242.weights_checked ⟨11, by decide⟩
def b0243 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0243.block Panels0243.accepted Panels0243.integerPanels Panels0243.aligned
    Panels0243.weightRows Panels0243.weights_checked ⟨11, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0240, b0241, b0242, b0243]
theorem chain_checked : blockChainCheck (17974011232050837835132378248720/10^30) (20000000000000000000000000000000/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=61451855696974468335522045521403852454608140741595967730386438964284354849373859040001955329226881438384485680911166128825526832440399988463765238393874795555912613198623925389208567821905/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row11
namespace Row12
abbrev ζ : ℚ := 9950248756218905472636815920/10^30
def b0240 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0240.block Panels0240.accepted Panels0240.integerPanels Panels0240.aligned
    Panels0240.weightRows Panels0240.weights_checked ⟨12, by decide⟩
def b0241 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0241.block Panels0241.accepted Panels0241.integerPanels Panels0241.aligned
    Panels0241.weightRows Panels0241.weights_checked ⟨12, by decide⟩
def b0242 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0242.block Panels0242.accepted Panels0242.integerPanels Panels0242.aligned
    Panels0242.weightRows Panels0242.weights_checked ⟨12, by decide⟩
def b0243 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0243.block Panels0243.accepted Panels0243.integerPanels Panels0243.aligned
    Panels0243.weightRows Panels0243.weights_checked ⟨12, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0240, b0241, b0242, b0243]
theorem chain_checked : blockChainCheck (17974011232050837835132378248720/10^30) (20000000000000000000000000000000/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=61455117856066506284745477038506945754045898780617662984863665254143001240835478312040936433277753854197862278394772044132725165139262857278908040033624580104967994714275811370437058984329/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row12
#print axioms Row12.segment
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments030
