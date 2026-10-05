module

public import BecknerOnofri.EntropyHeatCheckedWeights
public import BecknerOnofri.EntropyHeatSegments
public import BecknerOnofri.EntropyHeatCertificate.Panels0096
public import BecknerOnofri.EntropyHeatCertificate.Panels0097
public import BecknerOnofri.EntropyHeatCertificate.Panels0098
public import BecknerOnofri.EntropyHeatCertificate.Panels0099
public import BecknerOnofri.EntropyHeatCertificate.Panels0100
public import BecknerOnofri.EntropyHeatCertificate.Panels0101
public import BecknerOnofri.EntropyHeatCertificate.Panels0102
public import BecknerOnofri.EntropyHeatCertificate.Panels0103

@[expose] public section
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments012
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace Row00
abbrev ζ : ℚ := 285714285714285714285714285714/10^30
def b0096 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0096.block Panels0096.accepted Panels0096.integerPanels Panels0096.aligned
    Panels0096.weightRows Panels0096.weights_checked ⟨0, by decide⟩
def b0097 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0097.block Panels0097.accepted Panels0097.integerPanels Panels0097.aligned
    Panels0097.weightRows Panels0097.weights_checked ⟨0, by decide⟩
def b0098 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0098.block Panels0098.accepted Panels0098.integerPanels Panels0098.aligned
    Panels0098.weightRows Panels0098.weights_checked ⟨0, by decide⟩
def b0099 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0099.block Panels0099.accepted Panels0099.integerPanels Panels0099.aligned
    Panels0099.weightRows Panels0099.weights_checked ⟨0, by decide⟩
def b0100 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0100.block Panels0100.accepted Panels0100.integerPanels Panels0100.aligned
    Panels0100.weightRows Panels0100.weights_checked ⟨0, by decide⟩
def b0101 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0101.block Panels0101.accepted Panels0101.integerPanels Panels0101.aligned
    Panels0101.weightRows Panels0101.weights_checked ⟨0, by decide⟩
def b0102 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0102.block Panels0102.accepted Panels0102.integerPanels Panels0102.aligned
    Panels0102.weightRows Panels0102.weights_checked ⟨0, by decide⟩
def b0103 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0103.block Panels0103.accepted Panels0103.integerPanels Panels0103.aligned
    Panels0103.weightRows Panels0103.weights_checked ⟨0, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0096, b0097, b0098, b0099, b0100, b0101, b0102, b0103]
theorem chain_checked : blockChainCheck (199782924607866098106963165277/10^30) (256518525847052817488239228851/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=0/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row00
namespace Row01
abbrev ζ : ℚ := 222222222222222222222222222222/10^30
def b0096 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0096.block Panels0096.accepted Panels0096.integerPanels Panels0096.aligned
    Panels0096.weightRows Panels0096.weights_checked ⟨1, by decide⟩
def b0097 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0097.block Panels0097.accepted Panels0097.integerPanels Panels0097.aligned
    Panels0097.weightRows Panels0097.weights_checked ⟨1, by decide⟩
def b0098 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0098.block Panels0098.accepted Panels0098.integerPanels Panels0098.aligned
    Panels0098.weightRows Panels0098.weights_checked ⟨1, by decide⟩
def b0099 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0099.block Panels0099.accepted Panels0099.integerPanels Panels0099.aligned
    Panels0099.weightRows Panels0099.weights_checked ⟨1, by decide⟩
def b0100 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0100.block Panels0100.accepted Panels0100.integerPanels Panels0100.aligned
    Panels0100.weightRows Panels0100.weights_checked ⟨1, by decide⟩
def b0101 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0101.block Panels0101.accepted Panels0101.integerPanels Panels0101.aligned
    Panels0101.weightRows Panels0101.weights_checked ⟨1, by decide⟩
def b0102 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0102.block Panels0102.accepted Panels0102.integerPanels Panels0102.aligned
    Panels0102.weightRows Panels0102.weights_checked ⟨1, by decide⟩
def b0103 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0103.block Panels0103.accepted Panels0103.integerPanels Panels0103.aligned
    Panels0103.weightRows Panels0103.weights_checked ⟨1, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0096, b0097, b0098, b0099, b0100, b0101, b0102, b0103]
theorem chain_checked : blockChainCheck (199782924607866098106963165277/10^30) (256518525847052817488239228851/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=6082571168490574818810559858588916081533905944747115211241512931406392314592421285330000333510540657440630696284974349511916846192085347391975985080539163634966016989960298110494647988227478145088250299190226/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row01
namespace Row02
abbrev ζ : ℚ := 153846153846153846153846153846/10^30
def b0096 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0096.block Panels0096.accepted Panels0096.integerPanels Panels0096.aligned
    Panels0096.weightRows Panels0096.weights_checked ⟨2, by decide⟩
def b0097 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0097.block Panels0097.accepted Panels0097.integerPanels Panels0097.aligned
    Panels0097.weightRows Panels0097.weights_checked ⟨2, by decide⟩
def b0098 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0098.block Panels0098.accepted Panels0098.integerPanels Panels0098.aligned
    Panels0098.weightRows Panels0098.weights_checked ⟨2, by decide⟩
def b0099 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0099.block Panels0099.accepted Panels0099.integerPanels Panels0099.aligned
    Panels0099.weightRows Panels0099.weights_checked ⟨2, by decide⟩
def b0100 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0100.block Panels0100.accepted Panels0100.integerPanels Panels0100.aligned
    Panels0100.weightRows Panels0100.weights_checked ⟨2, by decide⟩
def b0101 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0101.block Panels0101.accepted Panels0101.integerPanels Panels0101.aligned
    Panels0101.weightRows Panels0101.weights_checked ⟨2, by decide⟩
def b0102 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0102.block Panels0102.accepted Panels0102.integerPanels Panels0102.aligned
    Panels0102.weightRows Panels0102.weights_checked ⟨2, by decide⟩
def b0103 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0103.block Panels0103.accepted Panels0103.integerPanels Panels0103.aligned
    Panels0103.weightRows Panels0103.weights_checked ⟨2, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0096, b0097, b0098, b0099, b0100, b0101, b0102, b0103]
theorem chain_checked : blockChainCheck (199782924607866098106963165277/10^30) (256518525847052817488239228851/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=5779156445967402001955737795273030169030589679092478549819456242795577335564659219594690498556828343837863898374568505288386612381662413807473604811484991747012994020442648256368271807981881746600376190665885345/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row02
namespace Row03
abbrev ζ : ℚ := 117647058823529411764705882352/10^30
def b0096 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0096.block Panels0096.accepted Panels0096.integerPanels Panels0096.aligned
    Panels0096.weightRows Panels0096.weights_checked ⟨3, by decide⟩
def b0097 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0097.block Panels0097.accepted Panels0097.integerPanels Panels0097.aligned
    Panels0097.weightRows Panels0097.weights_checked ⟨3, by decide⟩
def b0098 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0098.block Panels0098.accepted Panels0098.integerPanels Panels0098.aligned
    Panels0098.weightRows Panels0098.weights_checked ⟨3, by decide⟩
def b0099 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0099.block Panels0099.accepted Panels0099.integerPanels Panels0099.aligned
    Panels0099.weightRows Panels0099.weights_checked ⟨3, by decide⟩
def b0100 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0100.block Panels0100.accepted Panels0100.integerPanels Panels0100.aligned
    Panels0100.weightRows Panels0100.weights_checked ⟨3, by decide⟩
def b0101 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0101.block Panels0101.accepted Panels0101.integerPanels Panels0101.aligned
    Panels0101.weightRows Panels0101.weights_checked ⟨3, by decide⟩
def b0102 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0102.block Panels0102.accepted Panels0102.integerPanels Panels0102.aligned
    Panels0102.weightRows Panels0102.weights_checked ⟨3, by decide⟩
def b0103 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0103.block Panels0103.accepted Panels0103.integerPanels Panels0103.aligned
    Panels0103.weightRows Panels0103.weights_checked ⟨3, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0096, b0097, b0098, b0099, b0100, b0101, b0102, b0103]
theorem chain_checked : blockChainCheck (199782924607866098106963165277/10^30) (256518525847052817488239228851/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=38019074606598331969151610656697284861873371509100720475801766819184284927121239599998536338847622735985933040823985942817269811586404302906415163940977195542440988850966772715079092150698659907166549296008858593/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row03
namespace Row04
abbrev ζ : ℚ := 86956521739130434782608695652/10^30
def b0096 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0096.block Panels0096.accepted Panels0096.integerPanels Panels0096.aligned
    Panels0096.weightRows Panels0096.weights_checked ⟨4, by decide⟩
def b0097 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0097.block Panels0097.accepted Panels0097.integerPanels Panels0097.aligned
    Panels0097.weightRows Panels0097.weights_checked ⟨4, by decide⟩
def b0098 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0098.block Panels0098.accepted Panels0098.integerPanels Panels0098.aligned
    Panels0098.weightRows Panels0098.weights_checked ⟨4, by decide⟩
def b0099 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0099.block Panels0099.accepted Panels0099.integerPanels Panels0099.aligned
    Panels0099.weightRows Panels0099.weights_checked ⟨4, by decide⟩
def b0100 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0100.block Panels0100.accepted Panels0100.integerPanels Panels0100.aligned
    Panels0100.weightRows Panels0100.weights_checked ⟨4, by decide⟩
def b0101 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0101.block Panels0101.accepted Panels0101.integerPanels Panels0101.aligned
    Panels0101.weightRows Panels0101.weights_checked ⟨4, by decide⟩
def b0102 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0102.block Panels0102.accepted Panels0102.integerPanels Panels0102.aligned
    Panels0102.weightRows Panels0102.weights_checked ⟨4, by decide⟩
def b0103 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0103.block Panels0103.accepted Panels0103.integerPanels Panels0103.aligned
    Panels0103.weightRows Panels0103.weights_checked ⟨4, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0096, b0097, b0098, b0099, b0100, b0101, b0102, b0103]
theorem chain_checked : blockChainCheck (199782924607866098106963165277/10^30) (256518525847052817488239228851/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=127526856513890675008443714338637117526963781239803479366157957059492653638872144007002719297076762193910626952221921928686482459581676910008162583873818698482591016041858378458814227967065106632009581849717610793/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row04
namespace Row05
abbrev ζ : ℚ := 64516129032258064516129032258/10^30
def b0096 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0096.block Panels0096.accepted Panels0096.integerPanels Panels0096.aligned
    Panels0096.weightRows Panels0096.weights_checked ⟨5, by decide⟩
def b0097 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0097.block Panels0097.accepted Panels0097.integerPanels Panels0097.aligned
    Panels0097.weightRows Panels0097.weights_checked ⟨5, by decide⟩
def b0098 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0098.block Panels0098.accepted Panels0098.integerPanels Panels0098.aligned
    Panels0098.weightRows Panels0098.weights_checked ⟨5, by decide⟩
def b0099 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0099.block Panels0099.accepted Panels0099.integerPanels Panels0099.aligned
    Panels0099.weightRows Panels0099.weights_checked ⟨5, by decide⟩
def b0100 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0100.block Panels0100.accepted Panels0100.integerPanels Panels0100.aligned
    Panels0100.weightRows Panels0100.weights_checked ⟨5, by decide⟩
def b0101 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0101.block Panels0101.accepted Panels0101.integerPanels Panels0101.aligned
    Panels0101.weightRows Panels0101.weights_checked ⟨5, by decide⟩
def b0102 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0102.block Panels0102.accepted Panels0102.integerPanels Panels0102.aligned
    Panels0102.weightRows Panels0102.weights_checked ⟨5, by decide⟩
def b0103 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0103.block Panels0103.accepted Panels0103.integerPanels Panels0103.aligned
    Panels0103.weightRows Panels0103.weights_checked ⟨5, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0096, b0097, b0098, b0099, b0100, b0101, b0102, b0103]
theorem chain_checked : blockChainCheck (199782924607866098106963165277/10^30) (256518525847052817488239228851/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=266644045925944169045971756839961060873646164462265923269112013156204184909967471958883968774695714123032066424286644317742393965808686732121624255311040121616975113106983589303708584127336511523734754068750473321/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row05
namespace Row06
abbrev ζ : ℚ := 46511627906976744186046511627/10^30
def b0096 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0096.block Panels0096.accepted Panels0096.integerPanels Panels0096.aligned
    Panels0096.weightRows Panels0096.weights_checked ⟨6, by decide⟩
def b0097 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0097.block Panels0097.accepted Panels0097.integerPanels Panels0097.aligned
    Panels0097.weightRows Panels0097.weights_checked ⟨6, by decide⟩
def b0098 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0098.block Panels0098.accepted Panels0098.integerPanels Panels0098.aligned
    Panels0098.weightRows Panels0098.weights_checked ⟨6, by decide⟩
def b0099 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0099.block Panels0099.accepted Panels0099.integerPanels Panels0099.aligned
    Panels0099.weightRows Panels0099.weights_checked ⟨6, by decide⟩
def b0100 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0100.block Panels0100.accepted Panels0100.integerPanels Panels0100.aligned
    Panels0100.weightRows Panels0100.weights_checked ⟨6, by decide⟩
def b0101 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0101.block Panels0101.accepted Panels0101.integerPanels Panels0101.aligned
    Panels0101.weightRows Panels0101.weights_checked ⟨6, by decide⟩
def b0102 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0102.block Panels0102.accepted Panels0102.integerPanels Panels0102.aligned
    Panels0102.weightRows Panels0102.weights_checked ⟨6, by decide⟩
def b0103 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0103.block Panels0103.accepted Panels0103.integerPanels Panels0103.aligned
    Panels0103.weightRows Panels0103.weights_checked ⟨6, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0096, b0097, b0098, b0099, b0100, b0101, b0102, b0103]
theorem chain_checked : blockChainCheck (199782924607866098106963165277/10^30) (256518525847052817488239228851/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=450570430197561412589926238587070465866992994426977500694783293308905777253985949455020945943442336839461165540877511233271224935939201781782305547357579120026623149819656200379997460461140183069101590908046853943/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row06
namespace Row07
abbrev ζ : ℚ := 33898305084745762711864406779/10^30
def b0096 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0096.block Panels0096.accepted Panels0096.integerPanels Panels0096.aligned
    Panels0096.weightRows Panels0096.weights_checked ⟨7, by decide⟩
def b0097 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0097.block Panels0097.accepted Panels0097.integerPanels Panels0097.aligned
    Panels0097.weightRows Panels0097.weights_checked ⟨7, by decide⟩
def b0098 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0098.block Panels0098.accepted Panels0098.integerPanels Panels0098.aligned
    Panels0098.weightRows Panels0098.weights_checked ⟨7, by decide⟩
def b0099 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0099.block Panels0099.accepted Panels0099.integerPanels Panels0099.aligned
    Panels0099.weightRows Panels0099.weights_checked ⟨7, by decide⟩
def b0100 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0100.block Panels0100.accepted Panels0100.integerPanels Panels0100.aligned
    Panels0100.weightRows Panels0100.weights_checked ⟨7, by decide⟩
def b0101 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0101.block Panels0101.accepted Panels0101.integerPanels Panels0101.aligned
    Panels0101.weightRows Panels0101.weights_checked ⟨7, by decide⟩
def b0102 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0102.block Panels0102.accepted Panels0102.integerPanels Panels0102.aligned
    Panels0102.weightRows Panels0102.weights_checked ⟨7, by decide⟩
def b0103 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0103.block Panels0103.accepted Panels0103.integerPanels Panels0103.aligned
    Panels0103.weightRows Panels0103.weights_checked ⟨7, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0096, b0097, b0098, b0099, b0100, b0101, b0102, b0103]
theorem chain_checked : blockChainCheck (199782924607866098106963165277/10^30) (256518525847052817488239228851/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=631894815315998648403670093700852094674980783942050767567624317733405538405648556438801195427261792793526654828699053279711002513934443362393499020662544440323775404700378753140956112620483866350079793862720088279/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row07
namespace Row08
abbrev ζ : ℚ := 25316455696202531645569620253/10^30
def b0096 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0096.block Panels0096.accepted Panels0096.integerPanels Panels0096.aligned
    Panels0096.weightRows Panels0096.weights_checked ⟨8, by decide⟩
def b0097 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0097.block Panels0097.accepted Panels0097.integerPanels Panels0097.aligned
    Panels0097.weightRows Panels0097.weights_checked ⟨8, by decide⟩
def b0098 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0098.block Panels0098.accepted Panels0098.integerPanels Panels0098.aligned
    Panels0098.weightRows Panels0098.weights_checked ⟨8, by decide⟩
def b0099 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0099.block Panels0099.accepted Panels0099.integerPanels Panels0099.aligned
    Panels0099.weightRows Panels0099.weights_checked ⟨8, by decide⟩
def b0100 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0100.block Panels0100.accepted Panels0100.integerPanels Panels0100.aligned
    Panels0100.weightRows Panels0100.weights_checked ⟨8, by decide⟩
def b0101 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0101.block Panels0101.accepted Panels0101.integerPanels Panels0101.aligned
    Panels0101.weightRows Panels0101.weights_checked ⟨8, by decide⟩
def b0102 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0102.block Panels0102.accepted Panels0102.integerPanels Panels0102.aligned
    Panels0102.weightRows Panels0102.weights_checked ⟨8, by decide⟩
def b0103 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0103.block Panels0103.accepted Panels0103.integerPanels Panels0103.aligned
    Panels0103.weightRows Panels0103.weights_checked ⟨8, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0096, b0097, b0098, b0099, b0100, b0101, b0102, b0103]
theorem chain_checked : blockChainCheck (199782924607866098106963165277/10^30) (256518525847052817488239228851/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=785846252703437348675953642557856149831037892163101672479688181060617215600974614859840687081423366212824785403763209101055441619504125785967751135387502186303046235082835513078083545005573557924758040560094197751/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row08
namespace Row09
abbrev ζ : ℚ := 18691588785046728971962616822/10^30
def b0096 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0096.block Panels0096.accepted Panels0096.integerPanels Panels0096.aligned
    Panels0096.weightRows Panels0096.weights_checked ⟨9, by decide⟩
def b0097 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0097.block Panels0097.accepted Panels0097.integerPanels Panels0097.aligned
    Panels0097.weightRows Panels0097.weights_checked ⟨9, by decide⟩
def b0098 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0098.block Panels0098.accepted Panels0098.integerPanels Panels0098.aligned
    Panels0098.weightRows Panels0098.weights_checked ⟨9, by decide⟩
def b0099 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0099.block Panels0099.accepted Panels0099.integerPanels Panels0099.aligned
    Panels0099.weightRows Panels0099.weights_checked ⟨9, by decide⟩
def b0100 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0100.block Panels0100.accepted Panels0100.integerPanels Panels0100.aligned
    Panels0100.weightRows Panels0100.weights_checked ⟨9, by decide⟩
def b0101 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0101.block Panels0101.accepted Panels0101.integerPanels Panels0101.aligned
    Panels0101.weightRows Panels0101.weights_checked ⟨9, by decide⟩
def b0102 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0102.block Panels0102.accepted Panels0102.integerPanels Panels0102.aligned
    Panels0102.weightRows Panels0102.weights_checked ⟨9, by decide⟩
def b0103 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0103.block Panels0103.accepted Panels0103.integerPanels Panels0103.aligned
    Panels0103.weightRows Panels0103.weights_checked ⟨9, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0096, b0097, b0098, b0099, b0100, b0101, b0102, b0103]
theorem chain_checked : blockChainCheck (199782924607866098106963165277/10^30) (256518525847052817488239228851/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=924236589164239410087382342951587342391842565690331169612282452673794294049094070228658976397287722522221210893368889796954912073691020457005827569996476122675200290658964792415304366096781820365400700307614151073/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row09
namespace Row10
abbrev ζ : ℚ := 13793103448275862068965517241/10^30
def b0096 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0096.block Panels0096.accepted Panels0096.integerPanels Panels0096.aligned
    Panels0096.weightRows Panels0096.weights_checked ⟨10, by decide⟩
def b0097 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0097.block Panels0097.accepted Panels0097.integerPanels Panels0097.aligned
    Panels0097.weightRows Panels0097.weights_checked ⟨10, by decide⟩
def b0098 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0098.block Panels0098.accepted Panels0098.integerPanels Panels0098.aligned
    Panels0098.weightRows Panels0098.weights_checked ⟨10, by decide⟩
def b0099 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0099.block Panels0099.accepted Panels0099.integerPanels Panels0099.aligned
    Panels0099.weightRows Panels0099.weights_checked ⟨10, by decide⟩
def b0100 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0100.block Panels0100.accepted Panels0100.integerPanels Panels0100.aligned
    Panels0100.weightRows Panels0100.weights_checked ⟨10, by decide⟩
def b0101 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0101.block Panels0101.accepted Panels0101.integerPanels Panels0101.aligned
    Panels0101.weightRows Panels0101.weights_checked ⟨10, by decide⟩
def b0102 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0102.block Panels0102.accepted Panels0102.integerPanels Panels0102.aligned
    Panels0102.weightRows Panels0102.weights_checked ⟨10, by decide⟩
def b0103 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0103.block Panels0103.accepted Panels0103.integerPanels Panels0103.aligned
    Panels0103.weightRows Panels0103.weights_checked ⟨10, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0096, b0097, b0098, b0099, b0100, b0101, b0102, b0103]
theorem chain_checked : blockChainCheck (199782924607866098106963165277/10^30) (256518525847052817488239228851/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=1038662977842341738382459222871705632718789609876056682850315876590377594801750759857850910319885764068329000965357977479985822321336991456868280946145317940662113031408434410979867056535773499747838448729525308575/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row10
namespace Row11
abbrev ζ : ℚ := 10152284263959390862944162436/10^30
def b0096 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0096.block Panels0096.accepted Panels0096.integerPanels Panels0096.aligned
    Panels0096.weightRows Panels0096.weights_checked ⟨11, by decide⟩
def b0097 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0097.block Panels0097.accepted Panels0097.integerPanels Panels0097.aligned
    Panels0097.weightRows Panels0097.weights_checked ⟨11, by decide⟩
def b0098 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0098.block Panels0098.accepted Panels0098.integerPanels Panels0098.aligned
    Panels0098.weightRows Panels0098.weights_checked ⟨11, by decide⟩
def b0099 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0099.block Panels0099.accepted Panels0099.integerPanels Panels0099.aligned
    Panels0099.weightRows Panels0099.weights_checked ⟨11, by decide⟩
def b0100 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0100.block Panels0100.accepted Panels0100.integerPanels Panels0100.aligned
    Panels0100.weightRows Panels0100.weights_checked ⟨11, by decide⟩
def b0101 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0101.block Panels0101.accepted Panels0101.integerPanels Panels0101.aligned
    Panels0101.weightRows Panels0101.weights_checked ⟨11, by decide⟩
def b0102 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0102.block Panels0102.accepted Panels0102.integerPanels Panels0102.aligned
    Panels0102.weightRows Panels0102.weights_checked ⟨11, by decide⟩
def b0103 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0103.block Panels0103.accepted Panels0103.integerPanels Panels0103.aligned
    Panels0103.weightRows Panels0103.weights_checked ⟨11, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0096, b0097, b0098, b0099, b0100, b0101, b0102, b0103]
theorem chain_checked : blockChainCheck (199782924607866098106963165277/10^30) (256518525847052817488239228851/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=1130880526153641710641271322365464104503960064679433668051976182009403813942230999059973410323464681854242187620681121680134569200771614898547484402453703852986859960247889748057137803756999463495283652745571990505/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row11
namespace Row12
abbrev ζ : ℚ := 9950248756218905472636815920/10^30
def b0096 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0096.block Panels0096.accepted Panels0096.integerPanels Panels0096.aligned
    Panels0096.weightRows Panels0096.weights_checked ⟨12, by decide⟩
def b0097 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0097.block Panels0097.accepted Panels0097.integerPanels Panels0097.aligned
    Panels0097.weightRows Panels0097.weights_checked ⟨12, by decide⟩
def b0098 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0098.block Panels0098.accepted Panels0098.integerPanels Panels0098.aligned
    Panels0098.weightRows Panels0098.weights_checked ⟨12, by decide⟩
def b0099 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0099.block Panels0099.accepted Panels0099.integerPanels Panels0099.aligned
    Panels0099.weightRows Panels0099.weights_checked ⟨12, by decide⟩
def b0100 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0100.block Panels0100.accepted Panels0100.integerPanels Panels0100.aligned
    Panels0100.weightRows Panels0100.weights_checked ⟨12, by decide⟩
def b0101 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0101.block Panels0101.accepted Panels0101.integerPanels Panels0101.aligned
    Panels0101.weightRows Panels0101.weights_checked ⟨12, by decide⟩
def b0102 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0102.block Panels0102.accepted Panels0102.integerPanels Panels0102.aligned
    Panels0102.weightRows Panels0102.weights_checked ⟨12, by decide⟩
def b0103 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0103.block Panels0103.accepted Panels0103.integerPanels Panels0103.aligned
    Panels0103.weightRows Panels0103.weights_checked ⟨12, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0096, b0097, b0098, b0099, b0100, b0101, b0102, b0103]
theorem chain_checked : blockChainCheck (199782924607866098106963165277/10^30) (256518525847052817488239228851/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=1136184436612593174367628751392654285977785544650571827544358774965367126757098711345817136320118223229294025248534897920421831832224563784096455926924458930431067754648907163755929082558309595892004076297468765537/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row12
#print axioms Row12.segment
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments012
