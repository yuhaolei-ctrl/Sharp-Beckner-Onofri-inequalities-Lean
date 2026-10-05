import BecknerOnofri.EntropyHeatCheckedWeights
import BecknerOnofri.EntropyHeatSegments
import BecknerOnofri.EntropyHeatCertificate.Panels0176
import BecknerOnofri.EntropyHeatCertificate.Panels0177
import BecknerOnofri.EntropyHeatCertificate.Panels0178
import BecknerOnofri.EntropyHeatCertificate.Panels0179
import BecknerOnofri.EntropyHeatCertificate.Panels0180
import BecknerOnofri.EntropyHeatCertificate.Panels0181
import BecknerOnofri.EntropyHeatCertificate.Panels0182
import BecknerOnofri.EntropyHeatCertificate.Panels0183
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments022
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace Row00
abbrev ζ : ℚ := 285714285714285714285714285714/10^30
def b0176 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0176.block Panels0176.accepted Panels0176.integerPanels Panels0176.aligned
    Panels0176.weightRows Panels0176.weights_checked ⟨0, by decide⟩
def b0177 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0177.block Panels0177.accepted Panels0177.integerPanels Panels0177.aligned
    Panels0177.weightRows Panels0177.weights_checked ⟨0, by decide⟩
def b0178 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0178.block Panels0178.accepted Panels0178.integerPanels Panels0178.aligned
    Panels0178.weightRows Panels0178.weights_checked ⟨0, by decide⟩
def b0179 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0179.block Panels0179.accepted Panels0179.integerPanels Panels0179.aligned
    Panels0179.weightRows Panels0179.weights_checked ⟨0, by decide⟩
def b0180 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0180.block Panels0180.accepted Panels0180.integerPanels Panels0180.aligned
    Panels0180.weightRows Panels0180.weights_checked ⟨0, by decide⟩
def b0181 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0181.block Panels0181.accepted Panels0181.integerPanels Panels0181.aligned
    Panels0181.weightRows Panels0181.weights_checked ⟨0, by decide⟩
def b0182 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0182.block Panels0182.accepted Panels0182.integerPanels Panels0182.aligned
    Panels0182.weightRows Panels0182.weights_checked ⟨0, by decide⟩
def b0183 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0183.block Panels0183.accepted Panels0183.integerPanels Panels0183.aligned
    Panels0183.weightRows Panels0183.weights_checked ⟨0, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0176, b0177, b0178, b0179, b0180, b0181, b0182, b0183]
theorem chain_checked : blockChainCheck (2433111753263434836465548498036/10^30) (3124082007475528121207110426578/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=635725643698575199932465249581361299862830148554895403889280556194273464933161312358164053824112359868697629340758274611912701087863381954294867503719845682845114336077576927329841704667447060677557951924241285/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row00
namespace Row01
abbrev ζ : ℚ := 222222222222222222222222222222/10^30
def b0176 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0176.block Panels0176.accepted Panels0176.integerPanels Panels0176.aligned
    Panels0176.weightRows Panels0176.weights_checked ⟨1, by decide⟩
def b0177 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0177.block Panels0177.accepted Panels0177.integerPanels Panels0177.aligned
    Panels0177.weightRows Panels0177.weights_checked ⟨1, by decide⟩
def b0178 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0178.block Panels0178.accepted Panels0178.integerPanels Panels0178.aligned
    Panels0178.weightRows Panels0178.weights_checked ⟨1, by decide⟩
def b0179 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0179.block Panels0179.accepted Panels0179.integerPanels Panels0179.aligned
    Panels0179.weightRows Panels0179.weights_checked ⟨1, by decide⟩
def b0180 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0180.block Panels0180.accepted Panels0180.integerPanels Panels0180.aligned
    Panels0180.weightRows Panels0180.weights_checked ⟨1, by decide⟩
def b0181 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0181.block Panels0181.accepted Panels0181.integerPanels Panels0181.aligned
    Panels0181.weightRows Panels0181.weights_checked ⟨1, by decide⟩
def b0182 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0182.block Panels0182.accepted Panels0182.integerPanels Panels0182.aligned
    Panels0182.weightRows Panels0182.weights_checked ⟨1, by decide⟩
def b0183 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0183.block Panels0183.accepted Panels0183.integerPanels Panels0183.aligned
    Panels0183.weightRows Panels0183.weights_checked ⟨1, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0176, b0177, b0178, b0179, b0180, b0181, b0182, b0183]
theorem chain_checked : blockChainCheck (2433111753263434836465548498036/10^30) (3124082007475528121207110426578/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=725941441988535671212225467386214133301780790558448417455249779752345589446378615756138918296656184916066978155783444355103211235391714323279888267406017954313192784817222768341052559877554184268551227008395149/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row01
namespace Row02
abbrev ζ : ℚ := 153846153846153846153846153846/10^30
def b0176 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0176.block Panels0176.accepted Panels0176.integerPanels Panels0176.aligned
    Panels0176.weightRows Panels0176.weights_checked ⟨2, by decide⟩
def b0177 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0177.block Panels0177.accepted Panels0177.integerPanels Panels0177.aligned
    Panels0177.weightRows Panels0177.weights_checked ⟨2, by decide⟩
def b0178 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0178.block Panels0178.accepted Panels0178.integerPanels Panels0178.aligned
    Panels0178.weightRows Panels0178.weights_checked ⟨2, by decide⟩
def b0179 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0179.block Panels0179.accepted Panels0179.integerPanels Panels0179.aligned
    Panels0179.weightRows Panels0179.weights_checked ⟨2, by decide⟩
def b0180 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0180.block Panels0180.accepted Panels0180.integerPanels Panels0180.aligned
    Panels0180.weightRows Panels0180.weights_checked ⟨2, by decide⟩
def b0181 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0181.block Panels0181.accepted Panels0181.integerPanels Panels0181.aligned
    Panels0181.weightRows Panels0181.weights_checked ⟨2, by decide⟩
def b0182 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0182.block Panels0182.accepted Panels0182.integerPanels Panels0182.aligned
    Panels0182.weightRows Panels0182.weights_checked ⟨2, by decide⟩
def b0183 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0183.block Panels0183.accepted Panels0183.integerPanels Panels0183.aligned
    Panels0183.weightRows Panels0183.weights_checked ⟨2, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0176, b0177, b0178, b0179, b0180, b0181, b0182, b0183]
theorem chain_checked : blockChainCheck (2433111753263434836465548498036/10^30) (3124082007475528121207110426578/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=834322013291769493058191799086842464597080434899260735032930160172119200422848426341603088581834363524764505961589892261677671481163006068852702779116321492044759743893645131843821510338988792696338187923789981/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row02
namespace Row03
abbrev ζ : ℚ := 117647058823529411764705882352/10^30
def b0176 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0176.block Panels0176.accepted Panels0176.integerPanels Panels0176.aligned
    Panels0176.weightRows Panels0176.weights_checked ⟨3, by decide⟩
def b0177 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0177.block Panels0177.accepted Panels0177.integerPanels Panels0177.aligned
    Panels0177.weightRows Panels0177.weights_checked ⟨3, by decide⟩
def b0178 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0178.block Panels0178.accepted Panels0178.integerPanels Panels0178.aligned
    Panels0178.weightRows Panels0178.weights_checked ⟨3, by decide⟩
def b0179 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0179.block Panels0179.accepted Panels0179.integerPanels Panels0179.aligned
    Panels0179.weightRows Panels0179.weights_checked ⟨3, by decide⟩
def b0180 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0180.block Panels0180.accepted Panels0180.integerPanels Panels0180.aligned
    Panels0180.weightRows Panels0180.weights_checked ⟨3, by decide⟩
def b0181 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0181.block Panels0181.accepted Panels0181.integerPanels Panels0181.aligned
    Panels0181.weightRows Panels0181.weights_checked ⟨3, by decide⟩
def b0182 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0182.block Panels0182.accepted Panels0182.integerPanels Panels0182.aligned
    Panels0182.weightRows Panels0182.weights_checked ⟨3, by decide⟩
def b0183 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0183.block Panels0183.accepted Panels0183.integerPanels Panels0183.aligned
    Panels0183.weightRows Panels0183.weights_checked ⟨3, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0176, b0177, b0178, b0179, b0180, b0181, b0182, b0183]
theorem chain_checked : blockChainCheck (2433111753263434836465548498036/10^30) (3124082007475528121207110426578/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=896749423977049160304833164947896525544487018312817389812920180350932577726033380901918566093474627915338121928189511151141037334456785680191888915825028666704377910163115818311364689518651134181765318492077869/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row03
namespace Row04
abbrev ζ : ℚ := 86956521739130434782608695652/10^30
def b0176 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0176.block Panels0176.accepted Panels0176.integerPanels Panels0176.aligned
    Panels0176.weightRows Panels0176.weights_checked ⟨4, by decide⟩
def b0177 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0177.block Panels0177.accepted Panels0177.integerPanels Panels0177.aligned
    Panels0177.weightRows Panels0177.weights_checked ⟨4, by decide⟩
def b0178 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0178.block Panels0178.accepted Panels0178.integerPanels Panels0178.aligned
    Panels0178.weightRows Panels0178.weights_checked ⟨4, by decide⟩
def b0179 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0179.block Panels0179.accepted Panels0179.integerPanels Panels0179.aligned
    Panels0179.weightRows Panels0179.weights_checked ⟨4, by decide⟩
def b0180 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0180.block Panels0180.accepted Panels0180.integerPanels Panels0180.aligned
    Panels0180.weightRows Panels0180.weights_checked ⟨4, by decide⟩
def b0181 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0181.block Panels0181.accepted Panels0181.integerPanels Panels0181.aligned
    Panels0181.weightRows Panels0181.weights_checked ⟨4, by decide⟩
def b0182 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0182.block Panels0182.accepted Panels0182.integerPanels Panels0182.aligned
    Panels0182.weightRows Panels0182.weights_checked ⟨4, by decide⟩
def b0183 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0183.block Panels0183.accepted Panels0183.integerPanels Panels0183.aligned
    Panels0183.weightRows Panels0183.weights_checked ⟨4, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0176, b0177, b0178, b0179, b0180, b0181, b0182, b0183]
theorem chain_checked : blockChainCheck (2433111753263434836465548498036/10^30) (3124082007475528121207110426578/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=952568381708296944664677307125250963352764963759034378141677086497437619379922400453827932166284666028703863338648155056998792914280747157995344463825125282104243935413260020569069875307815668002646294163718069/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row04
namespace Row05
abbrev ζ : ℚ := 64516129032258064516129032258/10^30
def b0176 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0176.block Panels0176.accepted Panels0176.integerPanels Panels0176.aligned
    Panels0176.weightRows Panels0176.weights_checked ⟨5, by decide⟩
def b0177 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0177.block Panels0177.accepted Panels0177.integerPanels Panels0177.aligned
    Panels0177.weightRows Panels0177.weights_checked ⟨5, by decide⟩
def b0178 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0178.block Panels0178.accepted Panels0178.integerPanels Panels0178.aligned
    Panels0178.weightRows Panels0178.weights_checked ⟨5, by decide⟩
def b0179 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0179.block Panels0179.accepted Panels0179.integerPanels Panels0179.aligned
    Panels0179.weightRows Panels0179.weights_checked ⟨5, by decide⟩
def b0180 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0180.block Panels0180.accepted Panels0180.integerPanels Panels0180.aligned
    Panels0180.weightRows Panels0180.weights_checked ⟨5, by decide⟩
def b0181 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0181.block Panels0181.accepted Panels0181.integerPanels Panels0181.aligned
    Panels0181.weightRows Panels0181.weights_checked ⟨5, by decide⟩
def b0182 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0182.block Panels0182.accepted Panels0182.integerPanels Panels0182.aligned
    Panels0182.weightRows Panels0182.weights_checked ⟨5, by decide⟩
def b0183 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0183.block Panels0183.accepted Panels0183.integerPanels Panels0183.aligned
    Panels0183.weightRows Panels0183.weights_checked ⟨5, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0176, b0177, b0178, b0179, b0180, b0181, b0182, b0183]
theorem chain_checked : blockChainCheck (2433111753263434836465548498036/10^30) (3124082007475528121207110426578/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=995122101046435245510981791827848578288070921907621757109875145470453513133061214175047575360737301669159469133810637258807355466351950721063605594855865226614734912251871559267998933100667786126879810474189157/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row05
namespace Row06
abbrev ζ : ℚ := 46511627906976744186046511627/10^30
def b0176 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0176.block Panels0176.accepted Panels0176.integerPanels Panels0176.aligned
    Panels0176.weightRows Panels0176.weights_checked ⟨6, by decide⟩
def b0177 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0177.block Panels0177.accepted Panels0177.integerPanels Panels0177.aligned
    Panels0177.weightRows Panels0177.weights_checked ⟨6, by decide⟩
def b0178 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0178.block Panels0178.accepted Panels0178.integerPanels Panels0178.aligned
    Panels0178.weightRows Panels0178.weights_checked ⟨6, by decide⟩
def b0179 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0179.block Panels0179.accepted Panels0179.integerPanels Panels0179.aligned
    Panels0179.weightRows Panels0179.weights_checked ⟨6, by decide⟩
def b0180 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0180.block Panels0180.accepted Panels0180.integerPanels Panels0180.aligned
    Panels0180.weightRows Panels0180.weights_checked ⟨6, by decide⟩
def b0181 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0181.block Panels0181.accepted Panels0181.integerPanels Panels0181.aligned
    Panels0181.weightRows Panels0181.weights_checked ⟨6, by decide⟩
def b0182 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0182.block Panels0182.accepted Panels0182.integerPanels Panels0182.aligned
    Panels0182.weightRows Panels0182.weights_checked ⟨6, by decide⟩
def b0183 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0183.block Panels0183.accepted Panels0183.integerPanels Panels0183.aligned
    Panels0183.weightRows Panels0183.weights_checked ⟨6, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0176, b0177, b0178, b0179, b0180, b0181, b0182, b0183]
theorem chain_checked : blockChainCheck (2433111753263434836465548498036/10^30) (3124082007475528121207110426578/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=1030356770681934382648037403279044468465349549810486301626563567911912077472875173463657569835744906308977363078424397188461710880980327192472036742004378928028673260468695228843076539054337762641378180363712219/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row06
namespace Row07
abbrev ζ : ℚ := 33898305084745762711864406779/10^30
def b0176 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0176.block Panels0176.accepted Panels0176.integerPanels Panels0176.aligned
    Panels0176.weightRows Panels0176.weights_checked ⟨7, by decide⟩
def b0177 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0177.block Panels0177.accepted Panels0177.integerPanels Panels0177.aligned
    Panels0177.weightRows Panels0177.weights_checked ⟨7, by decide⟩
def b0178 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0178.block Panels0178.accepted Panels0178.integerPanels Panels0178.aligned
    Panels0178.weightRows Panels0178.weights_checked ⟨7, by decide⟩
def b0179 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0179.block Panels0179.accepted Panels0179.integerPanels Panels0179.aligned
    Panels0179.weightRows Panels0179.weights_checked ⟨7, by decide⟩
def b0180 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0180.block Panels0180.accepted Panels0180.integerPanels Panels0180.aligned
    Panels0180.weightRows Panels0180.weights_checked ⟨7, by decide⟩
def b0181 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0181.block Panels0181.accepted Panels0181.integerPanels Panels0181.aligned
    Panels0181.weightRows Panels0181.weights_checked ⟨7, by decide⟩
def b0182 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0182.block Panels0182.accepted Panels0182.integerPanels Panels0182.aligned
    Panels0182.weightRows Panels0182.weights_checked ⟨7, by decide⟩
def b0183 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0183.block Panels0183.accepted Panels0183.integerPanels Panels0183.aligned
    Panels0183.weightRows Panels0183.weights_checked ⟨7, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0176, b0177, b0178, b0179, b0180, b0181, b0182, b0183]
theorem chain_checked : blockChainCheck (2433111753263434836465548498036/10^30) (3124082007475528121207110426578/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=1055632578162710510983154509497930744934914806749810012097504685550584567506994707822920048001382577417519696658641736590707529861526702831338195245575753311520989018789916366922826488710473148564625904646430395/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row07
namespace Row08
abbrev ζ : ℚ := 25316455696202531645569620253/10^30
def b0176 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0176.block Panels0176.accepted Panels0176.integerPanels Panels0176.aligned
    Panels0176.weightRows Panels0176.weights_checked ⟨8, by decide⟩
def b0177 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0177.block Panels0177.accepted Panels0177.integerPanels Panels0177.aligned
    Panels0177.weightRows Panels0177.weights_checked ⟨8, by decide⟩
def b0178 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0178.block Panels0178.accepted Panels0178.integerPanels Panels0178.aligned
    Panels0178.weightRows Panels0178.weights_checked ⟨8, by decide⟩
def b0179 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0179.block Panels0179.accepted Panels0179.integerPanels Panels0179.aligned
    Panels0179.weightRows Panels0179.weights_checked ⟨8, by decide⟩
def b0180 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0180.block Panels0180.accepted Panels0180.integerPanels Panels0180.aligned
    Panels0180.weightRows Panels0180.weights_checked ⟨8, by decide⟩
def b0181 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0181.block Panels0181.accepted Panels0181.integerPanels Panels0181.aligned
    Panels0181.weightRows Panels0181.weights_checked ⟨8, by decide⟩
def b0182 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0182.block Panels0182.accepted Panels0182.integerPanels Panels0182.aligned
    Panels0182.weightRows Panels0182.weights_checked ⟨8, by decide⟩
def b0183 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0183.block Panels0183.accepted Panels0183.integerPanels Panels0183.aligned
    Panels0183.weightRows Panels0183.weights_checked ⟨8, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0176, b0177, b0178, b0179, b0180, b0181, b0182, b0183]
theorem chain_checked : blockChainCheck (2433111753263434836465548498036/10^30) (3124082007475528121207110426578/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=1073112643623360040421652933011214743368017821924591091392681258213100923944320616469103228845927223428012968095930997188715921819405069029153935005157034294095764588044311743128973262695775156737442056932533987/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row08
namespace Row09
abbrev ζ : ℚ := 18691588785046728971962616822/10^30
def b0176 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0176.block Panels0176.accepted Panels0176.integerPanels Panels0176.aligned
    Panels0176.weightRows Panels0176.weights_checked ⟨9, by decide⟩
def b0177 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0177.block Panels0177.accepted Panels0177.integerPanels Panels0177.aligned
    Panels0177.weightRows Panels0177.weights_checked ⟨9, by decide⟩
def b0178 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0178.block Panels0178.accepted Panels0178.integerPanels Panels0178.aligned
    Panels0178.weightRows Panels0178.weights_checked ⟨9, by decide⟩
def b0179 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0179.block Panels0179.accepted Panels0179.integerPanels Panels0179.aligned
    Panels0179.weightRows Panels0179.weights_checked ⟨9, by decide⟩
def b0180 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0180.block Panels0180.accepted Panels0180.integerPanels Panels0180.aligned
    Panels0180.weightRows Panels0180.weights_checked ⟨9, by decide⟩
def b0181 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0181.block Panels0181.accepted Panels0181.integerPanels Panels0181.aligned
    Panels0181.weightRows Panels0181.weights_checked ⟨9, by decide⟩
def b0182 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0182.block Panels0182.accepted Panels0182.integerPanels Panels0182.aligned
    Panels0182.weightRows Panels0182.weights_checked ⟨9, by decide⟩
def b0183 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0183.block Panels0183.accepted Panels0183.integerPanels Panels0183.aligned
    Panels0183.weightRows Panels0183.weights_checked ⟨9, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0176, b0177, b0178, b0179, b0180, b0181, b0182, b0183]
theorem chain_checked : blockChainCheck (2433111753263434836465548498036/10^30) (3124082007475528121207110426578/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=1086764986640548853344386208381753413847948255655256074373099778471441483206155153905080133695088926700330617594880849762092929936577230485824698783814990978151086947266878257136357370276768266832735135078427549/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row09
namespace Row10
abbrev ζ : ℚ := 13793103448275862068965517241/10^30
def b0176 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0176.block Panels0176.accepted Panels0176.integerPanels Panels0176.aligned
    Panels0176.weightRows Panels0176.weights_checked ⟨10, by decide⟩
def b0177 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0177.block Panels0177.accepted Panels0177.integerPanels Panels0177.aligned
    Panels0177.weightRows Panels0177.weights_checked ⟨10, by decide⟩
def b0178 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0178.block Panels0178.accepted Panels0178.integerPanels Panels0178.aligned
    Panels0178.weightRows Panels0178.weights_checked ⟨10, by decide⟩
def b0179 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0179.block Panels0179.accepted Panels0179.integerPanels Panels0179.aligned
    Panels0179.weightRows Panels0179.weights_checked ⟨10, by decide⟩
def b0180 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0180.block Panels0180.accepted Panels0180.integerPanels Panels0180.aligned
    Panels0180.weightRows Panels0180.weights_checked ⟨10, by decide⟩
def b0181 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0181.block Panels0181.accepted Panels0181.integerPanels Panels0181.aligned
    Panels0181.weightRows Panels0181.weights_checked ⟨10, by decide⟩
def b0182 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0182.block Panels0182.accepted Panels0182.integerPanels Panels0182.aligned
    Panels0182.weightRows Panels0182.weights_checked ⟨10, by decide⟩
def b0183 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0183.block Panels0183.accepted Panels0183.integerPanels Panels0183.aligned
    Panels0183.weightRows Panels0183.weights_checked ⟨10, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0176, b0177, b0178, b0179, b0180, b0181, b0182, b0183]
theorem chain_checked : blockChainCheck (2433111753263434836465548498036/10^30) (3124082007475528121207110426578/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=1096949084318137019819534018359075518122851314661414598556912203469117632471537045219388380866021096187479688574991992015363771015489664324060047579993675264661679026855636677558050746098359230626756799893027611/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row10
namespace Row11
abbrev ζ : ℚ := 10152284263959390862944162436/10^30
def b0176 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0176.block Panels0176.accepted Panels0176.integerPanels Panels0176.aligned
    Panels0176.weightRows Panels0176.weights_checked ⟨11, by decide⟩
def b0177 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0177.block Panels0177.accepted Panels0177.integerPanels Panels0177.aligned
    Panels0177.weightRows Panels0177.weights_checked ⟨11, by decide⟩
def b0178 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0178.block Panels0178.accepted Panels0178.integerPanels Panels0178.aligned
    Panels0178.weightRows Panels0178.weights_checked ⟨11, by decide⟩
def b0179 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0179.block Panels0179.accepted Panels0179.integerPanels Panels0179.aligned
    Panels0179.weightRows Panels0179.weights_checked ⟨11, by decide⟩
def b0180 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0180.block Panels0180.accepted Panels0180.integerPanels Panels0180.aligned
    Panels0180.weightRows Panels0180.weights_checked ⟨11, by decide⟩
def b0181 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0181.block Panels0181.accepted Panels0181.integerPanels Panels0181.aligned
    Panels0181.weightRows Panels0181.weights_checked ⟨11, by decide⟩
def b0182 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0182.block Panels0182.accepted Panels0182.integerPanels Panels0182.aligned
    Panels0182.weightRows Panels0182.weights_checked ⟨11, by decide⟩
def b0183 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0183.block Panels0183.accepted Panels0183.integerPanels Panels0183.aligned
    Panels0183.weightRows Panels0183.weights_checked ⟨11, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0176, b0177, b0178, b0179, b0180, b0181, b0182, b0183]
theorem chain_checked : blockChainCheck (2433111753263434836465548498036/10^30) (3124082007475528121207110426578/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=1104568002848826705164580857589030653086944936390228496675799444433542490609044340231539294122639447250827994223494370837686159570148145610522220935242253621022967999318795263814204168209846059082077281348749941/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row11
namespace Row12
abbrev ζ : ℚ := 9950248756218905472636815920/10^30
def b0176 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0176.block Panels0176.accepted Panels0176.integerPanels Panels0176.aligned
    Panels0176.weightRows Panels0176.weights_checked ⟨12, by decide⟩
def b0177 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0177.block Panels0177.accepted Panels0177.integerPanels Panels0177.aligned
    Panels0177.weightRows Panels0177.weights_checked ⟨12, by decide⟩
def b0178 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0178.block Panels0178.accepted Panels0178.integerPanels Panels0178.aligned
    Panels0178.weightRows Panels0178.weights_checked ⟨12, by decide⟩
def b0179 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0179.block Panels0179.accepted Panels0179.integerPanels Panels0179.aligned
    Panels0179.weightRows Panels0179.weights_checked ⟨12, by decide⟩
def b0180 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0180.block Panels0180.accepted Panels0180.integerPanels Panels0180.aligned
    Panels0180.weightRows Panels0180.weights_checked ⟨12, by decide⟩
def b0181 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0181.block Panels0181.accepted Panels0181.integerPanels Panels0181.aligned
    Panels0181.weightRows Panels0181.weights_checked ⟨12, by decide⟩
def b0182 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0182.block Panels0182.accepted Panels0182.integerPanels Panels0182.aligned
    Panels0182.weightRows Panels0182.weights_checked ⟨12, by decide⟩
def b0183 : WeightedPanelBlock ζ :=
  weightedBlockOfRows Panels0183.block Panels0183.accepted Panels0183.integerPanels Panels0183.aligned
    Panels0183.weightRows Panels0183.weights_checked ⟨12, by decide⟩
def blocks : List (WeightedPanelBlock ζ) := [b0176, b0177, b0178, b0179, b0180, b0181, b0182, b0183]
theorem chain_checked : blockChainCheck (2433111753263434836465548498036/10^30) (3124082007475528121207110426578/10^30)
    (blocks.map WeightedPanelBlock.certificate)=true := by decide +kernel
theorem weight_checked : weightedTotal blocks=1104992031582667372618722753471826164221013182926473099538414096353069286009826858110532796869958466893496794815791940584759943316274024760274185791095940507115641144659554415858286947368681481641400427709092013/(720*10^210) := by decide +kernel
def segment : WeightedSegment ζ := segmentOfBlocks blocks chain_checked (by norm_num) weight_checked
end Row12
#print axioms Row12.segment
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Segments022
