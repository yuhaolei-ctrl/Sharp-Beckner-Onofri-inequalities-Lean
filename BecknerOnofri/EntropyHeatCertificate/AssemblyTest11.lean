import BecknerOnofri.EntropyHeatCheckedWeights
import BecknerOnofri.EntropyTailRowAssembly
import BecknerOnofri.EntropyHeatCertificate.Panels0000
import BecknerOnofri.EntropyHeatCertificate.Panels0001
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.AssemblyTest11
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
def blocks : List (WeightedPanelBlock (10152284263959390862944162436/10^30)) := [
  weightedBlockOfRows Panels0000.block Panels0000.accepted Panels0000.integerPanels Panels0000.aligned
    Panels0000.weightRows Panels0000.weights_checked ⟨11, by decide⟩,
  weightedBlockOfRows Panels0001.block Panels0001.accepted Panels0001.integerPanels Panels0001.aligned
    Panels0001.weightRows Panels0001.weights_checked ⟨11, by decide⟩
]
theorem chain_checked : blockChainCheck (9950248756218905472636815920/10^30) (10591903868877960435253721855/10^30)
    (blocks.map WeightedPanelBlock.certificate) = true := by decide +kernel
theorem weight_checked : weightedTotal blocks = 5100132280370253562603549824039749740836573046466816791700472832308222562062275626641983527246371883967989028208101250446703836643966422008918876362092101298501441264011663936303490487636790617067387584385/(720*10^210) := by decide +kernel
#print axioms chain_checked
#print axioms weight_checked
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.AssemblyTest11
