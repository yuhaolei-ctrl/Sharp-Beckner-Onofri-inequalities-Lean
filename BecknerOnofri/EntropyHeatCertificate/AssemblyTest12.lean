import BecknerOnofri.EntropyHeatCheckedWeights
import BecknerOnofri.EntropyTailRowAssembly
import BecknerOnofri.EntropyHeatCertificate.Panels0000
import BecknerOnofri.EntropyHeatCertificate.Panels0001
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate.AssemblyTest12
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
def blocks : List (WeightedPanelBlock (9950248756218905472636815920/10^30)) := [
  weightedBlockOfRows Panels0000.block Panels0000.accepted Panels0000.integerPanels Panels0000.aligned
    Panels0000.weightRows Panels0000.weights_checked ⟨12, by decide⟩,
  weightedBlockOfRows Panels0001.block Panels0001.accepted Panels0001.integerPanels Panels0001.aligned
    Panels0001.weightRows Panels0001.weights_checked ⟨12, by decide⟩
]
theorem chain_checked : blockChainCheck (9950248756218905472636815920/10^30) (10591903868877960435253721855/10^30)
    (blocks.map WeightedPanelBlock.certificate) = true := by decide +kernel
theorem weight_checked : weightedTotal blocks = 50161293113673778659228962532911877897293790904830633692618790460713004987000524015023612324728182416745306949394327478191142081365195492431951957379523107646812337858321029807017901518316163367384965336738/(720*10^210) := by decide +kernel
#print axioms chain_checked
#print axioms weight_checked
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate.AssemblyTest12
