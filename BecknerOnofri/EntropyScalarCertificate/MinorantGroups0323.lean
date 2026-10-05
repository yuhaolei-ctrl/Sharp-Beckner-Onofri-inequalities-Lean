import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0323
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0323
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2584 : minorantGammaCheck GammaPanel2584.certificate 1621=true := by decide +kernel
noncomputable def cell2584 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2584.certificate 1621 accepted2584
theorem accepted2585 : minorantGammaCheck GammaPanel2585.certificate 1621=true := by decide +kernel
noncomputable def cell2585 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2585.certificate 1621 accepted2585
theorem accepted2586 : minorantGammaCheck GammaPanel2586.certificate 1621=true := by decide +kernel
noncomputable def cell2586 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2586.certificate 1621 accepted2586
theorem accepted2587 : minorantGammaCheck GammaPanel2587.certificate 1621=true := by decide +kernel
noncomputable def cell2587 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2587.certificate 1621 accepted2587
theorem accepted2588 : minorantGammaCheck GammaPanel2588.certificate 1621=true := by decide +kernel
noncomputable def cell2588 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2588.certificate 1621 accepted2588
theorem accepted2589 : minorantGammaCheck GammaPanel2589.certificate 1621=true := by decide +kernel
noncomputable def cell2589 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2589.certificate 1621 accepted2589
theorem accepted2590 : minorantGammaCheck GammaPanel2590.certificate 1621=true := by decide +kernel
noncomputable def cell2590 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2590.certificate 1621 accepted2590
theorem accepted2591 : minorantGammaCheck GammaPanel2591.certificate 1621=true := by decide +kernel
noncomputable def cell2591 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2591.certificate 1621 accepted2591
noncomputable def cells : List CertifiedMinorantCell := [cell2584, cell2585, cell2586, cell2587, cell2588, cell2589, cell2590, cell2591]
theorem chainAccepted : minorantChainCheck (24853/25000) (24857/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24853/25000) (24857/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0323
