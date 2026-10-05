import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0328
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0328
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2624 : minorantGammaCheck GammaPanel2624.certificate 1621=true := by decide +kernel
noncomputable def cell2624 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2624.certificate 1621 accepted2624
theorem accepted2625 : minorantGammaCheck GammaPanel2625.certificate 1621=true := by decide +kernel
noncomputable def cell2625 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2625.certificate 1621 accepted2625
theorem accepted2626 : minorantGammaCheck GammaPanel2626.certificate 1621=true := by decide +kernel
noncomputable def cell2626 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2626.certificate 1621 accepted2626
theorem accepted2627 : minorantGammaCheck GammaPanel2627.certificate 1621=true := by decide +kernel
noncomputable def cell2627 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2627.certificate 1621 accepted2627
theorem accepted2628 : minorantGammaCheck GammaPanel2628.certificate 1621=true := by decide +kernel
noncomputable def cell2628 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2628.certificate 1621 accepted2628
theorem accepted2629 : minorantGammaCheck GammaPanel2629.certificate 1621=true := by decide +kernel
noncomputable def cell2629 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2629.certificate 1621 accepted2629
theorem accepted2630 : minorantGammaCheck GammaPanel2630.certificate 1621=true := by decide +kernel
noncomputable def cell2630 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2630.certificate 1621 accepted2630
theorem accepted2631 : minorantGammaCheck GammaPanel2631.certificate 1621=true := by decide +kernel
noncomputable def cell2631 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2631.certificate 1621 accepted2631
noncomputable def cells : List CertifiedMinorantCell := [cell2624, cell2625, cell2626, cell2627, cell2628, cell2629, cell2630, cell2631]
theorem chainAccepted : minorantChainCheck (24873/25000) (24877/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24873/25000) (24877/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0328
