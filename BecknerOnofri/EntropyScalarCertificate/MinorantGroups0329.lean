import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0329
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0329
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2632 : minorantGammaCheck GammaPanel2632.certificate 1621=true := by decide +kernel
noncomputable def cell2632 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2632.certificate 1621 accepted2632
theorem accepted2633 : minorantGammaCheck GammaPanel2633.certificate 1621=true := by decide +kernel
noncomputable def cell2633 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2633.certificate 1621 accepted2633
theorem accepted2634 : minorantGammaCheck GammaPanel2634.certificate 1621=true := by decide +kernel
noncomputable def cell2634 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2634.certificate 1621 accepted2634
theorem accepted2635 : minorantGammaCheck GammaPanel2635.certificate 1621=true := by decide +kernel
noncomputable def cell2635 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2635.certificate 1621 accepted2635
theorem accepted2636 : minorantGammaCheck GammaPanel2636.certificate 1621=true := by decide +kernel
noncomputable def cell2636 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2636.certificate 1621 accepted2636
theorem accepted2637 : minorantGammaCheck GammaPanel2637.certificate 1621=true := by decide +kernel
noncomputable def cell2637 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2637.certificate 1621 accepted2637
theorem accepted2638 : minorantGammaCheck GammaPanel2638.certificate 1621=true := by decide +kernel
noncomputable def cell2638 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2638.certificate 1621 accepted2638
theorem accepted2639 : minorantGammaCheck GammaPanel2639.certificate 1621=true := by decide +kernel
noncomputable def cell2639 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2639.certificate 1621 accepted2639
noncomputable def cells : List CertifiedMinorantCell := [cell2632, cell2633, cell2634, cell2635, cell2636, cell2637, cell2638, cell2639]
theorem chainAccepted : minorantChainCheck (24877/25000) (24881/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24877/25000) (24881/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0329
