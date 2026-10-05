import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0336
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0336
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2688 : minorantGammaCheck GammaPanel2688.certificate 1621=true := by decide +kernel
noncomputable def cell2688 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2688.certificate 1621 accepted2688
theorem accepted2689 : minorantGammaCheck GammaPanel2689.certificate 1621=true := by decide +kernel
noncomputable def cell2689 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2689.certificate 1621 accepted2689
theorem accepted2690 : minorantGammaCheck GammaPanel2690.certificate 1621=true := by decide +kernel
noncomputable def cell2690 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2690.certificate 1621 accepted2690
theorem accepted2691 : minorantGammaCheck GammaPanel2691.certificate 1621=true := by decide +kernel
noncomputable def cell2691 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2691.certificate 1621 accepted2691
theorem accepted2692 : minorantGammaCheck GammaPanel2692.certificate 1621=true := by decide +kernel
noncomputable def cell2692 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2692.certificate 1621 accepted2692
theorem accepted2693 : minorantGammaCheck GammaPanel2693.certificate 1621=true := by decide +kernel
noncomputable def cell2693 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2693.certificate 1621 accepted2693
theorem accepted2694 : minorantGammaCheck GammaPanel2694.certificate 1621=true := by decide +kernel
noncomputable def cell2694 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2694.certificate 1621 accepted2694
theorem accepted2695 : minorantGammaCheck GammaPanel2695.certificate 1621=true := by decide +kernel
noncomputable def cell2695 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2695.certificate 1621 accepted2695
noncomputable def cells : List CertifiedMinorantCell := [cell2688, cell2689, cell2690, cell2691, cell2692, cell2693, cell2694, cell2695]
theorem chainAccepted : minorantChainCheck (4981/5000) (24909/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4981/5000) (24909/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0336
