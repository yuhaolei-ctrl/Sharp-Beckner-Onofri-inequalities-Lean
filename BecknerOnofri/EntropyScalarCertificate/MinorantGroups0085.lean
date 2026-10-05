import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0085
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0085
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0680 : minorantGammaCheck GammaPanel0680.certificate 616=true := by decide +kernel
noncomputable def cell0680 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0680.certificate 616 accepted0680
theorem accepted0681 : minorantGammaCheck GammaPanel0681.certificate 616=true := by decide +kernel
noncomputable def cell0681 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0681.certificate 616 accepted0681
theorem accepted0682 : minorantGammaCheck GammaPanel0682.certificate 616=true := by decide +kernel
noncomputable def cell0682 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0682.certificate 616 accepted0682
theorem accepted0683 : minorantGammaCheck GammaPanel0683.certificate 616=true := by decide +kernel
noncomputable def cell0683 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0683.certificate 616 accepted0683
theorem accepted0684 : minorantGammaCheck GammaPanel0684.certificate 616=true := by decide +kernel
noncomputable def cell0684 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0684.certificate 616 accepted0684
theorem accepted0685 : minorantGammaCheck GammaPanel0685.certificate 616=true := by decide +kernel
noncomputable def cell0685 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0685.certificate 616 accepted0685
theorem accepted0686 : minorantGammaCheck GammaPanel0686.certificate 616=true := by decide +kernel
noncomputable def cell0686 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0686.certificate 616 accepted0686
theorem accepted0687 : minorantGammaCheck GammaPanel0687.certificate 616=true := by decide +kernel
noncomputable def cell0687 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0687.certificate 616 accepted0687
noncomputable def cells : List CertifiedMinorantCell := [cell0680, cell0681, cell0682, cell0683, cell0684, cell0685, cell0686, cell0687]
theorem chainAccepted : minorantChainCheck (77/400) (1941/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (77/400) (1941/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0085
