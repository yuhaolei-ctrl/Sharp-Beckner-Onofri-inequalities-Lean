import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0071
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0071
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0568 : minorantGammaCheck GammaPanel0568.certificate 528=true := by decide +kernel
noncomputable def cell0568 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0568.certificate 528 accepted0568
theorem accepted0569 : minorantGammaCheck GammaPanel0569.certificate 529=true := by decide +kernel
noncomputable def cell0569 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0569.certificate 529 accepted0569
theorem accepted0570 : minorantGammaCheck GammaPanel0570.certificate 530=true := by decide +kernel
noncomputable def cell0570 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0570.certificate 530 accepted0570
theorem accepted0571 : minorantGammaCheck GammaPanel0571.certificate 531=true := by decide +kernel
noncomputable def cell0571 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0571.certificate 531 accepted0571
theorem accepted0572 : minorantGammaCheck GammaPanel0572.certificate 532=true := by decide +kernel
noncomputable def cell0572 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0572.certificate 532 accepted0572
theorem accepted0573 : minorantGammaCheck GammaPanel0573.certificate 533=true := by decide +kernel
noncomputable def cell0573 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0573.certificate 533 accepted0573
theorem accepted0574 : minorantGammaCheck GammaPanel0574.certificate 534=true := by decide +kernel
noncomputable def cell0574 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0574.certificate 534 accepted0574
theorem accepted0575 : minorantGammaCheck GammaPanel0575.certificate 535=true := by decide +kernel
noncomputable def cell0575 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0575.certificate 535 accepted0575
noncomputable def cells : List CertifiedMinorantCell := [cell0568, cell0569, cell0570, cell0571, cell0572, cell0573, cell0574, cell0575]
theorem chainAccepted : minorantChainCheck (1701/10000) (1717/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1701/10000) (1717/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0071
