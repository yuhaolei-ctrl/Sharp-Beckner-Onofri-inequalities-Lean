import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0079
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0079
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0632 : minorantGammaCheck GammaPanel0632.certificate 592=true := by decide +kernel
noncomputable def cell0632 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0632.certificate 592 accepted0632
theorem accepted0633 : minorantGammaCheck GammaPanel0633.certificate 593=true := by decide +kernel
noncomputable def cell0633 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0633.certificate 593 accepted0633
theorem accepted0634 : minorantGammaCheck GammaPanel0634.certificate 594=true := by decide +kernel
noncomputable def cell0634 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0634.certificate 594 accepted0634
theorem accepted0635 : minorantGammaCheck GammaPanel0635.certificate 595=true := by decide +kernel
noncomputable def cell0635 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0635.certificate 595 accepted0635
theorem accepted0636 : minorantGammaCheck GammaPanel0636.certificate 596=true := by decide +kernel
noncomputable def cell0636 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0636.certificate 596 accepted0636
theorem accepted0637 : minorantGammaCheck GammaPanel0637.certificate 597=true := by decide +kernel
noncomputable def cell0637 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0637.certificate 597 accepted0637
theorem accepted0638 : minorantGammaCheck GammaPanel0638.certificate 598=true := by decide +kernel
noncomputable def cell0638 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0638.certificate 598 accepted0638
theorem accepted0639 : minorantGammaCheck GammaPanel0639.certificate 599=true := by decide +kernel
noncomputable def cell0639 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0639.certificate 599 accepted0639
noncomputable def cells : List CertifiedMinorantCell := [cell0632, cell0633, cell0634, cell0635, cell0636, cell0637, cell0638, cell0639]
theorem chainAccepted : minorantChainCheck (1829/10000) (369/2000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1829/10000) (369/2000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0079
