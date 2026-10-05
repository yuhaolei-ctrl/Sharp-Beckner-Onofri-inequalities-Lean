import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0091
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0091
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0728 : minorantGammaCheck GammaPanel0728.certificate 626=true := by decide +kernel
noncomputable def cell0728 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0728.certificate 626 accepted0728
theorem accepted0729 : minorantGammaCheck GammaPanel0729.certificate 627=true := by decide +kernel
noncomputable def cell0729 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0729.certificate 627 accepted0729
theorem accepted0730 : minorantGammaCheck GammaPanel0730.certificate 628=true := by decide +kernel
noncomputable def cell0730 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0730.certificate 628 accepted0730
theorem accepted0731 : minorantGammaCheck GammaPanel0731.certificate 629=true := by decide +kernel
noncomputable def cell0731 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0731.certificate 629 accepted0731
theorem accepted0732 : minorantGammaCheck GammaPanel0732.certificate 630=true := by decide +kernel
noncomputable def cell0732 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0732.certificate 630 accepted0732
theorem accepted0733 : minorantGammaCheck GammaPanel0733.certificate 631=true := by decide +kernel
noncomputable def cell0733 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0733.certificate 631 accepted0733
theorem accepted0734 : minorantGammaCheck GammaPanel0734.certificate 632=true := by decide +kernel
noncomputable def cell0734 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0734.certificate 632 accepted0734
theorem accepted0735 : minorantGammaCheck GammaPanel0735.certificate 633=true := by decide +kernel
noncomputable def cell0735 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0735.certificate 633 accepted0735
noncomputable def cells : List CertifiedMinorantCell := [cell0728, cell0729, cell0730, cell0731, cell0732, cell0733, cell0734, cell0735]
theorem chainAccepted : minorantChainCheck (21/100) (109/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (21/100) (109/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0091
