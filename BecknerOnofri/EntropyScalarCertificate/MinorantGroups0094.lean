import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0094
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0094
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0752 : minorantGammaCheck GammaPanel0752.certificate 650=true := by decide +kernel
noncomputable def cell0752 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0752.certificate 650 accepted0752
theorem accepted0753 : minorantGammaCheck GammaPanel0753.certificate 651=true := by decide +kernel
noncomputable def cell0753 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0753.certificate 651 accepted0753
theorem accepted0754 : minorantGammaCheck GammaPanel0754.certificate 652=true := by decide +kernel
noncomputable def cell0754 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0754.certificate 652 accepted0754
theorem accepted0755 : minorantGammaCheck GammaPanel0755.certificate 653=true := by decide +kernel
noncomputable def cell0755 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0755.certificate 653 accepted0755
theorem accepted0756 : minorantGammaCheck GammaPanel0756.certificate 654=true := by decide +kernel
noncomputable def cell0756 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0756.certificate 654 accepted0756
theorem accepted0757 : minorantGammaCheck GammaPanel0757.certificate 655=true := by decide +kernel
noncomputable def cell0757 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0757.certificate 655 accepted0757
theorem accepted0758 : minorantGammaCheck GammaPanel0758.certificate 656=true := by decide +kernel
noncomputable def cell0758 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0758.certificate 656 accepted0758
theorem accepted0759 : minorantGammaCheck GammaPanel0759.certificate 657=true := by decide +kernel
noncomputable def cell0759 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0759.certificate 657 accepted0759
noncomputable def cells : List CertifiedMinorantCell := [cell0752, cell0753, cell0754, cell0755, cell0756, cell0757, cell0758, cell0759]
theorem chainAccepted : minorantChainCheck (117/500) (121/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (117/500) (121/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0094
