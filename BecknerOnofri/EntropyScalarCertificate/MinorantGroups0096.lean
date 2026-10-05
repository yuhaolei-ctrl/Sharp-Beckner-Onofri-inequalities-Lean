import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0096
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0096
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0768 : minorantGammaCheck GammaPanel0768.certificate 666=true := by decide +kernel
noncomputable def cell0768 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0768.certificate 666 accepted0768
theorem accepted0769 : minorantGammaCheck GammaPanel0769.certificate 667=true := by decide +kernel
noncomputable def cell0769 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0769.certificate 667 accepted0769
theorem accepted0770 : minorantGammaCheck GammaPanel0770.certificate 668=true := by decide +kernel
noncomputable def cell0770 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0770.certificate 668 accepted0770
theorem accepted0771 : minorantGammaCheck GammaPanel0771.certificate 669=true := by decide +kernel
noncomputable def cell0771 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0771.certificate 669 accepted0771
theorem accepted0772 : minorantGammaCheck GammaPanel0772.certificate 670=true := by decide +kernel
noncomputable def cell0772 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0772.certificate 670 accepted0772
theorem accepted0773 : minorantGammaCheck GammaPanel0773.certificate 671=true := by decide +kernel
noncomputable def cell0773 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0773.certificate 671 accepted0773
theorem accepted0774 : minorantGammaCheck GammaPanel0774.certificate 672=true := by decide +kernel
noncomputable def cell0774 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0774.certificate 672 accepted0774
theorem accepted0775 : minorantGammaCheck GammaPanel0775.certificate 673=true := by decide +kernel
noncomputable def cell0775 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0775.certificate 673 accepted0775
noncomputable def cells : List CertifiedMinorantCell := [cell0768, cell0769, cell0770, cell0771, cell0772, cell0773, cell0774, cell0775]
theorem chainAccepted : minorantChainCheck (1/4) (129/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1/4) (129/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0096
