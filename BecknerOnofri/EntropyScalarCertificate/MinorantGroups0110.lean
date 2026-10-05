module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0110

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0110
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0880 : minorantGammaCheck GammaPanel0880.certificate 778=true := by decide +kernel
noncomputable def cell0880 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0880.certificate 778 accepted0880
theorem accepted0881 : minorantGammaCheck GammaPanel0881.certificate 779=true := by decide +kernel
noncomputable def cell0881 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0881.certificate 779 accepted0881
theorem accepted0882 : minorantGammaCheck GammaPanel0882.certificate 780=true := by decide +kernel
noncomputable def cell0882 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0882.certificate 780 accepted0882
theorem accepted0883 : minorantGammaCheck GammaPanel0883.certificate 781=true := by decide +kernel
noncomputable def cell0883 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0883.certificate 781 accepted0883
theorem accepted0884 : minorantGammaCheck GammaPanel0884.certificate 782=true := by decide +kernel
noncomputable def cell0884 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0884.certificate 782 accepted0884
theorem accepted0885 : minorantGammaCheck GammaPanel0885.certificate 783=true := by decide +kernel
noncomputable def cell0885 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0885.certificate 783 accepted0885
theorem accepted0886 : minorantGammaCheck GammaPanel0886.certificate 784=true := by decide +kernel
noncomputable def cell0886 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0886.certificate 784 accepted0886
theorem accepted0887 : minorantGammaCheck GammaPanel0887.certificate 785=true := by decide +kernel
noncomputable def cell0887 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0887.certificate 785 accepted0887
noncomputable def cells : List CertifiedMinorantCell := [cell0880, cell0881, cell0882, cell0883, cell0884, cell0885, cell0886, cell0887]
theorem chainAccepted : minorantChainCheck (181/500) (37/100) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (181/500) (37/100) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0110
