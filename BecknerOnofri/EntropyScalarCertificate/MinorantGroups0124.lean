import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0124
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0124
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0992 : minorantGammaCheck GammaPanel0992.certificate 890=true := by decide +kernel
noncomputable def cell0992 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0992.certificate 890 accepted0992
theorem accepted0993 : minorantGammaCheck GammaPanel0993.certificate 891=true := by decide +kernel
noncomputable def cell0993 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0993.certificate 891 accepted0993
theorem accepted0994 : minorantGammaCheck GammaPanel0994.certificate 892=true := by decide +kernel
noncomputable def cell0994 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0994.certificate 892 accepted0994
theorem accepted0995 : minorantGammaCheck GammaPanel0995.certificate 893=true := by decide +kernel
noncomputable def cell0995 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0995.certificate 893 accepted0995
theorem accepted0996 : minorantGammaCheck GammaPanel0996.certificate 894=true := by decide +kernel
noncomputable def cell0996 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0996.certificate 894 accepted0996
theorem accepted0997 : minorantGammaCheck GammaPanel0997.certificate 895=true := by decide +kernel
noncomputable def cell0997 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0997.certificate 895 accepted0997
theorem accepted0998 : minorantGammaCheck GammaPanel0998.certificate 896=true := by decide +kernel
noncomputable def cell0998 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0998.certificate 896 accepted0998
theorem accepted0999 : minorantGammaCheck GammaPanel0999.certificate 897=true := by decide +kernel
noncomputable def cell0999 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0999.certificate 897 accepted0999
noncomputable def cells : List CertifiedMinorantCell := [cell0992, cell0993, cell0994, cell0995, cell0996, cell0997, cell0998, cell0999]
theorem chainAccepted : minorantChainCheck (237/500) (241/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (237/500) (241/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0124
