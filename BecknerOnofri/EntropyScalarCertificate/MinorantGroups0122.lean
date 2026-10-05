import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0122
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0122
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0976 : minorantGammaCheck GammaPanel0976.certificate 874=true := by decide +kernel
noncomputable def cell0976 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0976.certificate 874 accepted0976
theorem accepted0977 : minorantGammaCheck GammaPanel0977.certificate 875=true := by decide +kernel
noncomputable def cell0977 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0977.certificate 875 accepted0977
theorem accepted0978 : minorantGammaCheck GammaPanel0978.certificate 876=true := by decide +kernel
noncomputable def cell0978 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0978.certificate 876 accepted0978
theorem accepted0979 : minorantGammaCheck GammaPanel0979.certificate 877=true := by decide +kernel
noncomputable def cell0979 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0979.certificate 877 accepted0979
theorem accepted0980 : minorantGammaCheck GammaPanel0980.certificate 878=true := by decide +kernel
noncomputable def cell0980 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0980.certificate 878 accepted0980
theorem accepted0981 : minorantGammaCheck GammaPanel0981.certificate 879=true := by decide +kernel
noncomputable def cell0981 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0981.certificate 879 accepted0981
theorem accepted0982 : minorantGammaCheck GammaPanel0982.certificate 880=true := by decide +kernel
noncomputable def cell0982 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0982.certificate 880 accepted0982
theorem accepted0983 : minorantGammaCheck GammaPanel0983.certificate 881=true := by decide +kernel
noncomputable def cell0983 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0983.certificate 881 accepted0983
noncomputable def cells : List CertifiedMinorantCell := [cell0976, cell0977, cell0978, cell0979, cell0980, cell0981, cell0982, cell0983]
theorem chainAccepted : minorantChainCheck (229/500) (233/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (229/500) (233/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0122
