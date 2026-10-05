import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0136
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0136
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1088 : minorantGammaCheck GammaPanel1088.certificate 986=true := by decide +kernel
noncomputable def cell1088 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1088.certificate 986 accepted1088
theorem accepted1089 : minorantGammaCheck GammaPanel1089.certificate 987=true := by decide +kernel
noncomputable def cell1089 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1089.certificate 987 accepted1089
theorem accepted1090 : minorantGammaCheck GammaPanel1090.certificate 988=true := by decide +kernel
noncomputable def cell1090 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1090.certificate 988 accepted1090
theorem accepted1091 : minorantGammaCheck GammaPanel1091.certificate 989=true := by decide +kernel
noncomputable def cell1091 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1091.certificate 989 accepted1091
theorem accepted1092 : minorantGammaCheck GammaPanel1092.certificate 990=true := by decide +kernel
noncomputable def cell1092 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1092.certificate 990 accepted1092
theorem accepted1093 : minorantGammaCheck GammaPanel1093.certificate 991=true := by decide +kernel
noncomputable def cell1093 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1093.certificate 991 accepted1093
theorem accepted1094 : minorantGammaCheck GammaPanel1094.certificate 992=true := by decide +kernel
noncomputable def cell1094 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1094.certificate 992 accepted1094
theorem accepted1095 : minorantGammaCheck GammaPanel1095.certificate 993=true := by decide +kernel
noncomputable def cell1095 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1095.certificate 993 accepted1095
noncomputable def cells : List CertifiedMinorantCell := [cell1088, cell1089, cell1090, cell1091, cell1092, cell1093, cell1094, cell1095]
theorem chainAccepted : minorantChainCheck (57/100) (289/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (57/100) (289/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0136
