import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0137
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0137
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1096 : minorantGammaCheck GammaPanel1096.certificate 994=true := by decide +kernel
noncomputable def cell1096 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1096.certificate 994 accepted1096
theorem accepted1097 : minorantGammaCheck GammaPanel1097.certificate 995=true := by decide +kernel
noncomputable def cell1097 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1097.certificate 995 accepted1097
theorem accepted1098 : minorantGammaCheck GammaPanel1098.certificate 996=true := by decide +kernel
noncomputable def cell1098 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1098.certificate 996 accepted1098
theorem accepted1099 : minorantGammaCheck GammaPanel1099.certificate 997=true := by decide +kernel
noncomputable def cell1099 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1099.certificate 997 accepted1099
theorem accepted1100 : minorantGammaCheck GammaPanel1100.certificate 998=true := by decide +kernel
noncomputable def cell1100 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1100.certificate 998 accepted1100
theorem accepted1101 : minorantGammaCheck GammaPanel1101.certificate 999=true := by decide +kernel
noncomputable def cell1101 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1101.certificate 999 accepted1101
theorem accepted1102 : minorantGammaCheck GammaPanel1102.certificate 1000=true := by decide +kernel
noncomputable def cell1102 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1102.certificate 1000 accepted1102
theorem accepted1103 : minorantGammaCheck GammaPanel1103.certificate 1001=true := by decide +kernel
noncomputable def cell1103 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1103.certificate 1001 accepted1103
noncomputable def cells : List CertifiedMinorantCell := [cell1096, cell1097, cell1098, cell1099, cell1100, cell1101, cell1102, cell1103]
theorem chainAccepted : minorantChainCheck (289/500) (293/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (289/500) (293/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0137
