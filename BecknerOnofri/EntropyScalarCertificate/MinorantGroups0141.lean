import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0141
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0141
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1128 : minorantGammaCheck GammaPanel1128.certificate 1026=true := by decide +kernel
noncomputable def cell1128 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1128.certificate 1026 accepted1128
theorem accepted1129 : minorantGammaCheck GammaPanel1129.certificate 1027=true := by decide +kernel
noncomputable def cell1129 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1129.certificate 1027 accepted1129
theorem accepted1130 : minorantGammaCheck GammaPanel1130.certificate 1028=true := by decide +kernel
noncomputable def cell1130 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1130.certificate 1028 accepted1130
theorem accepted1131 : minorantGammaCheck GammaPanel1131.certificate 1029=true := by decide +kernel
noncomputable def cell1131 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1131.certificate 1029 accepted1131
theorem accepted1132 : minorantGammaCheck GammaPanel1132.certificate 1030=true := by decide +kernel
noncomputable def cell1132 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1132.certificate 1030 accepted1132
theorem accepted1133 : minorantGammaCheck GammaPanel1133.certificate 1031=true := by decide +kernel
noncomputable def cell1133 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1133.certificate 1031 accepted1133
theorem accepted1134 : minorantGammaCheck GammaPanel1134.certificate 1032=true := by decide +kernel
noncomputable def cell1134 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1134.certificate 1032 accepted1134
theorem accepted1135 : minorantGammaCheck GammaPanel1135.certificate 1033=true := by decide +kernel
noncomputable def cell1135 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1135.certificate 1033 accepted1135
noncomputable def cells : List CertifiedMinorantCell := [cell1128, cell1129, cell1130, cell1131, cell1132, cell1133, cell1134, cell1135]
theorem chainAccepted : minorantChainCheck (61/100) (309/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (61/100) (309/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0141
