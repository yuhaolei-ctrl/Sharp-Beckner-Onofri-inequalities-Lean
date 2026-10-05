import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0144
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0144
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1152 : minorantGammaCheck GammaPanel1152.certificate 1050=true := by decide +kernel
noncomputable def cell1152 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1152.certificate 1050 accepted1152
theorem accepted1153 : minorantGammaCheck GammaPanel1153.certificate 1051=true := by decide +kernel
noncomputable def cell1153 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1153.certificate 1051 accepted1153
theorem accepted1154 : minorantGammaCheck GammaPanel1154.certificate 1052=true := by decide +kernel
noncomputable def cell1154 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1154.certificate 1052 accepted1154
theorem accepted1155 : minorantGammaCheck GammaPanel1155.certificate 1053=true := by decide +kernel
noncomputable def cell1155 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1155.certificate 1053 accepted1155
theorem accepted1156 : minorantGammaCheck GammaPanel1156.certificate 1054=true := by decide +kernel
noncomputable def cell1156 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1156.certificate 1054 accepted1156
theorem accepted1157 : minorantGammaCheck GammaPanel1157.certificate 1055=true := by decide +kernel
noncomputable def cell1157 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1157.certificate 1055 accepted1157
theorem accepted1158 : minorantGammaCheck GammaPanel1158.certificate 1056=true := by decide +kernel
noncomputable def cell1158 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1158.certificate 1056 accepted1158
theorem accepted1159 : minorantGammaCheck GammaPanel1159.certificate 1057=true := by decide +kernel
noncomputable def cell1159 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1159.certificate 1057 accepted1159
noncomputable def cells : List CertifiedMinorantCell := [cell1152, cell1153, cell1154, cell1155, cell1156, cell1157, cell1158, cell1159]
theorem chainAccepted : minorantChainCheck (317/500) (321/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (317/500) (321/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0144
