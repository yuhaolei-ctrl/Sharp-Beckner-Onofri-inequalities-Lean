import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0157
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0157
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1256 : minorantGammaCheck GammaPanel1256.certificate 1154=true := by decide +kernel
noncomputable def cell1256 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1256.certificate 1154 accepted1256
theorem accepted1257 : minorantGammaCheck GammaPanel1257.certificate 1155=true := by decide +kernel
noncomputable def cell1257 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1257.certificate 1155 accepted1257
theorem accepted1258 : minorantGammaCheck GammaPanel1258.certificate 1156=true := by decide +kernel
noncomputable def cell1258 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1258.certificate 1156 accepted1258
theorem accepted1259 : minorantGammaCheck GammaPanel1259.certificate 1157=true := by decide +kernel
noncomputable def cell1259 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1259.certificate 1157 accepted1259
theorem accepted1260 : minorantGammaCheck GammaPanel1260.certificate 1158=true := by decide +kernel
noncomputable def cell1260 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1260.certificate 1158 accepted1260
theorem accepted1261 : minorantGammaCheck GammaPanel1261.certificate 1159=true := by decide +kernel
noncomputable def cell1261 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1261.certificate 1159 accepted1261
theorem accepted1262 : minorantGammaCheck GammaPanel1262.certificate 1160=true := by decide +kernel
noncomputable def cell1262 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1262.certificate 1160 accepted1262
theorem accepted1263 : minorantGammaCheck GammaPanel1263.certificate 1161=true := by decide +kernel
noncomputable def cell1263 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1263.certificate 1161 accepted1263
noncomputable def cells : List CertifiedMinorantCell := [cell1256, cell1257, cell1258, cell1259, cell1260, cell1261, cell1262, cell1263]
theorem chainAccepted : minorantChainCheck (369/500) (373/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (369/500) (373/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0157
