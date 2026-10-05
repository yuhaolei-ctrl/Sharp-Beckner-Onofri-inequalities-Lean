import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0155
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0155
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1240 : minorantGammaCheck GammaPanel1240.certificate 1138=true := by decide +kernel
noncomputable def cell1240 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1240.certificate 1138 accepted1240
theorem accepted1241 : minorantGammaCheck GammaPanel1241.certificate 1139=true := by decide +kernel
noncomputable def cell1241 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1241.certificate 1139 accepted1241
theorem accepted1242 : minorantGammaCheck GammaPanel1242.certificate 1140=true := by decide +kernel
noncomputable def cell1242 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1242.certificate 1140 accepted1242
theorem accepted1243 : minorantGammaCheck GammaPanel1243.certificate 1141=true := by decide +kernel
noncomputable def cell1243 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1243.certificate 1141 accepted1243
theorem accepted1244 : minorantGammaCheck GammaPanel1244.certificate 1142=true := by decide +kernel
noncomputable def cell1244 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1244.certificate 1142 accepted1244
theorem accepted1245 : minorantGammaCheck GammaPanel1245.certificate 1143=true := by decide +kernel
noncomputable def cell1245 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1245.certificate 1143 accepted1245
theorem accepted1246 : minorantGammaCheck GammaPanel1246.certificate 1144=true := by decide +kernel
noncomputable def cell1246 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1246.certificate 1144 accepted1246
theorem accepted1247 : minorantGammaCheck GammaPanel1247.certificate 1145=true := by decide +kernel
noncomputable def cell1247 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1247.certificate 1145 accepted1247
noncomputable def cells : List CertifiedMinorantCell := [cell1240, cell1241, cell1242, cell1243, cell1244, cell1245, cell1246, cell1247]
theorem chainAccepted : minorantChainCheck (361/500) (73/100) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (361/500) (73/100) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0155
