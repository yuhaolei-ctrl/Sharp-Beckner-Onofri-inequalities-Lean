import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0151
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0151
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1208 : minorantGammaCheck GammaPanel1208.certificate 1106=true := by decide +kernel
noncomputable def cell1208 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1208.certificate 1106 accepted1208
theorem accepted1209 : minorantGammaCheck GammaPanel1209.certificate 1107=true := by decide +kernel
noncomputable def cell1209 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1209.certificate 1107 accepted1209
theorem accepted1210 : minorantGammaCheck GammaPanel1210.certificate 1108=true := by decide +kernel
noncomputable def cell1210 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1210.certificate 1108 accepted1210
theorem accepted1211 : minorantGammaCheck GammaPanel1211.certificate 1109=true := by decide +kernel
noncomputable def cell1211 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1211.certificate 1109 accepted1211
theorem accepted1212 : minorantGammaCheck GammaPanel1212.certificate 1110=true := by decide +kernel
noncomputable def cell1212 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1212.certificate 1110 accepted1212
theorem accepted1213 : minorantGammaCheck GammaPanel1213.certificate 1111=true := by decide +kernel
noncomputable def cell1213 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1213.certificate 1111 accepted1213
theorem accepted1214 : minorantGammaCheck GammaPanel1214.certificate 1112=true := by decide +kernel
noncomputable def cell1214 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1214.certificate 1112 accepted1214
theorem accepted1215 : minorantGammaCheck GammaPanel1215.certificate 1113=true := by decide +kernel
noncomputable def cell1215 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1215.certificate 1113 accepted1215
noncomputable def cells : List CertifiedMinorantCell := [cell1208, cell1209, cell1210, cell1211, cell1212, cell1213, cell1214, cell1215]
theorem chainAccepted : minorantChainCheck (69/100) (349/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (69/100) (349/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0151
