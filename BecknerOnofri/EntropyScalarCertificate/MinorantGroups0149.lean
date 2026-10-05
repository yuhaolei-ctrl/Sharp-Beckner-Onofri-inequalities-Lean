module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0149

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0149
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1192 : minorantGammaCheck GammaPanel1192.certificate 1090=true := by decide +kernel
noncomputable def cell1192 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1192.certificate 1090 accepted1192
theorem accepted1193 : minorantGammaCheck GammaPanel1193.certificate 1091=true := by decide +kernel
noncomputable def cell1193 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1193.certificate 1091 accepted1193
theorem accepted1194 : minorantGammaCheck GammaPanel1194.certificate 1092=true := by decide +kernel
noncomputable def cell1194 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1194.certificate 1092 accepted1194
theorem accepted1195 : minorantGammaCheck GammaPanel1195.certificate 1093=true := by decide +kernel
noncomputable def cell1195 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1195.certificate 1093 accepted1195
theorem accepted1196 : minorantGammaCheck GammaPanel1196.certificate 1094=true := by decide +kernel
noncomputable def cell1196 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1196.certificate 1094 accepted1196
theorem accepted1197 : minorantGammaCheck GammaPanel1197.certificate 1095=true := by decide +kernel
noncomputable def cell1197 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1197.certificate 1095 accepted1197
theorem accepted1198 : minorantGammaCheck GammaPanel1198.certificate 1096=true := by decide +kernel
noncomputable def cell1198 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1198.certificate 1096 accepted1198
theorem accepted1199 : minorantGammaCheck GammaPanel1199.certificate 1097=true := by decide +kernel
noncomputable def cell1199 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1199.certificate 1097 accepted1199
noncomputable def cells : List CertifiedMinorantCell := [cell1192, cell1193, cell1194, cell1195, cell1196, cell1197, cell1198, cell1199]
theorem chainAccepted : minorantChainCheck (337/500) (341/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (337/500) (341/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0149
