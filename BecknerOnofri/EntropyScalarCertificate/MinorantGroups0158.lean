module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0158

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0158
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1264 : minorantGammaCheck GammaPanel1264.certificate 1162=true := by decide +kernel
noncomputable def cell1264 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1264.certificate 1162 accepted1264
theorem accepted1265 : minorantGammaCheck GammaPanel1265.certificate 1163=true := by decide +kernel
noncomputable def cell1265 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1265.certificate 1163 accepted1265
theorem accepted1266 : minorantGammaCheck GammaPanel1266.certificate 1164=true := by decide +kernel
noncomputable def cell1266 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1266.certificate 1164 accepted1266
theorem accepted1267 : minorantGammaCheck GammaPanel1267.certificate 1165=true := by decide +kernel
noncomputable def cell1267 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1267.certificate 1165 accepted1267
theorem accepted1268 : minorantGammaCheck GammaPanel1268.certificate 1166=true := by decide +kernel
noncomputable def cell1268 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1268.certificate 1166 accepted1268
theorem accepted1269 : minorantGammaCheck GammaPanel1269.certificate 1167=true := by decide +kernel
noncomputable def cell1269 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1269.certificate 1167 accepted1269
theorem accepted1270 : minorantGammaCheck GammaPanel1270.certificate 1168=true := by decide +kernel
noncomputable def cell1270 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1270.certificate 1168 accepted1270
theorem accepted1271 : minorantGammaCheck GammaPanel1271.certificate 1169=true := by decide +kernel
noncomputable def cell1271 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1271.certificate 1169 accepted1271
noncomputable def cells : List CertifiedMinorantCell := [cell1264, cell1265, cell1266, cell1267, cell1268, cell1269, cell1270, cell1271]
theorem chainAccepted : minorantChainCheck (373/500) (377/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (373/500) (377/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0158
