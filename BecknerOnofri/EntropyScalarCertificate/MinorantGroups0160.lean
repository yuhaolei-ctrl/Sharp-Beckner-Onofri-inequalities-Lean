module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0160

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0160
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1280 : minorantGammaCheck GammaPanel1280.certificate 1178=true := by decide +kernel
noncomputable def cell1280 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1280.certificate 1178 accepted1280
theorem accepted1281 : minorantGammaCheck GammaPanel1281.certificate 1179=true := by decide +kernel
noncomputable def cell1281 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1281.certificate 1179 accepted1281
theorem accepted1282 : minorantGammaCheck GammaPanel1282.certificate 1180=true := by decide +kernel
noncomputable def cell1282 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1282.certificate 1180 accepted1282
theorem accepted1283 : minorantGammaCheck GammaPanel1283.certificate 1181=true := by decide +kernel
noncomputable def cell1283 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1283.certificate 1181 accepted1283
theorem accepted1284 : minorantGammaCheck GammaPanel1284.certificate 1182=true := by decide +kernel
noncomputable def cell1284 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1284.certificate 1182 accepted1284
theorem accepted1285 : minorantGammaCheck GammaPanel1285.certificate 1183=true := by decide +kernel
noncomputable def cell1285 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1285.certificate 1183 accepted1285
theorem accepted1286 : minorantGammaCheck GammaPanel1286.certificate 1184=true := by decide +kernel
noncomputable def cell1286 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1286.certificate 1184 accepted1286
theorem accepted1287 : minorantGammaCheck GammaPanel1287.certificate 1185=true := by decide +kernel
noncomputable def cell1287 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1287.certificate 1185 accepted1287
noncomputable def cells : List CertifiedMinorantCell := [cell1280, cell1281, cell1282, cell1283, cell1284, cell1285, cell1286, cell1287]
theorem chainAccepted : minorantChainCheck (381/500) (77/100) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (381/500) (77/100) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0160
