module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0172

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0172
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1376 : minorantGammaCheck GammaPanel1376.certificate 1247=true := by decide +kernel
noncomputable def cell1376 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1376.certificate 1247 accepted1376
theorem accepted1377 : minorantGammaCheck GammaPanel1377.certificate 1248=true := by decide +kernel
noncomputable def cell1377 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1377.certificate 1248 accepted1377
theorem accepted1378 : minorantGammaCheck GammaPanel1378.certificate 1249=true := by decide +kernel
noncomputable def cell1378 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1378.certificate 1249 accepted1378
theorem accepted1379 : minorantGammaCheck GammaPanel1379.certificate 1249=true := by decide +kernel
noncomputable def cell1379 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1379.certificate 1249 accepted1379
theorem accepted1380 : minorantGammaCheck GammaPanel1380.certificate 1249=true := by decide +kernel
noncomputable def cell1380 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1380.certificate 1249 accepted1380
theorem accepted1381 : minorantGammaCheck GammaPanel1381.certificate 1249=true := by decide +kernel
noncomputable def cell1381 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1381.certificate 1249 accepted1381
theorem accepted1382 : minorantGammaCheck GammaPanel1382.certificate 1249=true := by decide +kernel
noncomputable def cell1382 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1382.certificate 1249 accepted1382
theorem accepted1383 : minorantGammaCheck GammaPanel1383.certificate 1249=true := by decide +kernel
noncomputable def cell1383 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1383.certificate 1249 accepted1383
noncomputable def cells : List CertifiedMinorantCell := [cell1376, cell1377, cell1378, cell1379, cell1380, cell1381, cell1382, cell1383]
theorem chainAccepted : minorantChainCheck (829/1000) (4153/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (829/1000) (4153/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0172
