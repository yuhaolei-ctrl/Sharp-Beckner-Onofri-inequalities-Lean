import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0171
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0171
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1368 : minorantGammaCheck GammaPanel1368.certificate 1239=true := by decide +kernel
noncomputable def cell1368 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1368.certificate 1239 accepted1368
theorem accepted1369 : minorantGammaCheck GammaPanel1369.certificate 1240=true := by decide +kernel
noncomputable def cell1369 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1369.certificate 1240 accepted1369
theorem accepted1370 : minorantGammaCheck GammaPanel1370.certificate 1241=true := by decide +kernel
noncomputable def cell1370 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1370.certificate 1241 accepted1370
theorem accepted1371 : minorantGammaCheck GammaPanel1371.certificate 1242=true := by decide +kernel
noncomputable def cell1371 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1371.certificate 1242 accepted1371
theorem accepted1372 : minorantGammaCheck GammaPanel1372.certificate 1243=true := by decide +kernel
noncomputable def cell1372 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1372.certificate 1243 accepted1372
theorem accepted1373 : minorantGammaCheck GammaPanel1373.certificate 1244=true := by decide +kernel
noncomputable def cell1373 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1373.certificate 1244 accepted1373
theorem accepted1374 : minorantGammaCheck GammaPanel1374.certificate 1245=true := by decide +kernel
noncomputable def cell1374 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1374.certificate 1245 accepted1374
theorem accepted1375 : minorantGammaCheck GammaPanel1375.certificate 1246=true := by decide +kernel
noncomputable def cell1375 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1375.certificate 1246 accepted1375
noncomputable def cells : List CertifiedMinorantCell := [cell1368, cell1369, cell1370, cell1371, cell1372, cell1373, cell1374, cell1375]
theorem chainAccepted : minorantChainCheck (33/40) (829/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (33/40) (829/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0171
