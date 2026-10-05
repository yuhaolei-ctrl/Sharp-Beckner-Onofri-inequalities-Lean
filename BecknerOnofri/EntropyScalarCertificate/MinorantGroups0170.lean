module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0170

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0170
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1360 : minorantGammaCheck GammaPanel1360.certificate 1231=true := by decide +kernel
noncomputable def cell1360 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1360.certificate 1231 accepted1360
theorem accepted1361 : minorantGammaCheck GammaPanel1361.certificate 1232=true := by decide +kernel
noncomputable def cell1361 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1361.certificate 1232 accepted1361
theorem accepted1362 : minorantGammaCheck GammaPanel1362.certificate 1233=true := by decide +kernel
noncomputable def cell1362 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1362.certificate 1233 accepted1362
theorem accepted1363 : minorantGammaCheck GammaPanel1363.certificate 1234=true := by decide +kernel
noncomputable def cell1363 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1363.certificate 1234 accepted1363
theorem accepted1364 : minorantGammaCheck GammaPanel1364.certificate 1235=true := by decide +kernel
noncomputable def cell1364 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1364.certificate 1235 accepted1364
theorem accepted1365 : minorantGammaCheck GammaPanel1365.certificate 1236=true := by decide +kernel
noncomputable def cell1365 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1365.certificate 1236 accepted1365
theorem accepted1366 : minorantGammaCheck GammaPanel1366.certificate 1237=true := by decide +kernel
noncomputable def cell1366 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1366.certificate 1237 accepted1366
theorem accepted1367 : minorantGammaCheck GammaPanel1367.certificate 1238=true := by decide +kernel
noncomputable def cell1367 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1367.certificate 1238 accepted1367
noncomputable def cells : List CertifiedMinorantCell := [cell1360, cell1361, cell1362, cell1363, cell1364, cell1365, cell1366, cell1367]
theorem chainAccepted : minorantChainCheck (821/1000) (33/40) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (821/1000) (33/40) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0170
