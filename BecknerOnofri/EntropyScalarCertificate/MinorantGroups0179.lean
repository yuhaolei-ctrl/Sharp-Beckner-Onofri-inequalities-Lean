module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0179

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0179
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1432 : minorantGammaCheck GammaPanel1432.certificate 1249=true := by decide +kernel
noncomputable def cell1432 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1432.certificate 1249 accepted1432
theorem accepted1433 : minorantGammaCheck GammaPanel1433.certificate 1249=true := by decide +kernel
noncomputable def cell1433 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1433.certificate 1249 accepted1433
theorem accepted1434 : minorantGammaCheck GammaPanel1434.certificate 1249=true := by decide +kernel
noncomputable def cell1434 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1434.certificate 1249 accepted1434
theorem accepted1435 : minorantGammaCheck GammaPanel1435.certificate 1249=true := by decide +kernel
noncomputable def cell1435 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1435.certificate 1249 accepted1435
theorem accepted1436 : minorantGammaCheck GammaPanel1436.certificate 1249=true := by decide +kernel
noncomputable def cell1436 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1436.certificate 1249 accepted1436
theorem accepted1437 : minorantGammaCheck GammaPanel1437.certificate 1249=true := by decide +kernel
noncomputable def cell1437 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1437.certificate 1249 accepted1437
theorem accepted1438 : minorantGammaCheck GammaPanel1438.certificate 1249=true := by decide +kernel
noncomputable def cell1438 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1438.certificate 1249 accepted1438
theorem accepted1439 : minorantGammaCheck GammaPanel1439.certificate 1249=true := by decide +kernel
noncomputable def cell1439 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1439.certificate 1249 accepted1439
noncomputable def cells : List CertifiedMinorantCell := [cell1432, cell1433, cell1434, cell1435, cell1436, cell1437, cell1438, cell1439]
theorem chainAccepted : minorantChainCheck (4177/5000) (4181/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4177/5000) (4181/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0179
