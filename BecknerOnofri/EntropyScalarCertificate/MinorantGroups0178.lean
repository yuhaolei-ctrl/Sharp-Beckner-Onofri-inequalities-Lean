module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0178

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0178
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1424 : minorantGammaCheck GammaPanel1424.certificate 1249=true := by decide +kernel
noncomputable def cell1424 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1424.certificate 1249 accepted1424
theorem accepted1425 : minorantGammaCheck GammaPanel1425.certificate 1249=true := by decide +kernel
noncomputable def cell1425 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1425.certificate 1249 accepted1425
theorem accepted1426 : minorantGammaCheck GammaPanel1426.certificate 1249=true := by decide +kernel
noncomputable def cell1426 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1426.certificate 1249 accepted1426
theorem accepted1427 : minorantGammaCheck GammaPanel1427.certificate 1249=true := by decide +kernel
noncomputable def cell1427 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1427.certificate 1249 accepted1427
theorem accepted1428 : minorantGammaCheck GammaPanel1428.certificate 1249=true := by decide +kernel
noncomputable def cell1428 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1428.certificate 1249 accepted1428
theorem accepted1429 : minorantGammaCheck GammaPanel1429.certificate 1249=true := by decide +kernel
noncomputable def cell1429 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1429.certificate 1249 accepted1429
theorem accepted1430 : minorantGammaCheck GammaPanel1430.certificate 1249=true := by decide +kernel
noncomputable def cell1430 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1430.certificate 1249 accepted1430
theorem accepted1431 : minorantGammaCheck GammaPanel1431.certificate 1249=true := by decide +kernel
noncomputable def cell1431 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1431.certificate 1249 accepted1431
noncomputable def cells : List CertifiedMinorantCell := [cell1424, cell1425, cell1426, cell1427, cell1428, cell1429, cell1430, cell1431]
theorem chainAccepted : minorantChainCheck (4173/5000) (4177/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4173/5000) (4177/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0178
