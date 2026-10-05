module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0182

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0182
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1456 : minorantGammaCheck GammaPanel1456.certificate 1249=true := by decide +kernel
noncomputable def cell1456 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1456.certificate 1249 accepted1456
theorem accepted1457 : minorantGammaCheck GammaPanel1457.certificate 1249=true := by decide +kernel
noncomputable def cell1457 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1457.certificate 1249 accepted1457
theorem accepted1458 : minorantGammaCheck GammaPanel1458.certificate 1249=true := by decide +kernel
noncomputable def cell1458 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1458.certificate 1249 accepted1458
theorem accepted1459 : minorantGammaCheck GammaPanel1459.certificate 1249=true := by decide +kernel
noncomputable def cell1459 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1459.certificate 1249 accepted1459
theorem accepted1460 : minorantGammaCheck GammaPanel1460.certificate 1249=true := by decide +kernel
noncomputable def cell1460 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1460.certificate 1249 accepted1460
theorem accepted1461 : minorantGammaCheck GammaPanel1461.certificate 1249=true := by decide +kernel
noncomputable def cell1461 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1461.certificate 1249 accepted1461
theorem accepted1462 : minorantGammaCheck GammaPanel1462.certificate 1249=true := by decide +kernel
noncomputable def cell1462 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1462.certificate 1249 accepted1462
theorem accepted1463 : minorantGammaCheck GammaPanel1463.certificate 1249=true := by decide +kernel
noncomputable def cell1463 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1463.certificate 1249 accepted1463
noncomputable def cells : List CertifiedMinorantCell := [cell1456, cell1457, cell1458, cell1459, cell1460, cell1461, cell1462, cell1463]
theorem chainAccepted : minorantChainCheck (4189/5000) (4193/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4189/5000) (4193/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0182
