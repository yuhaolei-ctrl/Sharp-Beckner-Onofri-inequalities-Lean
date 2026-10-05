module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0186

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0186
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1488 : minorantGammaCheck GammaPanel1488.certificate 1249=true := by decide +kernel
noncomputable def cell1488 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1488.certificate 1249 accepted1488
theorem accepted1489 : minorantGammaCheck GammaPanel1489.certificate 1249=true := by decide +kernel
noncomputable def cell1489 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1489.certificate 1249 accepted1489
theorem accepted1490 : minorantGammaCheck GammaPanel1490.certificate 1249=true := by decide +kernel
noncomputable def cell1490 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1490.certificate 1249 accepted1490
theorem accepted1491 : minorantGammaCheck GammaPanel1491.certificate 1249=true := by decide +kernel
noncomputable def cell1491 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1491.certificate 1249 accepted1491
theorem accepted1492 : minorantGammaCheck GammaPanel1492.certificate 1250=true := by decide +kernel
noncomputable def cell1492 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1492.certificate 1250 accepted1492
theorem accepted1493 : minorantGammaCheck GammaPanel1493.certificate 1251=true := by decide +kernel
noncomputable def cell1493 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1493.certificate 1251 accepted1493
theorem accepted1494 : minorantGammaCheck GammaPanel1494.certificate 1252=true := by decide +kernel
noncomputable def cell1494 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1494.certificate 1252 accepted1494
theorem accepted1495 : minorantGammaCheck GammaPanel1495.certificate 1253=true := by decide +kernel
noncomputable def cell1495 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1495.certificate 1253 accepted1495
noncomputable def cells : List CertifiedMinorantCell := [cell1488, cell1489, cell1490, cell1491, cell1492, cell1493, cell1494, cell1495]
theorem chainAccepted : minorantChainCheck (841/1000) (4209/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (841/1000) (4209/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0186
