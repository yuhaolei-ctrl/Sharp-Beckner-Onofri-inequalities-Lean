module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0195

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0195
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1560 : minorantGammaCheck GammaPanel1560.certificate 1318=true := by decide +kernel
noncomputable def cell1560 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1560.certificate 1318 accepted1560
theorem accepted1561 : minorantGammaCheck GammaPanel1561.certificate 1319=true := by decide +kernel
noncomputable def cell1561 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1561.certificate 1319 accepted1561
theorem accepted1562 : minorantGammaCheck GammaPanel1562.certificate 1320=true := by decide +kernel
noncomputable def cell1562 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1562.certificate 1320 accepted1562
theorem accepted1563 : minorantGammaCheck GammaPanel1563.certificate 1321=true := by decide +kernel
noncomputable def cell1563 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1563.certificate 1321 accepted1563
theorem accepted1564 : minorantGammaCheck GammaPanel1564.certificate 1322=true := by decide +kernel
noncomputable def cell1564 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1564.certificate 1322 accepted1564
theorem accepted1565 : minorantGammaCheck GammaPanel1565.certificate 1323=true := by decide +kernel
noncomputable def cell1565 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1565.certificate 1323 accepted1565
theorem accepted1566 : minorantGammaCheck GammaPanel1566.certificate 1324=true := by decide +kernel
noncomputable def cell1566 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1566.certificate 1324 accepted1566
theorem accepted1567 : minorantGammaCheck GammaPanel1567.certificate 1325=true := by decide +kernel
noncomputable def cell1567 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1567.certificate 1325 accepted1567
noncomputable def cells : List CertifiedMinorantCell := [cell1560, cell1561, cell1562, cell1563, cell1564, cell1565, cell1566, cell1567]
theorem chainAccepted : minorantChainCheck (4241/5000) (849/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4241/5000) (849/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0195
