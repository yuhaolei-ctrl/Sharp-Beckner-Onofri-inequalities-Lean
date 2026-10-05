module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0202

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0202
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1616 : minorantGammaCheck GammaPanel1616.certificate 1374=true := by decide +kernel
noncomputable def cell1616 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1616.certificate 1374 accepted1616
theorem accepted1617 : minorantGammaCheck GammaPanel1617.certificate 1375=true := by decide +kernel
noncomputable def cell1617 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1617.certificate 1375 accepted1617
theorem accepted1618 : minorantGammaCheck GammaPanel1618.certificate 1376=true := by decide +kernel
noncomputable def cell1618 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1618.certificate 1376 accepted1618
theorem accepted1619 : minorantGammaCheck GammaPanel1619.certificate 1377=true := by decide +kernel
noncomputable def cell1619 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1619.certificate 1377 accepted1619
theorem accepted1620 : minorantGammaCheck GammaPanel1620.certificate 1378=true := by decide +kernel
noncomputable def cell1620 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1620.certificate 1378 accepted1620
theorem accepted1621 : minorantGammaCheck GammaPanel1621.certificate 1379=true := by decide +kernel
noncomputable def cell1621 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1621.certificate 1379 accepted1621
theorem accepted1622 : minorantGammaCheck GammaPanel1622.certificate 1380=true := by decide +kernel
noncomputable def cell1622 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1622.certificate 1380 accepted1622
theorem accepted1623 : minorantGammaCheck GammaPanel1623.certificate 1381=true := by decide +kernel
noncomputable def cell1623 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1623.certificate 1381 accepted1623
noncomputable def cells : List CertifiedMinorantCell := [cell1616, cell1617, cell1618, cell1619, cell1620, cell1621, cell1622, cell1623]
theorem chainAccepted : minorantChainCheck (4269/5000) (4273/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4269/5000) (4273/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0202
