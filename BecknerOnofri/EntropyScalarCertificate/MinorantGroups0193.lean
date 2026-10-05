module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0193

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0193
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1544 : minorantGammaCheck GammaPanel1544.certificate 1302=true := by decide +kernel
noncomputable def cell1544 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1544.certificate 1302 accepted1544
theorem accepted1545 : minorantGammaCheck GammaPanel1545.certificate 1303=true := by decide +kernel
noncomputable def cell1545 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1545.certificate 1303 accepted1545
theorem accepted1546 : minorantGammaCheck GammaPanel1546.certificate 1304=true := by decide +kernel
noncomputable def cell1546 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1546.certificate 1304 accepted1546
theorem accepted1547 : minorantGammaCheck GammaPanel1547.certificate 1305=true := by decide +kernel
noncomputable def cell1547 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1547.certificate 1305 accepted1547
theorem accepted1548 : minorantGammaCheck GammaPanel1548.certificate 1306=true := by decide +kernel
noncomputable def cell1548 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1548.certificate 1306 accepted1548
theorem accepted1549 : minorantGammaCheck GammaPanel1549.certificate 1307=true := by decide +kernel
noncomputable def cell1549 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1549.certificate 1307 accepted1549
theorem accepted1550 : minorantGammaCheck GammaPanel1550.certificate 1308=true := by decide +kernel
noncomputable def cell1550 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1550.certificate 1308 accepted1550
theorem accepted1551 : minorantGammaCheck GammaPanel1551.certificate 1309=true := by decide +kernel
noncomputable def cell1551 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1551.certificate 1309 accepted1551
noncomputable def cells : List CertifiedMinorantCell := [cell1544, cell1545, cell1546, cell1547, cell1548, cell1549, cell1550, cell1551]
theorem chainAccepted : minorantChainCheck (4233/5000) (4237/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4233/5000) (4237/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0193
