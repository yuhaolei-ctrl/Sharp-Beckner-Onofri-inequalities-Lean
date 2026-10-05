import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0203
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0203
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1624 : minorantGammaCheck GammaPanel1624.certificate 1382=true := by decide +kernel
noncomputable def cell1624 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1624.certificate 1382 accepted1624
theorem accepted1625 : minorantGammaCheck GammaPanel1625.certificate 1383=true := by decide +kernel
noncomputable def cell1625 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1625.certificate 1383 accepted1625
theorem accepted1626 : minorantGammaCheck GammaPanel1626.certificate 1384=true := by decide +kernel
noncomputable def cell1626 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1626.certificate 1384 accepted1626
theorem accepted1627 : minorantGammaCheck GammaPanel1627.certificate 1385=true := by decide +kernel
noncomputable def cell1627 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1627.certificate 1385 accepted1627
theorem accepted1628 : minorantGammaCheck GammaPanel1628.certificate 1386=true := by decide +kernel
noncomputable def cell1628 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1628.certificate 1386 accepted1628
theorem accepted1629 : minorantGammaCheck GammaPanel1629.certificate 1387=true := by decide +kernel
noncomputable def cell1629 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1629.certificate 1387 accepted1629
theorem accepted1630 : minorantGammaCheck GammaPanel1630.certificate 1388=true := by decide +kernel
noncomputable def cell1630 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1630.certificate 1388 accepted1630
theorem accepted1631 : minorantGammaCheck GammaPanel1631.certificate 1389=true := by decide +kernel
noncomputable def cell1631 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1631.certificate 1389 accepted1631
noncomputable def cells : List CertifiedMinorantCell := [cell1624, cell1625, cell1626, cell1627, cell1628, cell1629, cell1630, cell1631]
theorem chainAccepted : minorantChainCheck (4273/5000) (4277/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4273/5000) (4277/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0203
