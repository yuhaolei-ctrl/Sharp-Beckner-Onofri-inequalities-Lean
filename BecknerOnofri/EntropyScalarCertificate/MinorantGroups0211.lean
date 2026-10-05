import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0211
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0211
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1688 : minorantGammaCheck GammaPanel1688.certificate 1446=true := by decide +kernel
noncomputable def cell1688 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1688.certificate 1446 accepted1688
theorem accepted1689 : minorantGammaCheck GammaPanel1689.certificate 1447=true := by decide +kernel
noncomputable def cell1689 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1689.certificate 1447 accepted1689
theorem accepted1690 : minorantGammaCheck GammaPanel1690.certificate 1448=true := by decide +kernel
noncomputable def cell1690 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1690.certificate 1448 accepted1690
theorem accepted1691 : minorantGammaCheck GammaPanel1691.certificate 1449=true := by decide +kernel
noncomputable def cell1691 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1691.certificate 1449 accepted1691
theorem accepted1692 : minorantGammaCheck GammaPanel1692.certificate 1450=true := by decide +kernel
noncomputable def cell1692 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1692.certificate 1450 accepted1692
theorem accepted1693 : minorantGammaCheck GammaPanel1693.certificate 1451=true := by decide +kernel
noncomputable def cell1693 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1693.certificate 1451 accepted1693
theorem accepted1694 : minorantGammaCheck GammaPanel1694.certificate 1452=true := by decide +kernel
noncomputable def cell1694 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1694.certificate 1452 accepted1694
theorem accepted1695 : minorantGammaCheck GammaPanel1695.certificate 1453=true := by decide +kernel
noncomputable def cell1695 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1695.certificate 1453 accepted1695
noncomputable def cells : List CertifiedMinorantCell := [cell1688, cell1689, cell1690, cell1691, cell1692, cell1693, cell1694, cell1695]
theorem chainAccepted : minorantChainCheck (861/1000) (4309/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (861/1000) (4309/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0211
