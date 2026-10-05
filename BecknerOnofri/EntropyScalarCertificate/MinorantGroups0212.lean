import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0212
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0212
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1696 : minorantGammaCheck GammaPanel1696.certificate 1454=true := by decide +kernel
noncomputable def cell1696 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1696.certificate 1454 accepted1696
theorem accepted1697 : minorantGammaCheck GammaPanel1697.certificate 1455=true := by decide +kernel
noncomputable def cell1697 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1697.certificate 1455 accepted1697
theorem accepted1698 : minorantGammaCheck GammaPanel1698.certificate 1456=true := by decide +kernel
noncomputable def cell1698 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1698.certificate 1456 accepted1698
theorem accepted1699 : minorantGammaCheck GammaPanel1699.certificate 1457=true := by decide +kernel
noncomputable def cell1699 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1699.certificate 1457 accepted1699
theorem accepted1700 : minorantGammaCheck GammaPanel1700.certificate 1458=true := by decide +kernel
noncomputable def cell1700 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1700.certificate 1458 accepted1700
theorem accepted1701 : minorantGammaCheck GammaPanel1701.certificate 1459=true := by decide +kernel
noncomputable def cell1701 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1701.certificate 1459 accepted1701
theorem accepted1702 : minorantGammaCheck GammaPanel1702.certificate 1460=true := by decide +kernel
noncomputable def cell1702 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1702.certificate 1460 accepted1702
theorem accepted1703 : minorantGammaCheck GammaPanel1703.certificate 1461=true := by decide +kernel
noncomputable def cell1703 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1703.certificate 1461 accepted1703
noncomputable def cells : List CertifiedMinorantCell := [cell1696, cell1697, cell1698, cell1699, cell1700, cell1701, cell1702, cell1703]
theorem chainAccepted : minorantChainCheck (4309/5000) (4313/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4309/5000) (4313/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0212
