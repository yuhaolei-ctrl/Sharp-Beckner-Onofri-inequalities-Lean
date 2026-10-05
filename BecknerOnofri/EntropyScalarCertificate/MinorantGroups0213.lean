import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0213
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0213
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1704 : minorantGammaCheck GammaPanel1704.certificate 1462=true := by decide +kernel
noncomputable def cell1704 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1704.certificate 1462 accepted1704
theorem accepted1705 : minorantGammaCheck GammaPanel1705.certificate 1463=true := by decide +kernel
noncomputable def cell1705 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1705.certificate 1463 accepted1705
theorem accepted1706 : minorantGammaCheck GammaPanel1706.certificate 1464=true := by decide +kernel
noncomputable def cell1706 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1706.certificate 1464 accepted1706
theorem accepted1707 : minorantGammaCheck GammaPanel1707.certificate 1465=true := by decide +kernel
noncomputable def cell1707 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1707.certificate 1465 accepted1707
theorem accepted1708 : minorantGammaCheck GammaPanel1708.certificate 1466=true := by decide +kernel
noncomputable def cell1708 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1708.certificate 1466 accepted1708
theorem accepted1709 : minorantGammaCheck GammaPanel1709.certificate 1467=true := by decide +kernel
noncomputable def cell1709 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1709.certificate 1467 accepted1709
theorem accepted1710 : minorantGammaCheck GammaPanel1710.certificate 1468=true := by decide +kernel
noncomputable def cell1710 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1710.certificate 1468 accepted1710
theorem accepted1711 : minorantGammaCheck GammaPanel1711.certificate 1469=true := by decide +kernel
noncomputable def cell1711 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1711.certificate 1469 accepted1711
noncomputable def cells : List CertifiedMinorantCell := [cell1704, cell1705, cell1706, cell1707, cell1708, cell1709, cell1710, cell1711]
theorem chainAccepted : minorantChainCheck (4313/5000) (4317/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4313/5000) (4317/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0213
