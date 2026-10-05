import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0206
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0206
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1648 : minorantGammaCheck GammaPanel1648.certificate 1406=true := by decide +kernel
noncomputable def cell1648 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1648.certificate 1406 accepted1648
theorem accepted1649 : minorantGammaCheck GammaPanel1649.certificate 1407=true := by decide +kernel
noncomputable def cell1649 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1649.certificate 1407 accepted1649
theorem accepted1650 : minorantGammaCheck GammaPanel1650.certificate 1408=true := by decide +kernel
noncomputable def cell1650 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1650.certificate 1408 accepted1650
theorem accepted1651 : minorantGammaCheck GammaPanel1651.certificate 1409=true := by decide +kernel
noncomputable def cell1651 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1651.certificate 1409 accepted1651
theorem accepted1652 : minorantGammaCheck GammaPanel1652.certificate 1410=true := by decide +kernel
noncomputable def cell1652 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1652.certificate 1410 accepted1652
theorem accepted1653 : minorantGammaCheck GammaPanel1653.certificate 1411=true := by decide +kernel
noncomputable def cell1653 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1653.certificate 1411 accepted1653
theorem accepted1654 : minorantGammaCheck GammaPanel1654.certificate 1412=true := by decide +kernel
noncomputable def cell1654 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1654.certificate 1412 accepted1654
theorem accepted1655 : minorantGammaCheck GammaPanel1655.certificate 1413=true := by decide +kernel
noncomputable def cell1655 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1655.certificate 1413 accepted1655
noncomputable def cells : List CertifiedMinorantCell := [cell1648, cell1649, cell1650, cell1651, cell1652, cell1653, cell1654, cell1655]
theorem chainAccepted : minorantChainCheck (857/1000) (4289/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (857/1000) (4289/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0206
