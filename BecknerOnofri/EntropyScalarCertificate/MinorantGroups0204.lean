module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0204

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0204
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1632 : minorantGammaCheck GammaPanel1632.certificate 1390=true := by decide +kernel
noncomputable def cell1632 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1632.certificate 1390 accepted1632
theorem accepted1633 : minorantGammaCheck GammaPanel1633.certificate 1391=true := by decide +kernel
noncomputable def cell1633 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1633.certificate 1391 accepted1633
theorem accepted1634 : minorantGammaCheck GammaPanel1634.certificate 1392=true := by decide +kernel
noncomputable def cell1634 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1634.certificate 1392 accepted1634
theorem accepted1635 : minorantGammaCheck GammaPanel1635.certificate 1393=true := by decide +kernel
noncomputable def cell1635 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1635.certificate 1393 accepted1635
theorem accepted1636 : minorantGammaCheck GammaPanel1636.certificate 1394=true := by decide +kernel
noncomputable def cell1636 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1636.certificate 1394 accepted1636
theorem accepted1637 : minorantGammaCheck GammaPanel1637.certificate 1395=true := by decide +kernel
noncomputable def cell1637 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1637.certificate 1395 accepted1637
theorem accepted1638 : minorantGammaCheck GammaPanel1638.certificate 1396=true := by decide +kernel
noncomputable def cell1638 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1638.certificate 1396 accepted1638
theorem accepted1639 : minorantGammaCheck GammaPanel1639.certificate 1397=true := by decide +kernel
noncomputable def cell1639 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1639.certificate 1397 accepted1639
noncomputable def cells : List CertifiedMinorantCell := [cell1632, cell1633, cell1634, cell1635, cell1636, cell1637, cell1638, cell1639]
theorem chainAccepted : minorantChainCheck (4277/5000) (4281/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4277/5000) (4281/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0204
