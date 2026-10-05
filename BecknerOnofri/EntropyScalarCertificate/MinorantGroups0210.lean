module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0210

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0210
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1680 : minorantGammaCheck GammaPanel1680.certificate 1438=true := by decide +kernel
noncomputable def cell1680 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1680.certificate 1438 accepted1680
theorem accepted1681 : minorantGammaCheck GammaPanel1681.certificate 1439=true := by decide +kernel
noncomputable def cell1681 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1681.certificate 1439 accepted1681
theorem accepted1682 : minorantGammaCheck GammaPanel1682.certificate 1440=true := by decide +kernel
noncomputable def cell1682 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1682.certificate 1440 accepted1682
theorem accepted1683 : minorantGammaCheck GammaPanel1683.certificate 1441=true := by decide +kernel
noncomputable def cell1683 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1683.certificate 1441 accepted1683
theorem accepted1684 : minorantGammaCheck GammaPanel1684.certificate 1442=true := by decide +kernel
noncomputable def cell1684 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1684.certificate 1442 accepted1684
theorem accepted1685 : minorantGammaCheck GammaPanel1685.certificate 1443=true := by decide +kernel
noncomputable def cell1685 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1685.certificate 1443 accepted1685
theorem accepted1686 : minorantGammaCheck GammaPanel1686.certificate 1444=true := by decide +kernel
noncomputable def cell1686 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1686.certificate 1444 accepted1686
theorem accepted1687 : minorantGammaCheck GammaPanel1687.certificate 1445=true := by decide +kernel
noncomputable def cell1687 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1687.certificate 1445 accepted1687
noncomputable def cells : List CertifiedMinorantCell := [cell1680, cell1681, cell1682, cell1683, cell1684, cell1685, cell1686, cell1687]
theorem chainAccepted : minorantChainCheck (4301/5000) (861/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4301/5000) (861/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0210
