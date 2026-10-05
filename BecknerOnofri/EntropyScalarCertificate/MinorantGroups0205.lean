module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0205

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0205
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1640 : minorantGammaCheck GammaPanel1640.certificate 1398=true := by decide +kernel
noncomputable def cell1640 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1640.certificate 1398 accepted1640
theorem accepted1641 : minorantGammaCheck GammaPanel1641.certificate 1399=true := by decide +kernel
noncomputable def cell1641 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1641.certificate 1399 accepted1641
theorem accepted1642 : minorantGammaCheck GammaPanel1642.certificate 1400=true := by decide +kernel
noncomputable def cell1642 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1642.certificate 1400 accepted1642
theorem accepted1643 : minorantGammaCheck GammaPanel1643.certificate 1401=true := by decide +kernel
noncomputable def cell1643 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1643.certificate 1401 accepted1643
theorem accepted1644 : minorantGammaCheck GammaPanel1644.certificate 1402=true := by decide +kernel
noncomputable def cell1644 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1644.certificate 1402 accepted1644
theorem accepted1645 : minorantGammaCheck GammaPanel1645.certificate 1403=true := by decide +kernel
noncomputable def cell1645 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1645.certificate 1403 accepted1645
theorem accepted1646 : minorantGammaCheck GammaPanel1646.certificate 1404=true := by decide +kernel
noncomputable def cell1646 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1646.certificate 1404 accepted1646
theorem accepted1647 : minorantGammaCheck GammaPanel1647.certificate 1405=true := by decide +kernel
noncomputable def cell1647 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1647.certificate 1405 accepted1647
noncomputable def cells : List CertifiedMinorantCell := [cell1640, cell1641, cell1642, cell1643, cell1644, cell1645, cell1646, cell1647]
theorem chainAccepted : minorantChainCheck (4281/5000) (857/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4281/5000) (857/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0205
