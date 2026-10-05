module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0207

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0207
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1656 : minorantGammaCheck GammaPanel1656.certificate 1414=true := by decide +kernel
noncomputable def cell1656 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1656.certificate 1414 accepted1656
theorem accepted1657 : minorantGammaCheck GammaPanel1657.certificate 1415=true := by decide +kernel
noncomputable def cell1657 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1657.certificate 1415 accepted1657
theorem accepted1658 : minorantGammaCheck GammaPanel1658.certificate 1416=true := by decide +kernel
noncomputable def cell1658 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1658.certificate 1416 accepted1658
theorem accepted1659 : minorantGammaCheck GammaPanel1659.certificate 1417=true := by decide +kernel
noncomputable def cell1659 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1659.certificate 1417 accepted1659
theorem accepted1660 : minorantGammaCheck GammaPanel1660.certificate 1418=true := by decide +kernel
noncomputable def cell1660 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1660.certificate 1418 accepted1660
theorem accepted1661 : minorantGammaCheck GammaPanel1661.certificate 1419=true := by decide +kernel
noncomputable def cell1661 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1661.certificate 1419 accepted1661
theorem accepted1662 : minorantGammaCheck GammaPanel1662.certificate 1420=true := by decide +kernel
noncomputable def cell1662 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1662.certificate 1420 accepted1662
theorem accepted1663 : minorantGammaCheck GammaPanel1663.certificate 1421=true := by decide +kernel
noncomputable def cell1663 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1663.certificate 1421 accepted1663
noncomputable def cells : List CertifiedMinorantCell := [cell1656, cell1657, cell1658, cell1659, cell1660, cell1661, cell1662, cell1663]
theorem chainAccepted : minorantChainCheck (4289/5000) (4293/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4289/5000) (4293/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0207
