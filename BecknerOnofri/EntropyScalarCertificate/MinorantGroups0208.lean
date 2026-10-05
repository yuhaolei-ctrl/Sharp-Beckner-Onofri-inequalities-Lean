module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0208

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0208
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1664 : minorantGammaCheck GammaPanel1664.certificate 1422=true := by decide +kernel
noncomputable def cell1664 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1664.certificate 1422 accepted1664
theorem accepted1665 : minorantGammaCheck GammaPanel1665.certificate 1423=true := by decide +kernel
noncomputable def cell1665 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1665.certificate 1423 accepted1665
theorem accepted1666 : minorantGammaCheck GammaPanel1666.certificate 1424=true := by decide +kernel
noncomputable def cell1666 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1666.certificate 1424 accepted1666
theorem accepted1667 : minorantGammaCheck GammaPanel1667.certificate 1425=true := by decide +kernel
noncomputable def cell1667 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1667.certificate 1425 accepted1667
theorem accepted1668 : minorantGammaCheck GammaPanel1668.certificate 1426=true := by decide +kernel
noncomputable def cell1668 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1668.certificate 1426 accepted1668
theorem accepted1669 : minorantGammaCheck GammaPanel1669.certificate 1427=true := by decide +kernel
noncomputable def cell1669 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1669.certificate 1427 accepted1669
theorem accepted1670 : minorantGammaCheck GammaPanel1670.certificate 1428=true := by decide +kernel
noncomputable def cell1670 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1670.certificate 1428 accepted1670
theorem accepted1671 : minorantGammaCheck GammaPanel1671.certificate 1429=true := by decide +kernel
noncomputable def cell1671 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1671.certificate 1429 accepted1671
noncomputable def cells : List CertifiedMinorantCell := [cell1664, cell1665, cell1666, cell1667, cell1668, cell1669, cell1670, cell1671]
theorem chainAccepted : minorantChainCheck (4293/5000) (4297/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4293/5000) (4297/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0208
