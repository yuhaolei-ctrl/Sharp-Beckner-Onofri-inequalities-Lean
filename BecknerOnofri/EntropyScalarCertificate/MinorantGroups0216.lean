module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0216

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0216
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1728 : minorantGammaCheck GammaPanel1728.certificate 1472=true := by decide +kernel
noncomputable def cell1728 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1728.certificate 1472 accepted1728
theorem accepted1729 : minorantGammaCheck GammaPanel1729.certificate 1472=true := by decide +kernel
noncomputable def cell1729 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1729.certificate 1472 accepted1729
theorem accepted1730 : minorantGammaCheck GammaPanel1730.certificate 1472=true := by decide +kernel
noncomputable def cell1730 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1730.certificate 1472 accepted1730
theorem accepted1731 : minorantGammaCheck GammaPanel1731.certificate 1472=true := by decide +kernel
noncomputable def cell1731 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1731.certificate 1472 accepted1731
theorem accepted1732 : minorantGammaCheck GammaPanel1732.certificate 1472=true := by decide +kernel
noncomputable def cell1732 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1732.certificate 1472 accepted1732
theorem accepted1733 : minorantGammaCheck GammaPanel1733.certificate 1472=true := by decide +kernel
noncomputable def cell1733 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1733.certificate 1472 accepted1733
theorem accepted1734 : minorantGammaCheck GammaPanel1734.certificate 1472=true := by decide +kernel
noncomputable def cell1734 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1734.certificate 1472 accepted1734
theorem accepted1735 : minorantGammaCheck GammaPanel1735.certificate 1472=true := by decide +kernel
noncomputable def cell1735 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1735.certificate 1472 accepted1735
noncomputable def cells : List CertifiedMinorantCell := [cell1728, cell1729, cell1730, cell1731, cell1732, cell1733, cell1734, cell1735]
theorem chainAccepted : minorantChainCheck (173/200) (4329/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (173/200) (4329/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0216
