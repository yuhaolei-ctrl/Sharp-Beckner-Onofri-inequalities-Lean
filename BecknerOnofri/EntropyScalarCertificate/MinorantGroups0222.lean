module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0222

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0222
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1776 : minorantGammaCheck GammaPanel1776.certificate 1472=true := by decide +kernel
noncomputable def cell1776 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1776.certificate 1472 accepted1776
theorem accepted1777 : minorantGammaCheck GammaPanel1777.certificate 1472=true := by decide +kernel
noncomputable def cell1777 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1777.certificate 1472 accepted1777
theorem accepted1778 : minorantGammaCheck GammaPanel1778.certificate 1472=true := by decide +kernel
noncomputable def cell1778 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1778.certificate 1472 accepted1778
theorem accepted1779 : minorantGammaCheck GammaPanel1779.certificate 1472=true := by decide +kernel
noncomputable def cell1779 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1779.certificate 1472 accepted1779
theorem accepted1780 : minorantGammaCheck GammaPanel1780.certificate 1472=true := by decide +kernel
noncomputable def cell1780 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1780.certificate 1472 accepted1780
theorem accepted1781 : minorantGammaCheck GammaPanel1781.certificate 1472=true := by decide +kernel
noncomputable def cell1781 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1781.certificate 1472 accepted1781
theorem accepted1782 : minorantGammaCheck GammaPanel1782.certificate 1472=true := by decide +kernel
noncomputable def cell1782 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1782.certificate 1472 accepted1782
theorem accepted1783 : minorantGammaCheck GammaPanel1783.certificate 1472=true := by decide +kernel
noncomputable def cell1783 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1783.certificate 1472 accepted1783
noncomputable def cells : List CertifiedMinorantCell := [cell1776, cell1777, cell1778, cell1779, cell1780, cell1781, cell1782, cell1783]
theorem chainAccepted : minorantChainCheck (4349/5000) (4353/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4349/5000) (4353/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0222
