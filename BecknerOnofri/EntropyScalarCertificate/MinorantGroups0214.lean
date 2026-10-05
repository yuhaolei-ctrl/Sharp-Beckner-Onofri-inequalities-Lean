import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0214
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0214
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1712 : minorantGammaCheck GammaPanel1712.certificate 1470=true := by decide +kernel
noncomputable def cell1712 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1712.certificate 1470 accepted1712
theorem accepted1713 : minorantGammaCheck GammaPanel1713.certificate 1471=true := by decide +kernel
noncomputable def cell1713 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1713.certificate 1471 accepted1713
theorem accepted1714 : minorantGammaCheck GammaPanel1714.certificate 1472=true := by decide +kernel
noncomputable def cell1714 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1714.certificate 1472 accepted1714
theorem accepted1715 : minorantGammaCheck GammaPanel1715.certificate 1472=true := by decide +kernel
noncomputable def cell1715 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1715.certificate 1472 accepted1715
theorem accepted1716 : minorantGammaCheck GammaPanel1716.certificate 1472=true := by decide +kernel
noncomputable def cell1716 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1716.certificate 1472 accepted1716
theorem accepted1717 : minorantGammaCheck GammaPanel1717.certificate 1472=true := by decide +kernel
noncomputable def cell1717 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1717.certificate 1472 accepted1717
theorem accepted1718 : minorantGammaCheck GammaPanel1718.certificate 1472=true := by decide +kernel
noncomputable def cell1718 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1718.certificate 1472 accepted1718
theorem accepted1719 : minorantGammaCheck GammaPanel1719.certificate 1472=true := by decide +kernel
noncomputable def cell1719 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1719.certificate 1472 accepted1719
noncomputable def cells : List CertifiedMinorantCell := [cell1712, cell1713, cell1714, cell1715, cell1716, cell1717, cell1718, cell1719]
theorem chainAccepted : minorantChainCheck (4317/5000) (4321/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4317/5000) (4321/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0214
