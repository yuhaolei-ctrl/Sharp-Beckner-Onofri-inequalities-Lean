import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0070
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0070
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0560 : minorantGammaCheck GammaPanel0560.certificate 520=true := by decide +kernel
noncomputable def cell0560 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0560.certificate 520 accepted0560
theorem accepted0561 : minorantGammaCheck GammaPanel0561.certificate 521=true := by decide +kernel
noncomputable def cell0561 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0561.certificate 521 accepted0561
theorem accepted0562 : minorantGammaCheck GammaPanel0562.certificate 522=true := by decide +kernel
noncomputable def cell0562 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0562.certificate 522 accepted0562
theorem accepted0563 : minorantGammaCheck GammaPanel0563.certificate 523=true := by decide +kernel
noncomputable def cell0563 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0563.certificate 523 accepted0563
theorem accepted0564 : minorantGammaCheck GammaPanel0564.certificate 524=true := by decide +kernel
noncomputable def cell0564 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0564.certificate 524 accepted0564
theorem accepted0565 : minorantGammaCheck GammaPanel0565.certificate 525=true := by decide +kernel
noncomputable def cell0565 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0565.certificate 525 accepted0565
theorem accepted0566 : minorantGammaCheck GammaPanel0566.certificate 526=true := by decide +kernel
noncomputable def cell0566 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0566.certificate 526 accepted0566
theorem accepted0567 : minorantGammaCheck GammaPanel0567.certificate 527=true := by decide +kernel
noncomputable def cell0567 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0567.certificate 527 accepted0567
noncomputable def cells : List CertifiedMinorantCell := [cell0560, cell0561, cell0562, cell0563, cell0564, cell0565, cell0566, cell0567]
theorem chainAccepted : minorantChainCheck (337/2000) (1701/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (337/2000) (1701/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0070
