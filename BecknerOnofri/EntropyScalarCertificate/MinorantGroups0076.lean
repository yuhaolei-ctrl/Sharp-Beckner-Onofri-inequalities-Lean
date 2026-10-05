import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0076
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0076
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0608 : minorantGammaCheck GammaPanel0608.certificate 568=true := by decide +kernel
noncomputable def cell0608 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0608.certificate 568 accepted0608
theorem accepted0609 : minorantGammaCheck GammaPanel0609.certificate 569=true := by decide +kernel
noncomputable def cell0609 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0609.certificate 569 accepted0609
theorem accepted0610 : minorantGammaCheck GammaPanel0610.certificate 570=true := by decide +kernel
noncomputable def cell0610 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0610.certificate 570 accepted0610
theorem accepted0611 : minorantGammaCheck GammaPanel0611.certificate 571=true := by decide +kernel
noncomputable def cell0611 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0611.certificate 571 accepted0611
theorem accepted0612 : minorantGammaCheck GammaPanel0612.certificate 572=true := by decide +kernel
noncomputable def cell0612 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0612.certificate 572 accepted0612
theorem accepted0613 : minorantGammaCheck GammaPanel0613.certificate 573=true := by decide +kernel
noncomputable def cell0613 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0613.certificate 573 accepted0613
theorem accepted0614 : minorantGammaCheck GammaPanel0614.certificate 574=true := by decide +kernel
noncomputable def cell0614 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0614.certificate 574 accepted0614
theorem accepted0615 : minorantGammaCheck GammaPanel0615.certificate 575=true := by decide +kernel
noncomputable def cell0615 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0615.certificate 575 accepted0615
noncomputable def cells : List CertifiedMinorantCell := [cell0608, cell0609, cell0610, cell0611, cell0612, cell0613, cell0614, cell0615]
theorem chainAccepted : minorantChainCheck (1781/10000) (1797/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1781/10000) (1797/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0076
