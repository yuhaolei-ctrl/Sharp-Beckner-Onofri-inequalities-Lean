import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0081
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0081
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0648 : minorantGammaCheck GammaPanel0648.certificate 608=true := by decide +kernel
noncomputable def cell0648 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0648.certificate 608 accepted0648
theorem accepted0649 : minorantGammaCheck GammaPanel0649.certificate 609=true := by decide +kernel
noncomputable def cell0649 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0649.certificate 609 accepted0649
theorem accepted0650 : minorantGammaCheck GammaPanel0650.certificate 610=true := by decide +kernel
noncomputable def cell0650 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0650.certificate 610 accepted0650
theorem accepted0651 : minorantGammaCheck GammaPanel0651.certificate 611=true := by decide +kernel
noncomputable def cell0651 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0651.certificate 611 accepted0651
theorem accepted0652 : minorantGammaCheck GammaPanel0652.certificate 612=true := by decide +kernel
noncomputable def cell0652 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0652.certificate 612 accepted0652
theorem accepted0653 : minorantGammaCheck GammaPanel0653.certificate 613=true := by decide +kernel
noncomputable def cell0653 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0653.certificate 613 accepted0653
theorem accepted0654 : minorantGammaCheck GammaPanel0654.certificate 614=true := by decide +kernel
noncomputable def cell0654 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0654.certificate 614 accepted0654
theorem accepted0655 : minorantGammaCheck GammaPanel0655.certificate 615=true := by decide +kernel
noncomputable def cell0655 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0655.certificate 615 accepted0655
noncomputable def cells : List CertifiedMinorantCell := [cell0648, cell0649, cell0650, cell0651, cell0652, cell0653, cell0654, cell0655]
theorem chainAccepted : minorantChainCheck (1861/10000) (1877/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1861/10000) (1877/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0081
