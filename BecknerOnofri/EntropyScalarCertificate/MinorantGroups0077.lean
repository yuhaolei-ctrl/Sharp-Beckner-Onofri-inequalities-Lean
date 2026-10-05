import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0077
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0077
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0616 : minorantGammaCheck GammaPanel0616.certificate 576=true := by decide +kernel
noncomputable def cell0616 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0616.certificate 576 accepted0616
theorem accepted0617 : minorantGammaCheck GammaPanel0617.certificate 577=true := by decide +kernel
noncomputable def cell0617 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0617.certificate 577 accepted0617
theorem accepted0618 : minorantGammaCheck GammaPanel0618.certificate 578=true := by decide +kernel
noncomputable def cell0618 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0618.certificate 578 accepted0618
theorem accepted0619 : minorantGammaCheck GammaPanel0619.certificate 579=true := by decide +kernel
noncomputable def cell0619 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0619.certificate 579 accepted0619
theorem accepted0620 : minorantGammaCheck GammaPanel0620.certificate 580=true := by decide +kernel
noncomputable def cell0620 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0620.certificate 580 accepted0620
theorem accepted0621 : minorantGammaCheck GammaPanel0621.certificate 581=true := by decide +kernel
noncomputable def cell0621 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0621.certificate 581 accepted0621
theorem accepted0622 : minorantGammaCheck GammaPanel0622.certificate 582=true := by decide +kernel
noncomputable def cell0622 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0622.certificate 582 accepted0622
theorem accepted0623 : minorantGammaCheck GammaPanel0623.certificate 583=true := by decide +kernel
noncomputable def cell0623 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0623.certificate 583 accepted0623
noncomputable def cells : List CertifiedMinorantCell := [cell0616, cell0617, cell0618, cell0619, cell0620, cell0621, cell0622, cell0623]
theorem chainAccepted : minorantChainCheck (1797/10000) (1813/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1797/10000) (1813/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0077
