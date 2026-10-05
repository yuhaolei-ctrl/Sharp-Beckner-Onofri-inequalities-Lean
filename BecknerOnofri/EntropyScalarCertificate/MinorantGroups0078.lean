import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0078
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0078
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0624 : minorantGammaCheck GammaPanel0624.certificate 584=true := by decide +kernel
noncomputable def cell0624 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0624.certificate 584 accepted0624
theorem accepted0625 : minorantGammaCheck GammaPanel0625.certificate 585=true := by decide +kernel
noncomputable def cell0625 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0625.certificate 585 accepted0625
theorem accepted0626 : minorantGammaCheck GammaPanel0626.certificate 586=true := by decide +kernel
noncomputable def cell0626 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0626.certificate 586 accepted0626
theorem accepted0627 : minorantGammaCheck GammaPanel0627.certificate 587=true := by decide +kernel
noncomputable def cell0627 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0627.certificate 587 accepted0627
theorem accepted0628 : minorantGammaCheck GammaPanel0628.certificate 588=true := by decide +kernel
noncomputable def cell0628 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0628.certificate 588 accepted0628
theorem accepted0629 : minorantGammaCheck GammaPanel0629.certificate 589=true := by decide +kernel
noncomputable def cell0629 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0629.certificate 589 accepted0629
theorem accepted0630 : minorantGammaCheck GammaPanel0630.certificate 590=true := by decide +kernel
noncomputable def cell0630 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0630.certificate 590 accepted0630
theorem accepted0631 : minorantGammaCheck GammaPanel0631.certificate 591=true := by decide +kernel
noncomputable def cell0631 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0631.certificate 591 accepted0631
noncomputable def cells : List CertifiedMinorantCell := [cell0624, cell0625, cell0626, cell0627, cell0628, cell0629, cell0630, cell0631]
theorem chainAccepted : minorantChainCheck (1813/10000) (1829/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1813/10000) (1829/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0078
