import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0083
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0083
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0664 : minorantGammaCheck GammaPanel0664.certificate 616=true := by decide +kernel
noncomputable def cell0664 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0664.certificate 616 accepted0664
theorem accepted0665 : minorantGammaCheck GammaPanel0665.certificate 616=true := by decide +kernel
noncomputable def cell0665 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0665.certificate 616 accepted0665
theorem accepted0666 : minorantGammaCheck GammaPanel0666.certificate 616=true := by decide +kernel
noncomputable def cell0666 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0666.certificate 616 accepted0666
theorem accepted0667 : minorantGammaCheck GammaPanel0667.certificate 616=true := by decide +kernel
noncomputable def cell0667 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0667.certificate 616 accepted0667
theorem accepted0668 : minorantGammaCheck GammaPanel0668.certificate 616=true := by decide +kernel
noncomputable def cell0668 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0668.certificate 616 accepted0668
theorem accepted0669 : minorantGammaCheck GammaPanel0669.certificate 616=true := by decide +kernel
noncomputable def cell0669 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0669.certificate 616 accepted0669
theorem accepted0670 : minorantGammaCheck GammaPanel0670.certificate 616=true := by decide +kernel
noncomputable def cell0670 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0670.certificate 616 accepted0670
theorem accepted0671 : minorantGammaCheck GammaPanel0671.certificate 616=true := by decide +kernel
noncomputable def cell0671 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0671.certificate 616 accepted0671
noncomputable def cells : List CertifiedMinorantCell := [cell0664, cell0665, cell0666, cell0667, cell0668, cell0669, cell0670, cell0671]
theorem chainAccepted : minorantChainCheck (1893/10000) (1909/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1893/10000) (1909/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0083
