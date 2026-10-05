import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0075
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0075
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0600 : minorantGammaCheck GammaPanel0600.certificate 560=true := by decide +kernel
noncomputable def cell0600 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0600.certificate 560 accepted0600
theorem accepted0601 : minorantGammaCheck GammaPanel0601.certificate 561=true := by decide +kernel
noncomputable def cell0601 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0601.certificate 561 accepted0601
theorem accepted0602 : minorantGammaCheck GammaPanel0602.certificate 562=true := by decide +kernel
noncomputable def cell0602 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0602.certificate 562 accepted0602
theorem accepted0603 : minorantGammaCheck GammaPanel0603.certificate 563=true := by decide +kernel
noncomputable def cell0603 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0603.certificate 563 accepted0603
theorem accepted0604 : minorantGammaCheck GammaPanel0604.certificate 564=true := by decide +kernel
noncomputable def cell0604 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0604.certificate 564 accepted0604
theorem accepted0605 : minorantGammaCheck GammaPanel0605.certificate 565=true := by decide +kernel
noncomputable def cell0605 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0605.certificate 565 accepted0605
theorem accepted0606 : minorantGammaCheck GammaPanel0606.certificate 566=true := by decide +kernel
noncomputable def cell0606 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0606.certificate 566 accepted0606
theorem accepted0607 : minorantGammaCheck GammaPanel0607.certificate 567=true := by decide +kernel
noncomputable def cell0607 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0607.certificate 567 accepted0607
noncomputable def cells : List CertifiedMinorantCell := [cell0600, cell0601, cell0602, cell0603, cell0604, cell0605, cell0606, cell0607]
theorem chainAccepted : minorantChainCheck (353/2000) (1781/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (353/2000) (1781/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0075
