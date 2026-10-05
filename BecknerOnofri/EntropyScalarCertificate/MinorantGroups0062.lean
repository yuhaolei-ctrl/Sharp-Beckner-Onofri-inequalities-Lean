import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0062
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0062
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0496 : minorantGammaCheck GammaPanel0496.certificate 456=true := by decide +kernel
noncomputable def cell0496 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0496.certificate 456 accepted0496
theorem accepted0497 : minorantGammaCheck GammaPanel0497.certificate 457=true := by decide +kernel
noncomputable def cell0497 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0497.certificate 457 accepted0497
theorem accepted0498 : minorantGammaCheck GammaPanel0498.certificate 458=true := by decide +kernel
noncomputable def cell0498 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0498.certificate 458 accepted0498
theorem accepted0499 : minorantGammaCheck GammaPanel0499.certificate 459=true := by decide +kernel
noncomputable def cell0499 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0499.certificate 459 accepted0499
theorem accepted0500 : minorantGammaCheck GammaPanel0500.certificate 460=true := by decide +kernel
noncomputable def cell0500 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0500.certificate 460 accepted0500
theorem accepted0501 : minorantGammaCheck GammaPanel0501.certificate 461=true := by decide +kernel
noncomputable def cell0501 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0501.certificate 461 accepted0501
theorem accepted0502 : minorantGammaCheck GammaPanel0502.certificate 462=true := by decide +kernel
noncomputable def cell0502 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0502.certificate 462 accepted0502
theorem accepted0503 : minorantGammaCheck GammaPanel0503.certificate 463=true := by decide +kernel
noncomputable def cell0503 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0503.certificate 463 accepted0503
noncomputable def cells : List CertifiedMinorantCell := [cell0496, cell0497, cell0498, cell0499, cell0500, cell0501, cell0502, cell0503]
theorem chainAccepted : minorantChainCheck (1557/10000) (1573/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1557/10000) (1573/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0062
