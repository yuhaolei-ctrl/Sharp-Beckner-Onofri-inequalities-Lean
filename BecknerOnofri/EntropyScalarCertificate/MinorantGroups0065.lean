import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0065
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0065
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0520 : minorantGammaCheck GammaPanel0520.certificate 480=true := by decide +kernel
noncomputable def cell0520 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0520.certificate 480 accepted0520
theorem accepted0521 : minorantGammaCheck GammaPanel0521.certificate 481=true := by decide +kernel
noncomputable def cell0521 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0521.certificate 481 accepted0521
theorem accepted0522 : minorantGammaCheck GammaPanel0522.certificate 482=true := by decide +kernel
noncomputable def cell0522 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0522.certificate 482 accepted0522
theorem accepted0523 : minorantGammaCheck GammaPanel0523.certificate 483=true := by decide +kernel
noncomputable def cell0523 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0523.certificate 483 accepted0523
theorem accepted0524 : minorantGammaCheck GammaPanel0524.certificate 484=true := by decide +kernel
noncomputable def cell0524 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0524.certificate 484 accepted0524
theorem accepted0525 : minorantGammaCheck GammaPanel0525.certificate 485=true := by decide +kernel
noncomputable def cell0525 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0525.certificate 485 accepted0525
theorem accepted0526 : minorantGammaCheck GammaPanel0526.certificate 486=true := by decide +kernel
noncomputable def cell0526 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0526.certificate 486 accepted0526
theorem accepted0527 : minorantGammaCheck GammaPanel0527.certificate 487=true := by decide +kernel
noncomputable def cell0527 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0527.certificate 487 accepted0527
noncomputable def cells : List CertifiedMinorantCell := [cell0520, cell0521, cell0522, cell0523, cell0524, cell0525, cell0526, cell0527]
theorem chainAccepted : minorantChainCheck (321/2000) (1621/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (321/2000) (1621/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0065
