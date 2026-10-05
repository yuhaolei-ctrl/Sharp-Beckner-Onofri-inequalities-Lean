import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0066
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0066
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0528 : minorantGammaCheck GammaPanel0528.certificate 488=true := by decide +kernel
noncomputable def cell0528 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0528.certificate 488 accepted0528
theorem accepted0529 : minorantGammaCheck GammaPanel0529.certificate 489=true := by decide +kernel
noncomputable def cell0529 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0529.certificate 489 accepted0529
theorem accepted0530 : minorantGammaCheck GammaPanel0530.certificate 490=true := by decide +kernel
noncomputable def cell0530 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0530.certificate 490 accepted0530
theorem accepted0531 : minorantGammaCheck GammaPanel0531.certificate 491=true := by decide +kernel
noncomputable def cell0531 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0531.certificate 491 accepted0531
theorem accepted0532 : minorantGammaCheck GammaPanel0532.certificate 492=true := by decide +kernel
noncomputable def cell0532 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0532.certificate 492 accepted0532
theorem accepted0533 : minorantGammaCheck GammaPanel0533.certificate 493=true := by decide +kernel
noncomputable def cell0533 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0533.certificate 493 accepted0533
theorem accepted0534 : minorantGammaCheck GammaPanel0534.certificate 494=true := by decide +kernel
noncomputable def cell0534 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0534.certificate 494 accepted0534
theorem accepted0535 : minorantGammaCheck GammaPanel0535.certificate 495=true := by decide +kernel
noncomputable def cell0535 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0535.certificate 495 accepted0535
noncomputable def cells : List CertifiedMinorantCell := [cell0528, cell0529, cell0530, cell0531, cell0532, cell0533, cell0534, cell0535]
theorem chainAccepted : minorantChainCheck (1621/10000) (1637/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1621/10000) (1637/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0066
