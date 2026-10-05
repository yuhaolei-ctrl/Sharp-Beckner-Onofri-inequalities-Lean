import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0072
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0072
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0576 : minorantGammaCheck GammaPanel0576.certificate 536=true := by decide +kernel
noncomputable def cell0576 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0576.certificate 536 accepted0576
theorem accepted0577 : minorantGammaCheck GammaPanel0577.certificate 537=true := by decide +kernel
noncomputable def cell0577 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0577.certificate 537 accepted0577
theorem accepted0578 : minorantGammaCheck GammaPanel0578.certificate 538=true := by decide +kernel
noncomputable def cell0578 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0578.certificate 538 accepted0578
theorem accepted0579 : minorantGammaCheck GammaPanel0579.certificate 539=true := by decide +kernel
noncomputable def cell0579 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0579.certificate 539 accepted0579
theorem accepted0580 : minorantGammaCheck GammaPanel0580.certificate 540=true := by decide +kernel
noncomputable def cell0580 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0580.certificate 540 accepted0580
theorem accepted0581 : minorantGammaCheck GammaPanel0581.certificate 541=true := by decide +kernel
noncomputable def cell0581 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0581.certificate 541 accepted0581
theorem accepted0582 : minorantGammaCheck GammaPanel0582.certificate 542=true := by decide +kernel
noncomputable def cell0582 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0582.certificate 542 accepted0582
theorem accepted0583 : minorantGammaCheck GammaPanel0583.certificate 543=true := by decide +kernel
noncomputable def cell0583 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0583.certificate 543 accepted0583
noncomputable def cells : List CertifiedMinorantCell := [cell0576, cell0577, cell0578, cell0579, cell0580, cell0581, cell0582, cell0583]
theorem chainAccepted : minorantChainCheck (1717/10000) (1733/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1717/10000) (1733/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0072
