import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0068
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0068
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0544 : minorantGammaCheck GammaPanel0544.certificate 504=true := by decide +kernel
noncomputable def cell0544 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0544.certificate 504 accepted0544
theorem accepted0545 : minorantGammaCheck GammaPanel0545.certificate 505=true := by decide +kernel
noncomputable def cell0545 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0545.certificate 505 accepted0545
theorem accepted0546 : minorantGammaCheck GammaPanel0546.certificate 506=true := by decide +kernel
noncomputable def cell0546 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0546.certificate 506 accepted0546
theorem accepted0547 : minorantGammaCheck GammaPanel0547.certificate 507=true := by decide +kernel
noncomputable def cell0547 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0547.certificate 507 accepted0547
theorem accepted0548 : minorantGammaCheck GammaPanel0548.certificate 508=true := by decide +kernel
noncomputable def cell0548 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0548.certificate 508 accepted0548
theorem accepted0549 : minorantGammaCheck GammaPanel0549.certificate 509=true := by decide +kernel
noncomputable def cell0549 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0549.certificate 509 accepted0549
theorem accepted0550 : minorantGammaCheck GammaPanel0550.certificate 510=true := by decide +kernel
noncomputable def cell0550 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0550.certificate 510 accepted0550
theorem accepted0551 : minorantGammaCheck GammaPanel0551.certificate 511=true := by decide +kernel
noncomputable def cell0551 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0551.certificate 511 accepted0551
noncomputable def cells : List CertifiedMinorantCell := [cell0544, cell0545, cell0546, cell0547, cell0548, cell0549, cell0550, cell0551]
theorem chainAccepted : minorantChainCheck (1653/10000) (1669/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1653/10000) (1669/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0068
