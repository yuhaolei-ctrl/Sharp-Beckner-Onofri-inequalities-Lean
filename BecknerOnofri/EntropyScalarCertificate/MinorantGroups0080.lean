import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0080
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0080
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0640 : minorantGammaCheck GammaPanel0640.certificate 600=true := by decide +kernel
noncomputable def cell0640 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0640.certificate 600 accepted0640
theorem accepted0641 : minorantGammaCheck GammaPanel0641.certificate 601=true := by decide +kernel
noncomputable def cell0641 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0641.certificate 601 accepted0641
theorem accepted0642 : minorantGammaCheck GammaPanel0642.certificate 602=true := by decide +kernel
noncomputable def cell0642 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0642.certificate 602 accepted0642
theorem accepted0643 : minorantGammaCheck GammaPanel0643.certificate 603=true := by decide +kernel
noncomputable def cell0643 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0643.certificate 603 accepted0643
theorem accepted0644 : minorantGammaCheck GammaPanel0644.certificate 604=true := by decide +kernel
noncomputable def cell0644 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0644.certificate 604 accepted0644
theorem accepted0645 : minorantGammaCheck GammaPanel0645.certificate 605=true := by decide +kernel
noncomputable def cell0645 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0645.certificate 605 accepted0645
theorem accepted0646 : minorantGammaCheck GammaPanel0646.certificate 606=true := by decide +kernel
noncomputable def cell0646 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0646.certificate 606 accepted0646
theorem accepted0647 : minorantGammaCheck GammaPanel0647.certificate 607=true := by decide +kernel
noncomputable def cell0647 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0647.certificate 607 accepted0647
noncomputable def cells : List CertifiedMinorantCell := [cell0640, cell0641, cell0642, cell0643, cell0644, cell0645, cell0646, cell0647]
theorem chainAccepted : minorantChainCheck (369/2000) (1861/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (369/2000) (1861/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0080
