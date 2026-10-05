import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0087
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0087
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0696 : minorantGammaCheck GammaPanel0696.certificate 616=true := by decide +kernel
noncomputable def cell0696 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0696.certificate 616 accepted0696
theorem accepted0697 : minorantGammaCheck GammaPanel0697.certificate 616=true := by decide +kernel
noncomputable def cell0697 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0697.certificate 616 accepted0697
theorem accepted0698 : minorantGammaCheck GammaPanel0698.certificate 616=true := by decide +kernel
noncomputable def cell0698 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0698.certificate 616 accepted0698
theorem accepted0699 : minorantGammaCheck GammaPanel0699.certificate 616=true := by decide +kernel
noncomputable def cell0699 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0699.certificate 616 accepted0699
theorem accepted0700 : minorantGammaCheck GammaPanel0700.certificate 616=true := by decide +kernel
noncomputable def cell0700 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0700.certificate 616 accepted0700
theorem accepted0701 : minorantGammaCheck GammaPanel0701.certificate 616=true := by decide +kernel
noncomputable def cell0701 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0701.certificate 616 accepted0701
theorem accepted0702 : minorantGammaCheck GammaPanel0702.certificate 616=true := by decide +kernel
noncomputable def cell0702 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0702.certificate 616 accepted0702
theorem accepted0703 : minorantGammaCheck GammaPanel0703.certificate 616=true := by decide +kernel
noncomputable def cell0703 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0703.certificate 616 accepted0703
noncomputable def cells : List CertifiedMinorantCell := [cell0696, cell0697, cell0698, cell0699, cell0700, cell0701, cell0702, cell0703]
theorem chainAccepted : minorantChainCheck (1957/10000) (1973/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1957/10000) (1973/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0087
