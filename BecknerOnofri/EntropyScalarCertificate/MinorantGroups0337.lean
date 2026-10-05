import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0337
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0337
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2696 : minorantGammaCheck GammaPanel2696.certificate 1621=true := by decide +kernel
noncomputable def cell2696 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2696.certificate 1621 accepted2696
theorem accepted2697 : minorantGammaCheck GammaPanel2697.certificate 1621=true := by decide +kernel
noncomputable def cell2697 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2697.certificate 1621 accepted2697
theorem accepted2698 : minorantGammaCheck GammaPanel2698.certificate 1621=true := by decide +kernel
noncomputable def cell2698 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2698.certificate 1621 accepted2698
theorem accepted2699 : minorantGammaCheck GammaPanel2699.certificate 1621=true := by decide +kernel
noncomputable def cell2699 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2699.certificate 1621 accepted2699
theorem accepted2700 : minorantGammaCheck GammaPanel2700.certificate 1621=true := by decide +kernel
noncomputable def cell2700 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2700.certificate 1621 accepted2700
theorem accepted2701 : minorantGammaCheck GammaPanel2701.certificate 1621=true := by decide +kernel
noncomputable def cell2701 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2701.certificate 1621 accepted2701
theorem accepted2702 : minorantGammaCheck GammaPanel2702.certificate 1621=true := by decide +kernel
noncomputable def cell2702 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2702.certificate 1621 accepted2702
theorem accepted2703 : minorantGammaCheck GammaPanel2703.certificate 1621=true := by decide +kernel
noncomputable def cell2703 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2703.certificate 1621 accepted2703
noncomputable def cells : List CertifiedMinorantCell := [cell2696, cell2697, cell2698, cell2699, cell2700, cell2701, cell2702, cell2703]
theorem chainAccepted : minorantChainCheck (24909/25000) (24913/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24909/25000) (24913/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0337
