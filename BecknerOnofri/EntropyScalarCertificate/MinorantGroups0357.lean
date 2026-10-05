import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0357
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0357
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2856 : minorantGammaCheck GammaPanel2856.certificate 1621=true := by decide +kernel
noncomputable def cell2856 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2856.certificate 1621 accepted2856
theorem accepted2857 : minorantGammaCheck GammaPanel2857.certificate 1621=true := by decide +kernel
noncomputable def cell2857 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2857.certificate 1621 accepted2857
theorem accepted2858 : minorantGammaCheck GammaPanel2858.certificate 1621=true := by decide +kernel
noncomputable def cell2858 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2858.certificate 1621 accepted2858
theorem accepted2859 : minorantGammaCheck GammaPanel2859.certificate 1621=true := by decide +kernel
noncomputable def cell2859 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2859.certificate 1621 accepted2859
theorem accepted2860 : minorantGammaCheck GammaPanel2860.certificate 1621=true := by decide +kernel
noncomputable def cell2860 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2860.certificate 1621 accepted2860
theorem accepted2861 : minorantGammaCheck GammaPanel2861.certificate 1621=true := by decide +kernel
noncomputable def cell2861 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2861.certificate 1621 accepted2861
theorem accepted2862 : minorantGammaCheck GammaPanel2862.certificate 1621=true := by decide +kernel
noncomputable def cell2862 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2862.certificate 1621 accepted2862
theorem accepted2863 : minorantGammaCheck GammaPanel2863.certificate 1621=true := by decide +kernel
noncomputable def cell2863 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2863.certificate 1621 accepted2863
noncomputable def cells : List CertifiedMinorantCell := [cell2856, cell2857, cell2858, cell2859, cell2860, cell2861, cell2862, cell2863]
theorem chainAccepted : minorantChainCheck (24941/25000) (12471/12500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24941/25000) (12471/12500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0357
