import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0355
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0355
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2840 : minorantGammaCheck GammaPanel2840.certificate 1621=true := by decide +kernel
noncomputable def cell2840 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2840.certificate 1621 accepted2840
theorem accepted2841 : minorantGammaCheck GammaPanel2841.certificate 1621=true := by decide +kernel
noncomputable def cell2841 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2841.certificate 1621 accepted2841
theorem accepted2842 : minorantGammaCheck GammaPanel2842.certificate 1621=true := by decide +kernel
noncomputable def cell2842 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2842.certificate 1621 accepted2842
theorem accepted2843 : minorantGammaCheck GammaPanel2843.certificate 1621=true := by decide +kernel
noncomputable def cell2843 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2843.certificate 1621 accepted2843
theorem accepted2844 : minorantGammaCheck GammaPanel2844.certificate 1621=true := by decide +kernel
noncomputable def cell2844 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2844.certificate 1621 accepted2844
theorem accepted2845 : minorantGammaCheck GammaPanel2845.certificate 1621=true := by decide +kernel
noncomputable def cell2845 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2845.certificate 1621 accepted2845
theorem accepted2846 : minorantGammaCheck GammaPanel2846.certificate 1621=true := by decide +kernel
noncomputable def cell2846 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2846.certificate 1621 accepted2846
theorem accepted2847 : minorantGammaCheck GammaPanel2847.certificate 1621=true := by decide +kernel
noncomputable def cell2847 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2847.certificate 1621 accepted2847
noncomputable def cells : List CertifiedMinorantCell := [cell2840, cell2841, cell2842, cell2843, cell2844, cell2845, cell2846, cell2847]
theorem chainAccepted : minorantChainCheck (24939/25000) (1247/1250) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24939/25000) (1247/1250) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0355
