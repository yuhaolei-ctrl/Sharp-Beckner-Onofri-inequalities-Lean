import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0361
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0361
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2888 : minorantGammaCheck GammaPanel2888.certificate 1621=true := by decide +kernel
noncomputable def cell2888 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2888.certificate 1621 accepted2888
theorem accepted2889 : minorantGammaCheck GammaPanel2889.certificate 1621=true := by decide +kernel
noncomputable def cell2889 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2889.certificate 1621 accepted2889
theorem accepted2890 : minorantGammaCheck GammaPanel2890.certificate 1621=true := by decide +kernel
noncomputable def cell2890 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2890.certificate 1621 accepted2890
theorem accepted2891 : minorantGammaCheck GammaPanel2891.certificate 1621=true := by decide +kernel
noncomputable def cell2891 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2891.certificate 1621 accepted2891
theorem accepted2892 : minorantGammaCheck GammaPanel2892.certificate 1621=true := by decide +kernel
noncomputable def cell2892 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2892.certificate 1621 accepted2892
theorem accepted2893 : minorantGammaCheck GammaPanel2893.certificate 1621=true := by decide +kernel
noncomputable def cell2893 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2893.certificate 1621 accepted2893
theorem accepted2894 : minorantGammaCheck GammaPanel2894.certificate 1621=true := by decide +kernel
noncomputable def cell2894 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2894.certificate 1621 accepted2894
theorem accepted2895 : minorantGammaCheck GammaPanel2895.certificate 1621=true := by decide +kernel
noncomputable def cell2895 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2895.certificate 1621 accepted2895
noncomputable def cells : List CertifiedMinorantCell := [cell2888, cell2889, cell2890, cell2891, cell2892, cell2893, cell2894, cell2895]
theorem chainAccepted : minorantChainCheck (4989/5000) (12473/12500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4989/5000) (12473/12500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0361
