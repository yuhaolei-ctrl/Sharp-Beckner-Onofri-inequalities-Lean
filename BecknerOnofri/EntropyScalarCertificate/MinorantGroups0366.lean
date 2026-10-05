import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0366
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0366
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2928 : minorantGammaCheck GammaPanel2928.certificate 1621=true := by decide +kernel
noncomputable def cell2928 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2928.certificate 1621 accepted2928
theorem accepted2929 : minorantGammaCheck GammaPanel2929.certificate 1621=true := by decide +kernel
noncomputable def cell2929 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2929.certificate 1621 accepted2929
theorem accepted2930 : minorantGammaCheck GammaPanel2930.certificate 1621=true := by decide +kernel
noncomputable def cell2930 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2930.certificate 1621 accepted2930
theorem accepted2931 : minorantGammaCheck GammaPanel2931.certificate 1621=true := by decide +kernel
noncomputable def cell2931 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2931.certificate 1621 accepted2931
theorem accepted2932 : minorantGammaCheck GammaPanel2932.certificate 1621=true := by decide +kernel
noncomputable def cell2932 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2932.certificate 1621 accepted2932
theorem accepted2933 : minorantGammaCheck GammaPanel2933.certificate 1621=true := by decide +kernel
noncomputable def cell2933 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2933.certificate 1621 accepted2933
theorem accepted2934 : minorantGammaCheck GammaPanel2934.certificate 1621=true := by decide +kernel
noncomputable def cell2934 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2934.certificate 1621 accepted2934
theorem accepted2935 : minorantGammaCheck GammaPanel2935.certificate 1621=true := by decide +kernel
noncomputable def cell2935 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2935.certificate 1621 accepted2935
noncomputable def cells : List CertifiedMinorantCell := [cell2928, cell2929, cell2930, cell2931, cell2932, cell2933, cell2934, cell2935]
theorem chainAccepted : minorantChainCheck (499/500) (24951/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (499/500) (24951/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0366
