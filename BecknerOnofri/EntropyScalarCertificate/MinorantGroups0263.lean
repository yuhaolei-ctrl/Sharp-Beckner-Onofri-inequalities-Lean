import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0263
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0263
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2104 : minorantGammaCheck GammaPanel2104.certificate 1621=true := by decide +kernel
noncomputable def cell2104 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2104.certificate 1621 accepted2104
theorem accepted2105 : minorantGammaCheck GammaPanel2105.certificate 1621=true := by decide +kernel
noncomputable def cell2105 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2105.certificate 1621 accepted2105
theorem accepted2106 : minorantGammaCheck GammaPanel2106.certificate 1621=true := by decide +kernel
noncomputable def cell2106 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2106.certificate 1621 accepted2106
theorem accepted2107 : minorantGammaCheck GammaPanel2107.certificate 1621=true := by decide +kernel
noncomputable def cell2107 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2107.certificate 1621 accepted2107
theorem accepted2108 : minorantGammaCheck GammaPanel2108.certificate 1621=true := by decide +kernel
noncomputable def cell2108 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2108.certificate 1621 accepted2108
theorem accepted2109 : minorantGammaCheck GammaPanel2109.certificate 1621=true := by decide +kernel
noncomputable def cell2109 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2109.certificate 1621 accepted2109
theorem accepted2110 : minorantGammaCheck GammaPanel2110.certificate 1621=true := by decide +kernel
noncomputable def cell2110 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2110.certificate 1621 accepted2110
theorem accepted2111 : minorantGammaCheck GammaPanel2111.certificate 1621=true := by decide +kernel
noncomputable def cell2111 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2111.certificate 1621 accepted2111
noncomputable def cells : List CertifiedMinorantCell := [cell2104, cell2105, cell2106, cell2107, cell2108, cell2109, cell2110, cell2111]
theorem chainAccepted : minorantChainCheck (4813/5000) (4817/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4813/5000) (4817/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0263
