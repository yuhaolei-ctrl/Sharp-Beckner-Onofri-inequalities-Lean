import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0278
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0278
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2224 : minorantGammaCheck GammaPanel2224.certificate 1621=true := by decide +kernel
noncomputable def cell2224 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2224.certificate 1621 accepted2224
theorem accepted2225 : minorantGammaCheck GammaPanel2225.certificate 1621=true := by decide +kernel
noncomputable def cell2225 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2225.certificate 1621 accepted2225
theorem accepted2226 : minorantGammaCheck GammaPanel2226.certificate 1621=true := by decide +kernel
noncomputable def cell2226 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2226.certificate 1621 accepted2226
theorem accepted2227 : minorantGammaCheck GammaPanel2227.certificate 1621=true := by decide +kernel
noncomputable def cell2227 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2227.certificate 1621 accepted2227
theorem accepted2228 : minorantGammaCheck GammaPanel2228.certificate 1621=true := by decide +kernel
noncomputable def cell2228 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2228.certificate 1621 accepted2228
theorem accepted2229 : minorantGammaCheck GammaPanel2229.certificate 1621=true := by decide +kernel
noncomputable def cell2229 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2229.certificate 1621 accepted2229
theorem accepted2230 : minorantGammaCheck GammaPanel2230.certificate 1621=true := by decide +kernel
noncomputable def cell2230 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2230.certificate 1621 accepted2230
theorem accepted2231 : minorantGammaCheck GammaPanel2231.certificate 1621=true := by decide +kernel
noncomputable def cell2231 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2231.certificate 1621 accepted2231
noncomputable def cells : List CertifiedMinorantCell := [cell2224, cell2225, cell2226, cell2227, cell2228, cell2229, cell2230, cell2231]
theorem chainAccepted : minorantChainCheck (4873/5000) (4877/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4873/5000) (4877/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0278
