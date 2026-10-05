import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0277
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0277
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2216 : minorantGammaCheck GammaPanel2216.certificate 1621=true := by decide +kernel
noncomputable def cell2216 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2216.certificate 1621 accepted2216
theorem accepted2217 : minorantGammaCheck GammaPanel2217.certificate 1621=true := by decide +kernel
noncomputable def cell2217 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2217.certificate 1621 accepted2217
theorem accepted2218 : minorantGammaCheck GammaPanel2218.certificate 1621=true := by decide +kernel
noncomputable def cell2218 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2218.certificate 1621 accepted2218
theorem accepted2219 : minorantGammaCheck GammaPanel2219.certificate 1621=true := by decide +kernel
noncomputable def cell2219 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2219.certificate 1621 accepted2219
theorem accepted2220 : minorantGammaCheck GammaPanel2220.certificate 1621=true := by decide +kernel
noncomputable def cell2220 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2220.certificate 1621 accepted2220
theorem accepted2221 : minorantGammaCheck GammaPanel2221.certificate 1621=true := by decide +kernel
noncomputable def cell2221 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2221.certificate 1621 accepted2221
theorem accepted2222 : minorantGammaCheck GammaPanel2222.certificate 1621=true := by decide +kernel
noncomputable def cell2222 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2222.certificate 1621 accepted2222
theorem accepted2223 : minorantGammaCheck GammaPanel2223.certificate 1621=true := by decide +kernel
noncomputable def cell2223 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2223.certificate 1621 accepted2223
noncomputable def cells : List CertifiedMinorantCell := [cell2216, cell2217, cell2218, cell2219, cell2220, cell2221, cell2222, cell2223]
theorem chainAccepted : minorantChainCheck (4869/5000) (4873/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4869/5000) (4873/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0277
