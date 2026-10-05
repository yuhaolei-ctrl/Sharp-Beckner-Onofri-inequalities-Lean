import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0282
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0282
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2256 : minorantGammaCheck GammaPanel2256.certificate 1621=true := by decide +kernel
noncomputable def cell2256 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2256.certificate 1621 accepted2256
theorem accepted2257 : minorantGammaCheck GammaPanel2257.certificate 1621=true := by decide +kernel
noncomputable def cell2257 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2257.certificate 1621 accepted2257
theorem accepted2258 : minorantGammaCheck GammaPanel2258.certificate 1621=true := by decide +kernel
noncomputable def cell2258 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2258.certificate 1621 accepted2258
theorem accepted2259 : minorantGammaCheck GammaPanel2259.certificate 1621=true := by decide +kernel
noncomputable def cell2259 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2259.certificate 1621 accepted2259
theorem accepted2260 : minorantGammaCheck GammaPanel2260.certificate 1621=true := by decide +kernel
noncomputable def cell2260 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2260.certificate 1621 accepted2260
theorem accepted2261 : minorantGammaCheck GammaPanel2261.certificate 1621=true := by decide +kernel
noncomputable def cell2261 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2261.certificate 1621 accepted2261
theorem accepted2262 : minorantGammaCheck GammaPanel2262.certificate 1621=true := by decide +kernel
noncomputable def cell2262 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2262.certificate 1621 accepted2262
theorem accepted2263 : minorantGammaCheck GammaPanel2263.certificate 1621=true := by decide +kernel
noncomputable def cell2263 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2263.certificate 1621 accepted2263
noncomputable def cells : List CertifiedMinorantCell := [cell2256, cell2257, cell2258, cell2259, cell2260, cell2261, cell2262, cell2263]
theorem chainAccepted : minorantChainCheck (4889/5000) (4893/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4889/5000) (4893/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0282
