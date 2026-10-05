import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0289
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0289
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2312 : minorantGammaCheck GammaPanel2312.certificate 1621=true := by decide +kernel
noncomputable def cell2312 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2312.certificate 1621 accepted2312
theorem accepted2313 : minorantGammaCheck GammaPanel2313.certificate 1621=true := by decide +kernel
noncomputable def cell2313 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2313.certificate 1621 accepted2313
theorem accepted2314 : minorantGammaCheck GammaPanel2314.certificate 1621=true := by decide +kernel
noncomputable def cell2314 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2314.certificate 1621 accepted2314
theorem accepted2315 : minorantGammaCheck GammaPanel2315.certificate 1621=true := by decide +kernel
noncomputable def cell2315 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2315.certificate 1621 accepted2315
theorem accepted2316 : minorantGammaCheck GammaPanel2316.certificate 1621=true := by decide +kernel
noncomputable def cell2316 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2316.certificate 1621 accepted2316
theorem accepted2317 : minorantGammaCheck GammaPanel2317.certificate 1621=true := by decide +kernel
noncomputable def cell2317 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2317.certificate 1621 accepted2317
theorem accepted2318 : minorantGammaCheck GammaPanel2318.certificate 1621=true := by decide +kernel
noncomputable def cell2318 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2318.certificate 1621 accepted2318
theorem accepted2319 : minorantGammaCheck GammaPanel2319.certificate 1621=true := by decide +kernel
noncomputable def cell2319 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2319.certificate 1621 accepted2319
noncomputable def cells : List CertifiedMinorantCell := [cell2312, cell2313, cell2314, cell2315, cell2316, cell2317, cell2318, cell2319]
theorem chainAccepted : minorantChainCheck (4917/5000) (4921/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4917/5000) (4921/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0289
