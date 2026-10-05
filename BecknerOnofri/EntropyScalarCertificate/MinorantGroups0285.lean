import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0285
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0285
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2280 : minorantGammaCheck GammaPanel2280.certificate 1621=true := by decide +kernel
noncomputable def cell2280 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2280.certificate 1621 accepted2280
theorem accepted2281 : minorantGammaCheck GammaPanel2281.certificate 1621=true := by decide +kernel
noncomputable def cell2281 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2281.certificate 1621 accepted2281
theorem accepted2282 : minorantGammaCheck GammaPanel2282.certificate 1621=true := by decide +kernel
noncomputable def cell2282 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2282.certificate 1621 accepted2282
theorem accepted2283 : minorantGammaCheck GammaPanel2283.certificate 1621=true := by decide +kernel
noncomputable def cell2283 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2283.certificate 1621 accepted2283
theorem accepted2284 : minorantGammaCheck GammaPanel2284.certificate 1621=true := by decide +kernel
noncomputable def cell2284 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2284.certificate 1621 accepted2284
theorem accepted2285 : minorantGammaCheck GammaPanel2285.certificate 1621=true := by decide +kernel
noncomputable def cell2285 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2285.certificate 1621 accepted2285
theorem accepted2286 : minorantGammaCheck GammaPanel2286.certificate 1621=true := by decide +kernel
noncomputable def cell2286 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2286.certificate 1621 accepted2286
theorem accepted2287 : minorantGammaCheck GammaPanel2287.certificate 1621=true := by decide +kernel
noncomputable def cell2287 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2287.certificate 1621 accepted2287
noncomputable def cells : List CertifiedMinorantCell := [cell2280, cell2281, cell2282, cell2283, cell2284, cell2285, cell2286, cell2287]
theorem chainAccepted : minorantChainCheck (4901/5000) (981/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4901/5000) (981/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0285
