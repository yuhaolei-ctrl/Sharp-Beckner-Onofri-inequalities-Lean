import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0286
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0286
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2288 : minorantGammaCheck GammaPanel2288.certificate 1621=true := by decide +kernel
noncomputable def cell2288 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2288.certificate 1621 accepted2288
theorem accepted2289 : minorantGammaCheck GammaPanel2289.certificate 1621=true := by decide +kernel
noncomputable def cell2289 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2289.certificate 1621 accepted2289
theorem accepted2290 : minorantGammaCheck GammaPanel2290.certificate 1621=true := by decide +kernel
noncomputable def cell2290 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2290.certificate 1621 accepted2290
theorem accepted2291 : minorantGammaCheck GammaPanel2291.certificate 1621=true := by decide +kernel
noncomputable def cell2291 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2291.certificate 1621 accepted2291
theorem accepted2292 : minorantGammaCheck GammaPanel2292.certificate 1621=true := by decide +kernel
noncomputable def cell2292 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2292.certificate 1621 accepted2292
theorem accepted2293 : minorantGammaCheck GammaPanel2293.certificate 1621=true := by decide +kernel
noncomputable def cell2293 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2293.certificate 1621 accepted2293
theorem accepted2294 : minorantGammaCheck GammaPanel2294.certificate 1621=true := by decide +kernel
noncomputable def cell2294 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2294.certificate 1621 accepted2294
theorem accepted2295 : minorantGammaCheck GammaPanel2295.certificate 1621=true := by decide +kernel
noncomputable def cell2295 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2295.certificate 1621 accepted2295
noncomputable def cells : List CertifiedMinorantCell := [cell2288, cell2289, cell2290, cell2291, cell2292, cell2293, cell2294, cell2295]
theorem chainAccepted : minorantChainCheck (981/1000) (4909/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (981/1000) (4909/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0286
