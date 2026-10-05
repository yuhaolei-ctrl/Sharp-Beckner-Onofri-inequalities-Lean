import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0291
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0291
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2328 : minorantGammaCheck GammaPanel2328.certificate 1621=true := by decide +kernel
noncomputable def cell2328 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2328.certificate 1621 accepted2328
theorem accepted2329 : minorantGammaCheck GammaPanel2329.certificate 1621=true := by decide +kernel
noncomputable def cell2329 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2329.certificate 1621 accepted2329
theorem accepted2330 : minorantGammaCheck GammaPanel2330.certificate 1621=true := by decide +kernel
noncomputable def cell2330 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2330.certificate 1621 accepted2330
theorem accepted2331 : minorantGammaCheck GammaPanel2331.certificate 1621=true := by decide +kernel
noncomputable def cell2331 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2331.certificate 1621 accepted2331
theorem accepted2332 : minorantGammaCheck GammaPanel2332.certificate 1621=true := by decide +kernel
noncomputable def cell2332 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2332.certificate 1621 accepted2332
theorem accepted2333 : minorantGammaCheck GammaPanel2333.certificate 1621=true := by decide +kernel
noncomputable def cell2333 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2333.certificate 1621 accepted2333
theorem accepted2334 : minorantGammaCheck GammaPanel2334.certificate 1621=true := by decide +kernel
noncomputable def cell2334 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2334.certificate 1621 accepted2334
theorem accepted2335 : minorantGammaCheck GammaPanel2335.certificate 1621=true := by decide +kernel
noncomputable def cell2335 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2335.certificate 1621 accepted2335
noncomputable def cells : List CertifiedMinorantCell := [cell2328, cell2329, cell2330, cell2331, cell2332, cell2333, cell2334, cell2335]
theorem chainAccepted : minorantChainCheck (197/200) (4929/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (197/200) (4929/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0291
