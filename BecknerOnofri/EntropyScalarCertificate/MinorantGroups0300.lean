import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0300
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0300
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2400 : minorantGammaCheck GammaPanel2400.certificate 1621=true := by decide +kernel
noncomputable def cell2400 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2400.certificate 1621 accepted2400
theorem accepted2401 : minorantGammaCheck GammaPanel2401.certificate 1621=true := by decide +kernel
noncomputable def cell2401 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2401.certificate 1621 accepted2401
theorem accepted2402 : minorantGammaCheck GammaPanel2402.certificate 1621=true := by decide +kernel
noncomputable def cell2402 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2402.certificate 1621 accepted2402
theorem accepted2403 : minorantGammaCheck GammaPanel2403.certificate 1621=true := by decide +kernel
noncomputable def cell2403 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2403.certificate 1621 accepted2403
theorem accepted2404 : minorantGammaCheck GammaPanel2404.certificate 1621=true := by decide +kernel
noncomputable def cell2404 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2404.certificate 1621 accepted2404
theorem accepted2405 : minorantGammaCheck GammaPanel2405.certificate 1621=true := by decide +kernel
noncomputable def cell2405 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2405.certificate 1621 accepted2405
theorem accepted2406 : minorantGammaCheck GammaPanel2406.certificate 1621=true := by decide +kernel
noncomputable def cell2406 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2406.certificate 1621 accepted2406
theorem accepted2407 : minorantGammaCheck GammaPanel2407.certificate 1621=true := by decide +kernel
noncomputable def cell2407 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2407.certificate 1621 accepted2407
noncomputable def cells : List CertifiedMinorantCell := [cell2400, cell2401, cell2402, cell2403, cell2404, cell2405, cell2406, cell2407]
theorem chainAccepted : minorantChainCheck (24761/25000) (4953/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24761/25000) (4953/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0300
