import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0306
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0306
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2448 : minorantGammaCheck GammaPanel2448.certificate 1621=true := by decide +kernel
noncomputable def cell2448 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2448.certificate 1621 accepted2448
theorem accepted2449 : minorantGammaCheck GammaPanel2449.certificate 1621=true := by decide +kernel
noncomputable def cell2449 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2449.certificate 1621 accepted2449
theorem accepted2450 : minorantGammaCheck GammaPanel2450.certificate 1621=true := by decide +kernel
noncomputable def cell2450 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2450.certificate 1621 accepted2450
theorem accepted2451 : minorantGammaCheck GammaPanel2451.certificate 1621=true := by decide +kernel
noncomputable def cell2451 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2451.certificate 1621 accepted2451
theorem accepted2452 : minorantGammaCheck GammaPanel2452.certificate 1621=true := by decide +kernel
noncomputable def cell2452 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2452.certificate 1621 accepted2452
theorem accepted2453 : minorantGammaCheck GammaPanel2453.certificate 1621=true := by decide +kernel
noncomputable def cell2453 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2453.certificate 1621 accepted2453
theorem accepted2454 : minorantGammaCheck GammaPanel2454.certificate 1621=true := by decide +kernel
noncomputable def cell2454 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2454.certificate 1621 accepted2454
theorem accepted2455 : minorantGammaCheck GammaPanel2455.certificate 1621=true := by decide +kernel
noncomputable def cell2455 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2455.certificate 1621 accepted2455
noncomputable def cells : List CertifiedMinorantCell := [cell2448, cell2449, cell2450, cell2451, cell2452, cell2453, cell2454, cell2455]
theorem chainAccepted : minorantChainCheck (4957/5000) (24789/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4957/5000) (24789/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0306
