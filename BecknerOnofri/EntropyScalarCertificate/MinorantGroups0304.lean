import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0304
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0304
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2432 : minorantGammaCheck GammaPanel2432.certificate 1621=true := by decide +kernel
noncomputable def cell2432 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2432.certificate 1621 accepted2432
theorem accepted2433 : minorantGammaCheck GammaPanel2433.certificate 1621=true := by decide +kernel
noncomputable def cell2433 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2433.certificate 1621 accepted2433
theorem accepted2434 : minorantGammaCheck GammaPanel2434.certificate 1621=true := by decide +kernel
noncomputable def cell2434 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2434.certificate 1621 accepted2434
theorem accepted2435 : minorantGammaCheck GammaPanel2435.certificate 1621=true := by decide +kernel
noncomputable def cell2435 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2435.certificate 1621 accepted2435
theorem accepted2436 : minorantGammaCheck GammaPanel2436.certificate 1621=true := by decide +kernel
noncomputable def cell2436 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2436.certificate 1621 accepted2436
theorem accepted2437 : minorantGammaCheck GammaPanel2437.certificate 1621=true := by decide +kernel
noncomputable def cell2437 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2437.certificate 1621 accepted2437
theorem accepted2438 : minorantGammaCheck GammaPanel2438.certificate 1621=true := by decide +kernel
noncomputable def cell2438 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2438.certificate 1621 accepted2438
theorem accepted2439 : minorantGammaCheck GammaPanel2439.certificate 1621=true := by decide +kernel
noncomputable def cell2439 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2439.certificate 1621 accepted2439
noncomputable def cells : List CertifiedMinorantCell := [cell2432, cell2433, cell2434, cell2435, cell2436, cell2437, cell2438, cell2439]
theorem chainAccepted : minorantChainCheck (24777/25000) (24781/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24777/25000) (24781/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0304
