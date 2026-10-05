import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0310
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0310
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2480 : minorantGammaCheck GammaPanel2480.certificate 1621=true := by decide +kernel
noncomputable def cell2480 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2480.certificate 1621 accepted2480
theorem accepted2481 : minorantGammaCheck GammaPanel2481.certificate 1621=true := by decide +kernel
noncomputable def cell2481 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2481.certificate 1621 accepted2481
theorem accepted2482 : minorantGammaCheck GammaPanel2482.certificate 1621=true := by decide +kernel
noncomputable def cell2482 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2482.certificate 1621 accepted2482
theorem accepted2483 : minorantGammaCheck GammaPanel2483.certificate 1621=true := by decide +kernel
noncomputable def cell2483 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2483.certificate 1621 accepted2483
theorem accepted2484 : minorantGammaCheck GammaPanel2484.certificate 1621=true := by decide +kernel
noncomputable def cell2484 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2484.certificate 1621 accepted2484
theorem accepted2485 : minorantGammaCheck GammaPanel2485.certificate 1621=true := by decide +kernel
noncomputable def cell2485 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2485.certificate 1621 accepted2485
theorem accepted2486 : minorantGammaCheck GammaPanel2486.certificate 1621=true := by decide +kernel
noncomputable def cell2486 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2486.certificate 1621 accepted2486
theorem accepted2487 : minorantGammaCheck GammaPanel2487.certificate 1621=true := by decide +kernel
noncomputable def cell2487 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2487.certificate 1621 accepted2487
noncomputable def cells : List CertifiedMinorantCell := [cell2480, cell2481, cell2482, cell2483, cell2484, cell2485, cell2486, cell2487]
theorem chainAccepted : minorantChainCheck (24801/25000) (4961/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24801/25000) (4961/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0310
