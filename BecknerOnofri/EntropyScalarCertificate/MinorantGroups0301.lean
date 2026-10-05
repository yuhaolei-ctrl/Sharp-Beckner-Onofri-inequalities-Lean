import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0301
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0301
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2408 : minorantGammaCheck GammaPanel2408.certificate 1621=true := by decide +kernel
noncomputable def cell2408 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2408.certificate 1621 accepted2408
theorem accepted2409 : minorantGammaCheck GammaPanel2409.certificate 1621=true := by decide +kernel
noncomputable def cell2409 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2409.certificate 1621 accepted2409
theorem accepted2410 : minorantGammaCheck GammaPanel2410.certificate 1621=true := by decide +kernel
noncomputable def cell2410 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2410.certificate 1621 accepted2410
theorem accepted2411 : minorantGammaCheck GammaPanel2411.certificate 1621=true := by decide +kernel
noncomputable def cell2411 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2411.certificate 1621 accepted2411
theorem accepted2412 : minorantGammaCheck GammaPanel2412.certificate 1621=true := by decide +kernel
noncomputable def cell2412 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2412.certificate 1621 accepted2412
theorem accepted2413 : minorantGammaCheck GammaPanel2413.certificate 1621=true := by decide +kernel
noncomputable def cell2413 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2413.certificate 1621 accepted2413
theorem accepted2414 : minorantGammaCheck GammaPanel2414.certificate 1621=true := by decide +kernel
noncomputable def cell2414 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2414.certificate 1621 accepted2414
theorem accepted2415 : minorantGammaCheck GammaPanel2415.certificate 1621=true := by decide +kernel
noncomputable def cell2415 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2415.certificate 1621 accepted2415
noncomputable def cells : List CertifiedMinorantCell := [cell2408, cell2409, cell2410, cell2411, cell2412, cell2413, cell2414, cell2415]
theorem chainAccepted : minorantChainCheck (4953/5000) (24769/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4953/5000) (24769/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0301
