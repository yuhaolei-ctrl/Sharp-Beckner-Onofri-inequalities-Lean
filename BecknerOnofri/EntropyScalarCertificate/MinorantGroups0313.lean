import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0313
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0313
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2504 : minorantGammaCheck GammaPanel2504.certificate 1621=true := by decide +kernel
noncomputable def cell2504 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2504.certificate 1621 accepted2504
theorem accepted2505 : minorantGammaCheck GammaPanel2505.certificate 1621=true := by decide +kernel
noncomputable def cell2505 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2505.certificate 1621 accepted2505
theorem accepted2506 : minorantGammaCheck GammaPanel2506.certificate 1621=true := by decide +kernel
noncomputable def cell2506 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2506.certificate 1621 accepted2506
theorem accepted2507 : minorantGammaCheck GammaPanel2507.certificate 1621=true := by decide +kernel
noncomputable def cell2507 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2507.certificate 1621 accepted2507
theorem accepted2508 : minorantGammaCheck GammaPanel2508.certificate 1621=true := by decide +kernel
noncomputable def cell2508 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2508.certificate 1621 accepted2508
theorem accepted2509 : minorantGammaCheck GammaPanel2509.certificate 1621=true := by decide +kernel
noncomputable def cell2509 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2509.certificate 1621 accepted2509
theorem accepted2510 : minorantGammaCheck GammaPanel2510.certificate 1621=true := by decide +kernel
noncomputable def cell2510 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2510.certificate 1621 accepted2510
theorem accepted2511 : minorantGammaCheck GammaPanel2511.certificate 1621=true := by decide +kernel
noncomputable def cell2511 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2511.certificate 1621 accepted2511
noncomputable def cells : List CertifiedMinorantCell := [cell2504, cell2505, cell2506, cell2507, cell2508, cell2509, cell2510, cell2511]
theorem chainAccepted : minorantChainCheck (24813/25000) (24817/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24813/25000) (24817/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0313
