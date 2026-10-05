import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0378
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0378
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted3024 : minorantGammaCheck GammaPanel3024.certificate 1621=true := by decide +kernel
noncomputable def cell3024 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3024.certificate 1621 accepted3024
theorem accepted3025 : minorantGammaCheck GammaPanel3025.certificate 1621=true := by decide +kernel
noncomputable def cell3025 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3025.certificate 1621 accepted3025
theorem accepted3026 : minorantGammaCheck GammaPanel3026.certificate 1621=true := by decide +kernel
noncomputable def cell3026 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3026.certificate 1621 accepted3026
theorem accepted3027 : minorantGammaCheck GammaPanel3027.certificate 1621=true := by decide +kernel
noncomputable def cell3027 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3027.certificate 1621 accepted3027
theorem accepted3028 : minorantGammaCheck GammaPanel3028.certificate 1621=true := by decide +kernel
noncomputable def cell3028 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3028.certificate 1621 accepted3028
theorem accepted3029 : minorantGammaCheck GammaPanel3029.certificate 1621=true := by decide +kernel
noncomputable def cell3029 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3029.certificate 1621 accepted3029
theorem accepted3030 : minorantGammaCheck GammaPanel3030.certificate 1621=true := by decide +kernel
noncomputable def cell3030 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3030.certificate 1621 accepted3030
theorem accepted3031 : minorantGammaCheck GammaPanel3031.certificate 1621=true := by decide +kernel
noncomputable def cell3031 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3031.certificate 1621 accepted3031
noncomputable def cells : List CertifiedMinorantCell := [cell3024, cell3025, cell3026, cell3027, cell3028, cell3029, cell3030, cell3031]
theorem chainAccepted : minorantChainCheck (12481/12500) (24963/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (12481/12500) (24963/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0378
