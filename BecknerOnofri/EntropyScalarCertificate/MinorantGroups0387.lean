import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0387
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0387
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted3096 : minorantGammaCheck GammaPanel3096.certificate 1621=true := by decide +kernel
noncomputable def cell3096 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3096.certificate 1621 accepted3096
theorem accepted3097 : minorantGammaCheck GammaPanel3097.certificate 1621=true := by decide +kernel
noncomputable def cell3097 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3097.certificate 1621 accepted3097
theorem accepted3098 : minorantGammaCheck GammaPanel3098.certificate 1621=true := by decide +kernel
noncomputable def cell3098 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3098.certificate 1621 accepted3098
theorem accepted3099 : minorantGammaCheck GammaPanel3099.certificate 1621=true := by decide +kernel
noncomputable def cell3099 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3099.certificate 1621 accepted3099
theorem accepted3100 : minorantGammaCheck GammaPanel3100.certificate 1621=true := by decide +kernel
noncomputable def cell3100 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3100.certificate 1621 accepted3100
theorem accepted3101 : minorantGammaCheck GammaPanel3101.certificate 1621=true := by decide +kernel
noncomputable def cell3101 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3101.certificate 1621 accepted3101
theorem accepted3102 : minorantGammaCheck GammaPanel3102.certificate 1621=true := by decide +kernel
noncomputable def cell3102 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3102.certificate 1621 accepted3102
theorem accepted3103 : minorantGammaCheck GammaPanel3103.certificate 1621=true := by decide +kernel
noncomputable def cell3103 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3103.certificate 1621 accepted3103
noncomputable def cells : List CertifiedMinorantCell := [cell3096, cell3097, cell3098, cell3099, cell3100, cell3101, cell3102, cell3103]
theorem chainAccepted : minorantChainCheck (24971/25000) (6243/6250) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24971/25000) (6243/6250) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0387
