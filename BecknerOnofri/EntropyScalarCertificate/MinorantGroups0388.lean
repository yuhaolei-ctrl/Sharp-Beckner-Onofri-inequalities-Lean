import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0388
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0388
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted3104 : minorantGammaCheck GammaPanel3104.certificate 1621=true := by decide +kernel
noncomputable def cell3104 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3104.certificate 1621 accepted3104
theorem accepted3105 : minorantGammaCheck GammaPanel3105.certificate 1621=true := by decide +kernel
noncomputable def cell3105 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3105.certificate 1621 accepted3105
theorem accepted3106 : minorantGammaCheck GammaPanel3106.certificate 1621=true := by decide +kernel
noncomputable def cell3106 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3106.certificate 1621 accepted3106
theorem accepted3107 : minorantGammaCheck GammaPanel3107.certificate 1621=true := by decide +kernel
noncomputable def cell3107 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3107.certificate 1621 accepted3107
theorem accepted3108 : minorantGammaCheck GammaPanel3108.certificate 1621=true := by decide +kernel
noncomputable def cell3108 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3108.certificate 1621 accepted3108
theorem accepted3109 : minorantGammaCheck GammaPanel3109.certificate 1621=true := by decide +kernel
noncomputable def cell3109 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3109.certificate 1621 accepted3109
theorem accepted3110 : minorantGammaCheck GammaPanel3110.certificate 1621=true := by decide +kernel
noncomputable def cell3110 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3110.certificate 1621 accepted3110
theorem accepted3111 : minorantGammaCheck GammaPanel3111.certificate 1621=true := by decide +kernel
noncomputable def cell3111 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3111.certificate 1621 accepted3111
noncomputable def cells : List CertifiedMinorantCell := [cell3104, cell3105, cell3106, cell3107, cell3108, cell3109, cell3110, cell3111]
theorem chainAccepted : minorantChainCheck (6243/6250) (24973/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (6243/6250) (24973/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0388
