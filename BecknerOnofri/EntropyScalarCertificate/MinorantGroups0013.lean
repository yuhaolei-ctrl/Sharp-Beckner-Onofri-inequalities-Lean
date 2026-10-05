import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0013
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0013
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0104 : minorantGammaCheck GammaPanel0104.certificate 64=true := by decide +kernel
noncomputable def cell0104 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0104.certificate 64 accepted0104
theorem accepted0105 : minorantGammaCheck GammaPanel0105.certificate 65=true := by decide +kernel
noncomputable def cell0105 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0105.certificate 65 accepted0105
theorem accepted0106 : minorantGammaCheck GammaPanel0106.certificate 66=true := by decide +kernel
noncomputable def cell0106 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0106.certificate 66 accepted0106
theorem accepted0107 : minorantGammaCheck GammaPanel0107.certificate 67=true := by decide +kernel
noncomputable def cell0107 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0107.certificate 67 accepted0107
theorem accepted0108 : minorantGammaCheck GammaPanel0108.certificate 68=true := by decide +kernel
noncomputable def cell0108 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0108.certificate 68 accepted0108
theorem accepted0109 : minorantGammaCheck GammaPanel0109.certificate 69=true := by decide +kernel
noncomputable def cell0109 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0109.certificate 69 accepted0109
theorem accepted0110 : minorantGammaCheck GammaPanel0110.certificate 70=true := by decide +kernel
noncomputable def cell0110 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0110.certificate 70 accepted0110
theorem accepted0111 : minorantGammaCheck GammaPanel0111.certificate 71=true := by decide +kernel
noncomputable def cell0111 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0111.certificate 71 accepted0111
noncomputable def cells : List CertifiedMinorantCell := [cell0104, cell0105, cell0106, cell0107, cell0108, cell0109, cell0110, cell0111]
theorem chainAccepted : minorantChainCheck (773/10000) (789/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (773/10000) (789/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0013
