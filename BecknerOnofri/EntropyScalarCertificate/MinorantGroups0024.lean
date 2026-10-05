import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0024
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0024
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0192 : minorantGammaCheck GammaPanel0192.certificate 152=true := by decide +kernel
noncomputable def cell0192 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0192.certificate 152 accepted0192
theorem accepted0193 : minorantGammaCheck GammaPanel0193.certificate 153=true := by decide +kernel
noncomputable def cell0193 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0193.certificate 153 accepted0193
theorem accepted0194 : minorantGammaCheck GammaPanel0194.certificate 154=true := by decide +kernel
noncomputable def cell0194 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0194.certificate 154 accepted0194
theorem accepted0195 : minorantGammaCheck GammaPanel0195.certificate 155=true := by decide +kernel
noncomputable def cell0195 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0195.certificate 155 accepted0195
theorem accepted0196 : minorantGammaCheck GammaPanel0196.certificate 156=true := by decide +kernel
noncomputable def cell0196 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0196.certificate 156 accepted0196
theorem accepted0197 : minorantGammaCheck GammaPanel0197.certificate 157=true := by decide +kernel
noncomputable def cell0197 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0197.certificate 157 accepted0197
theorem accepted0198 : minorantGammaCheck GammaPanel0198.certificate 158=true := by decide +kernel
noncomputable def cell0198 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0198.certificate 158 accepted0198
theorem accepted0199 : minorantGammaCheck GammaPanel0199.certificate 159=true := by decide +kernel
noncomputable def cell0199 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0199.certificate 159 accepted0199
noncomputable def cells : List CertifiedMinorantCell := [cell0192, cell0193, cell0194, cell0195, cell0196, cell0197, cell0198, cell0199]
theorem chainAccepted : minorantChainCheck (949/10000) (193/2000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (949/10000) (193/2000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0024
