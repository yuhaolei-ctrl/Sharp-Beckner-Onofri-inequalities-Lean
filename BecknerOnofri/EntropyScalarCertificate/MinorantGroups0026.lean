import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0026
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0026
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0208 : minorantGammaCheck GammaPanel0208.certificate 168=true := by decide +kernel
noncomputable def cell0208 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0208.certificate 168 accepted0208
theorem accepted0209 : minorantGammaCheck GammaPanel0209.certificate 169=true := by decide +kernel
noncomputable def cell0209 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0209.certificate 169 accepted0209
theorem accepted0210 : minorantGammaCheck GammaPanel0210.certificate 170=true := by decide +kernel
noncomputable def cell0210 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0210.certificate 170 accepted0210
theorem accepted0211 : minorantGammaCheck GammaPanel0211.certificate 171=true := by decide +kernel
noncomputable def cell0211 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0211.certificate 171 accepted0211
theorem accepted0212 : minorantGammaCheck GammaPanel0212.certificate 172=true := by decide +kernel
noncomputable def cell0212 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0212.certificate 172 accepted0212
theorem accepted0213 : minorantGammaCheck GammaPanel0213.certificate 173=true := by decide +kernel
noncomputable def cell0213 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0213.certificate 173 accepted0213
theorem accepted0214 : minorantGammaCheck GammaPanel0214.certificate 174=true := by decide +kernel
noncomputable def cell0214 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0214.certificate 174 accepted0214
theorem accepted0215 : minorantGammaCheck GammaPanel0215.certificate 175=true := by decide +kernel
noncomputable def cell0215 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0215.certificate 175 accepted0215
noncomputable def cells : List CertifiedMinorantCell := [cell0208, cell0209, cell0210, cell0211, cell0212, cell0213, cell0214, cell0215]
theorem chainAccepted : minorantChainCheck (981/10000) (997/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (981/10000) (997/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0026
