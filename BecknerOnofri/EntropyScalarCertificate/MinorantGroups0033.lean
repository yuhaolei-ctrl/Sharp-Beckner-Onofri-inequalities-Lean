import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0033
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0033
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0264 : minorantGammaCheck GammaPanel0264.certificate 224=true := by decide +kernel
noncomputable def cell0264 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0264.certificate 224 accepted0264
theorem accepted0265 : minorantGammaCheck GammaPanel0265.certificate 225=true := by decide +kernel
noncomputable def cell0265 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0265.certificate 225 accepted0265
theorem accepted0266 : minorantGammaCheck GammaPanel0266.certificate 226=true := by decide +kernel
noncomputable def cell0266 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0266.certificate 226 accepted0266
theorem accepted0267 : minorantGammaCheck GammaPanel0267.certificate 227=true := by decide +kernel
noncomputable def cell0267 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0267.certificate 227 accepted0267
theorem accepted0268 : minorantGammaCheck GammaPanel0268.certificate 228=true := by decide +kernel
noncomputable def cell0268 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0268.certificate 228 accepted0268
theorem accepted0269 : minorantGammaCheck GammaPanel0269.certificate 229=true := by decide +kernel
noncomputable def cell0269 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0269.certificate 229 accepted0269
theorem accepted0270 : minorantGammaCheck GammaPanel0270.certificate 230=true := by decide +kernel
noncomputable def cell0270 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0270.certificate 230 accepted0270
theorem accepted0271 : minorantGammaCheck GammaPanel0271.certificate 231=true := by decide +kernel
noncomputable def cell0271 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0271.certificate 231 accepted0271
noncomputable def cells : List CertifiedMinorantCell := [cell0264, cell0265, cell0266, cell0267, cell0268, cell0269, cell0270, cell0271]
theorem chainAccepted : minorantChainCheck (1093/10000) (1109/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1093/10000) (1109/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0033
