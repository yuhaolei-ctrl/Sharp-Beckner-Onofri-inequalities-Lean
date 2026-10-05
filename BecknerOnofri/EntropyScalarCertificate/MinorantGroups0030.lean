import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0030
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0030
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0240 : minorantGammaCheck GammaPanel0240.certificate 200=true := by decide +kernel
noncomputable def cell0240 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0240.certificate 200 accepted0240
theorem accepted0241 : minorantGammaCheck GammaPanel0241.certificate 201=true := by decide +kernel
noncomputable def cell0241 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0241.certificate 201 accepted0241
theorem accepted0242 : minorantGammaCheck GammaPanel0242.certificate 202=true := by decide +kernel
noncomputable def cell0242 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0242.certificate 202 accepted0242
theorem accepted0243 : minorantGammaCheck GammaPanel0243.certificate 203=true := by decide +kernel
noncomputable def cell0243 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0243.certificate 203 accepted0243
theorem accepted0244 : minorantGammaCheck GammaPanel0244.certificate 204=true := by decide +kernel
noncomputable def cell0244 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0244.certificate 204 accepted0244
theorem accepted0245 : minorantGammaCheck GammaPanel0245.certificate 205=true := by decide +kernel
noncomputable def cell0245 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0245.certificate 205 accepted0245
theorem accepted0246 : minorantGammaCheck GammaPanel0246.certificate 206=true := by decide +kernel
noncomputable def cell0246 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0246.certificate 206 accepted0246
theorem accepted0247 : minorantGammaCheck GammaPanel0247.certificate 207=true := by decide +kernel
noncomputable def cell0247 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0247.certificate 207 accepted0247
noncomputable def cells : List CertifiedMinorantCell := [cell0240, cell0241, cell0242, cell0243, cell0244, cell0245, cell0246, cell0247]
theorem chainAccepted : minorantChainCheck (209/2000) (1061/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (209/2000) (1061/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0030
