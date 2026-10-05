import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0028
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0028
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0224 : minorantGammaCheck GammaPanel0224.certificate 184=true := by decide +kernel
noncomputable def cell0224 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0224.certificate 184 accepted0224
theorem accepted0225 : minorantGammaCheck GammaPanel0225.certificate 185=true := by decide +kernel
noncomputable def cell0225 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0225.certificate 185 accepted0225
theorem accepted0226 : minorantGammaCheck GammaPanel0226.certificate 186=true := by decide +kernel
noncomputable def cell0226 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0226.certificate 186 accepted0226
theorem accepted0227 : minorantGammaCheck GammaPanel0227.certificate 187=true := by decide +kernel
noncomputable def cell0227 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0227.certificate 187 accepted0227
theorem accepted0228 : minorantGammaCheck GammaPanel0228.certificate 188=true := by decide +kernel
noncomputable def cell0228 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0228.certificate 188 accepted0228
theorem accepted0229 : minorantGammaCheck GammaPanel0229.certificate 189=true := by decide +kernel
noncomputable def cell0229 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0229.certificate 189 accepted0229
theorem accepted0230 : minorantGammaCheck GammaPanel0230.certificate 190=true := by decide +kernel
noncomputable def cell0230 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0230.certificate 190 accepted0230
theorem accepted0231 : minorantGammaCheck GammaPanel0231.certificate 191=true := by decide +kernel
noncomputable def cell0231 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0231.certificate 191 accepted0231
noncomputable def cells : List CertifiedMinorantCell := [cell0224, cell0225, cell0226, cell0227, cell0228, cell0229, cell0230, cell0231]
theorem chainAccepted : minorantChainCheck (1013/10000) (1029/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1013/10000) (1029/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0028
