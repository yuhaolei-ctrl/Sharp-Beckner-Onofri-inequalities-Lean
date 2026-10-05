import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0038
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0038
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0304 : minorantGammaCheck GammaPanel0304.certificate 264=true := by decide +kernel
noncomputable def cell0304 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0304.certificate 264 accepted0304
theorem accepted0305 : minorantGammaCheck GammaPanel0305.certificate 265=true := by decide +kernel
noncomputable def cell0305 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0305.certificate 265 accepted0305
theorem accepted0306 : minorantGammaCheck GammaPanel0306.certificate 266=true := by decide +kernel
noncomputable def cell0306 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0306.certificate 266 accepted0306
theorem accepted0307 : minorantGammaCheck GammaPanel0307.certificate 267=true := by decide +kernel
noncomputable def cell0307 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0307.certificate 267 accepted0307
theorem accepted0308 : minorantGammaCheck GammaPanel0308.certificate 268=true := by decide +kernel
noncomputable def cell0308 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0308.certificate 268 accepted0308
theorem accepted0309 : minorantGammaCheck GammaPanel0309.certificate 269=true := by decide +kernel
noncomputable def cell0309 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0309.certificate 269 accepted0309
theorem accepted0310 : minorantGammaCheck GammaPanel0310.certificate 270=true := by decide +kernel
noncomputable def cell0310 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0310.certificate 270 accepted0310
theorem accepted0311 : minorantGammaCheck GammaPanel0311.certificate 271=true := by decide +kernel
noncomputable def cell0311 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0311.certificate 271 accepted0311
noncomputable def cells : List CertifiedMinorantCell := [cell0304, cell0305, cell0306, cell0307, cell0308, cell0309, cell0310, cell0311]
theorem chainAccepted : minorantChainCheck (1173/10000) (1189/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1173/10000) (1189/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0038
