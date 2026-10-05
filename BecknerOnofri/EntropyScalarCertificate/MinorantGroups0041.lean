import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0041
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0041
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0328 : minorantGammaCheck GammaPanel0328.certificate 288=true := by decide +kernel
noncomputable def cell0328 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0328.certificate 288 accepted0328
theorem accepted0329 : minorantGammaCheck GammaPanel0329.certificate 289=true := by decide +kernel
noncomputable def cell0329 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0329.certificate 289 accepted0329
theorem accepted0330 : minorantGammaCheck GammaPanel0330.certificate 290=true := by decide +kernel
noncomputable def cell0330 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0330.certificate 290 accepted0330
theorem accepted0331 : minorantGammaCheck GammaPanel0331.certificate 291=true := by decide +kernel
noncomputable def cell0331 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0331.certificate 291 accepted0331
theorem accepted0332 : minorantGammaCheck GammaPanel0332.certificate 292=true := by decide +kernel
noncomputable def cell0332 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0332.certificate 292 accepted0332
theorem accepted0333 : minorantGammaCheck GammaPanel0333.certificate 293=true := by decide +kernel
noncomputable def cell0333 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0333.certificate 293 accepted0333
theorem accepted0334 : minorantGammaCheck GammaPanel0334.certificate 294=true := by decide +kernel
noncomputable def cell0334 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0334.certificate 294 accepted0334
theorem accepted0335 : minorantGammaCheck GammaPanel0335.certificate 295=true := by decide +kernel
noncomputable def cell0335 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0335.certificate 295 accepted0335
noncomputable def cells : List CertifiedMinorantCell := [cell0328, cell0329, cell0330, cell0331, cell0332, cell0333, cell0334, cell0335]
theorem chainAccepted : minorantChainCheck (1221/10000) (1237/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1221/10000) (1237/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0041
