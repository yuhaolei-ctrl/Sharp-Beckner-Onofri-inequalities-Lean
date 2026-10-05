import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0044
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0044
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0352 : minorantGammaCheck GammaPanel0352.certificate 312=true := by decide +kernel
noncomputable def cell0352 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0352.certificate 312 accepted0352
theorem accepted0353 : minorantGammaCheck GammaPanel0353.certificate 313=true := by decide +kernel
noncomputable def cell0353 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0353.certificate 313 accepted0353
theorem accepted0354 : minorantGammaCheck GammaPanel0354.certificate 314=true := by decide +kernel
noncomputable def cell0354 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0354.certificate 314 accepted0354
theorem accepted0355 : minorantGammaCheck GammaPanel0355.certificate 315=true := by decide +kernel
noncomputable def cell0355 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0355.certificate 315 accepted0355
theorem accepted0356 : minorantGammaCheck GammaPanel0356.certificate 316=true := by decide +kernel
noncomputable def cell0356 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0356.certificate 316 accepted0356
theorem accepted0357 : minorantGammaCheck GammaPanel0357.certificate 317=true := by decide +kernel
noncomputable def cell0357 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0357.certificate 317 accepted0357
theorem accepted0358 : minorantGammaCheck GammaPanel0358.certificate 318=true := by decide +kernel
noncomputable def cell0358 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0358.certificate 318 accepted0358
theorem accepted0359 : minorantGammaCheck GammaPanel0359.certificate 319=true := by decide +kernel
noncomputable def cell0359 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0359.certificate 319 accepted0359
noncomputable def cells : List CertifiedMinorantCell := [cell0352, cell0353, cell0354, cell0355, cell0356, cell0357, cell0358, cell0359]
theorem chainAccepted : minorantChainCheck (1269/10000) (257/2000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1269/10000) (257/2000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0044
