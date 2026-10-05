import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0047
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0047
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0376 : minorantGammaCheck GammaPanel0376.certificate 336=true := by decide +kernel
noncomputable def cell0376 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0376.certificate 336 accepted0376
theorem accepted0377 : minorantGammaCheck GammaPanel0377.certificate 337=true := by decide +kernel
noncomputable def cell0377 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0377.certificate 337 accepted0377
theorem accepted0378 : minorantGammaCheck GammaPanel0378.certificate 338=true := by decide +kernel
noncomputable def cell0378 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0378.certificate 338 accepted0378
theorem accepted0379 : minorantGammaCheck GammaPanel0379.certificate 339=true := by decide +kernel
noncomputable def cell0379 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0379.certificate 339 accepted0379
theorem accepted0380 : minorantGammaCheck GammaPanel0380.certificate 340=true := by decide +kernel
noncomputable def cell0380 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0380.certificate 340 accepted0380
theorem accepted0381 : minorantGammaCheck GammaPanel0381.certificate 341=true := by decide +kernel
noncomputable def cell0381 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0381.certificate 341 accepted0381
theorem accepted0382 : minorantGammaCheck GammaPanel0382.certificate 342=true := by decide +kernel
noncomputable def cell0382 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0382.certificate 342 accepted0382
theorem accepted0383 : minorantGammaCheck GammaPanel0383.certificate 343=true := by decide +kernel
noncomputable def cell0383 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0383.certificate 343 accepted0383
noncomputable def cells : List CertifiedMinorantCell := [cell0376, cell0377, cell0378, cell0379, cell0380, cell0381, cell0382, cell0383]
theorem chainAccepted : minorantChainCheck (1317/10000) (1333/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1317/10000) (1333/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0047
