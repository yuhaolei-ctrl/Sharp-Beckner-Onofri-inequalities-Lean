import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0049
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0049
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0392 : minorantGammaCheck GammaPanel0392.certificate 352=true := by decide +kernel
noncomputable def cell0392 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0392.certificate 352 accepted0392
theorem accepted0393 : minorantGammaCheck GammaPanel0393.certificate 353=true := by decide +kernel
noncomputable def cell0393 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0393.certificate 353 accepted0393
theorem accepted0394 : minorantGammaCheck GammaPanel0394.certificate 354=true := by decide +kernel
noncomputable def cell0394 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0394.certificate 354 accepted0394
theorem accepted0395 : minorantGammaCheck GammaPanel0395.certificate 355=true := by decide +kernel
noncomputable def cell0395 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0395.certificate 355 accepted0395
theorem accepted0396 : minorantGammaCheck GammaPanel0396.certificate 356=true := by decide +kernel
noncomputable def cell0396 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0396.certificate 356 accepted0396
theorem accepted0397 : minorantGammaCheck GammaPanel0397.certificate 357=true := by decide +kernel
noncomputable def cell0397 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0397.certificate 357 accepted0397
theorem accepted0398 : minorantGammaCheck GammaPanel0398.certificate 358=true := by decide +kernel
noncomputable def cell0398 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0398.certificate 358 accepted0398
theorem accepted0399 : minorantGammaCheck GammaPanel0399.certificate 359=true := by decide +kernel
noncomputable def cell0399 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0399.certificate 359 accepted0399
noncomputable def cells : List CertifiedMinorantCell := [cell0392, cell0393, cell0394, cell0395, cell0396, cell0397, cell0398, cell0399]
theorem chainAccepted : minorantChainCheck (1349/10000) (273/2000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1349/10000) (273/2000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0049
