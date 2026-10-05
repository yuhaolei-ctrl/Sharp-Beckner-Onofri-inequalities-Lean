module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0052

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0052
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0416 : minorantGammaCheck GammaPanel0416.certificate 376=true := by decide +kernel
noncomputable def cell0416 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0416.certificate 376 accepted0416
theorem accepted0417 : minorantGammaCheck GammaPanel0417.certificate 377=true := by decide +kernel
noncomputable def cell0417 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0417.certificate 377 accepted0417
theorem accepted0418 : minorantGammaCheck GammaPanel0418.certificate 378=true := by decide +kernel
noncomputable def cell0418 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0418.certificate 378 accepted0418
theorem accepted0419 : minorantGammaCheck GammaPanel0419.certificate 379=true := by decide +kernel
noncomputable def cell0419 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0419.certificate 379 accepted0419
theorem accepted0420 : minorantGammaCheck GammaPanel0420.certificate 380=true := by decide +kernel
noncomputable def cell0420 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0420.certificate 380 accepted0420
theorem accepted0421 : minorantGammaCheck GammaPanel0421.certificate 381=true := by decide +kernel
noncomputable def cell0421 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0421.certificate 381 accepted0421
theorem accepted0422 : minorantGammaCheck GammaPanel0422.certificate 382=true := by decide +kernel
noncomputable def cell0422 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0422.certificate 382 accepted0422
theorem accepted0423 : minorantGammaCheck GammaPanel0423.certificate 383=true := by decide +kernel
noncomputable def cell0423 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0423.certificate 383 accepted0423
noncomputable def cells : List CertifiedMinorantCell := [cell0416, cell0417, cell0418, cell0419, cell0420, cell0421, cell0422, cell0423]
theorem chainAccepted : minorantChainCheck (1397/10000) (1413/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1397/10000) (1413/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0052
