import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0054
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0054
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0432 : minorantGammaCheck GammaPanel0432.certificate 392=true := by decide +kernel
noncomputable def cell0432 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0432.certificate 392 accepted0432
theorem accepted0433 : minorantGammaCheck GammaPanel0433.certificate 393=true := by decide +kernel
noncomputable def cell0433 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0433.certificate 393 accepted0433
theorem accepted0434 : minorantGammaCheck GammaPanel0434.certificate 394=true := by decide +kernel
noncomputable def cell0434 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0434.certificate 394 accepted0434
theorem accepted0435 : minorantGammaCheck GammaPanel0435.certificate 395=true := by decide +kernel
noncomputable def cell0435 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0435.certificate 395 accepted0435
theorem accepted0436 : minorantGammaCheck GammaPanel0436.certificate 396=true := by decide +kernel
noncomputable def cell0436 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0436.certificate 396 accepted0436
theorem accepted0437 : minorantGammaCheck GammaPanel0437.certificate 397=true := by decide +kernel
noncomputable def cell0437 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0437.certificate 397 accepted0437
theorem accepted0438 : minorantGammaCheck GammaPanel0438.certificate 398=true := by decide +kernel
noncomputable def cell0438 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0438.certificate 398 accepted0438
theorem accepted0439 : minorantGammaCheck GammaPanel0439.certificate 399=true := by decide +kernel
noncomputable def cell0439 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0439.certificate 399 accepted0439
noncomputable def cells : List CertifiedMinorantCell := [cell0432, cell0433, cell0434, cell0435, cell0436, cell0437, cell0438, cell0439]
theorem chainAccepted : minorantChainCheck (1429/10000) (289/2000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1429/10000) (289/2000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0054
