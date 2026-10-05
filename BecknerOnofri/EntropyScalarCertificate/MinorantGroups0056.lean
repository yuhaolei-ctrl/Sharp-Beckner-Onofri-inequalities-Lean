import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0056
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0056
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0448 : minorantGammaCheck GammaPanel0448.certificate 408=true := by decide +kernel
noncomputable def cell0448 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0448.certificate 408 accepted0448
theorem accepted0449 : minorantGammaCheck GammaPanel0449.certificate 409=true := by decide +kernel
noncomputable def cell0449 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0449.certificate 409 accepted0449
theorem accepted0450 : minorantGammaCheck GammaPanel0450.certificate 410=true := by decide +kernel
noncomputable def cell0450 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0450.certificate 410 accepted0450
theorem accepted0451 : minorantGammaCheck GammaPanel0451.certificate 411=true := by decide +kernel
noncomputable def cell0451 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0451.certificate 411 accepted0451
theorem accepted0452 : minorantGammaCheck GammaPanel0452.certificate 412=true := by decide +kernel
noncomputable def cell0452 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0452.certificate 412 accepted0452
theorem accepted0453 : minorantGammaCheck GammaPanel0453.certificate 413=true := by decide +kernel
noncomputable def cell0453 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0453.certificate 413 accepted0453
theorem accepted0454 : minorantGammaCheck GammaPanel0454.certificate 414=true := by decide +kernel
noncomputable def cell0454 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0454.certificate 414 accepted0454
theorem accepted0455 : minorantGammaCheck GammaPanel0455.certificate 415=true := by decide +kernel
noncomputable def cell0455 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0455.certificate 415 accepted0455
noncomputable def cells : List CertifiedMinorantCell := [cell0448, cell0449, cell0450, cell0451, cell0452, cell0453, cell0454, cell0455]
theorem chainAccepted : minorantChainCheck (1461/10000) (1477/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1461/10000) (1477/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0056
