import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0046
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0046
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0368 : minorantGammaCheck GammaPanel0368.certificate 328=true := by decide +kernel
noncomputable def cell0368 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0368.certificate 328 accepted0368
theorem accepted0369 : minorantGammaCheck GammaPanel0369.certificate 329=true := by decide +kernel
noncomputable def cell0369 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0369.certificate 329 accepted0369
theorem accepted0370 : minorantGammaCheck GammaPanel0370.certificate 330=true := by decide +kernel
noncomputable def cell0370 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0370.certificate 330 accepted0370
theorem accepted0371 : minorantGammaCheck GammaPanel0371.certificate 331=true := by decide +kernel
noncomputable def cell0371 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0371.certificate 331 accepted0371
theorem accepted0372 : minorantGammaCheck GammaPanel0372.certificate 332=true := by decide +kernel
noncomputable def cell0372 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0372.certificate 332 accepted0372
theorem accepted0373 : minorantGammaCheck GammaPanel0373.certificate 333=true := by decide +kernel
noncomputable def cell0373 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0373.certificate 333 accepted0373
theorem accepted0374 : minorantGammaCheck GammaPanel0374.certificate 334=true := by decide +kernel
noncomputable def cell0374 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0374.certificate 334 accepted0374
theorem accepted0375 : minorantGammaCheck GammaPanel0375.certificate 335=true := by decide +kernel
noncomputable def cell0375 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0375.certificate 335 accepted0375
noncomputable def cells : List CertifiedMinorantCell := [cell0368, cell0369, cell0370, cell0371, cell0372, cell0373, cell0374, cell0375]
theorem chainAccepted : minorantChainCheck (1301/10000) (1317/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1301/10000) (1317/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0046
