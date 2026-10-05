import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0051
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0051
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0408 : minorantGammaCheck GammaPanel0408.certificate 368=true := by decide +kernel
noncomputable def cell0408 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0408.certificate 368 accepted0408
theorem accepted0409 : minorantGammaCheck GammaPanel0409.certificate 369=true := by decide +kernel
noncomputable def cell0409 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0409.certificate 369 accepted0409
theorem accepted0410 : minorantGammaCheck GammaPanel0410.certificate 370=true := by decide +kernel
noncomputable def cell0410 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0410.certificate 370 accepted0410
theorem accepted0411 : minorantGammaCheck GammaPanel0411.certificate 371=true := by decide +kernel
noncomputable def cell0411 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0411.certificate 371 accepted0411
theorem accepted0412 : minorantGammaCheck GammaPanel0412.certificate 372=true := by decide +kernel
noncomputable def cell0412 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0412.certificate 372 accepted0412
theorem accepted0413 : minorantGammaCheck GammaPanel0413.certificate 373=true := by decide +kernel
noncomputable def cell0413 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0413.certificate 373 accepted0413
theorem accepted0414 : minorantGammaCheck GammaPanel0414.certificate 374=true := by decide +kernel
noncomputable def cell0414 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0414.certificate 374 accepted0414
theorem accepted0415 : minorantGammaCheck GammaPanel0415.certificate 375=true := by decide +kernel
noncomputable def cell0415 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0415.certificate 375 accepted0415
noncomputable def cells : List CertifiedMinorantCell := [cell0408, cell0409, cell0410, cell0411, cell0412, cell0413, cell0414, cell0415]
theorem chainAccepted : minorantChainCheck (1381/10000) (1397/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1381/10000) (1397/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0051
