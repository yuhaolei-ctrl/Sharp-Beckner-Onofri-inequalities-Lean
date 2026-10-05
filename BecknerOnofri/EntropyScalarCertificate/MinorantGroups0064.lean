module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0064

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0064
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0512 : minorantGammaCheck GammaPanel0512.certificate 472=true := by decide +kernel
noncomputable def cell0512 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0512.certificate 472 accepted0512
theorem accepted0513 : minorantGammaCheck GammaPanel0513.certificate 473=true := by decide +kernel
noncomputable def cell0513 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0513.certificate 473 accepted0513
theorem accepted0514 : minorantGammaCheck GammaPanel0514.certificate 474=true := by decide +kernel
noncomputable def cell0514 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0514.certificate 474 accepted0514
theorem accepted0515 : minorantGammaCheck GammaPanel0515.certificate 475=true := by decide +kernel
noncomputable def cell0515 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0515.certificate 475 accepted0515
theorem accepted0516 : minorantGammaCheck GammaPanel0516.certificate 476=true := by decide +kernel
noncomputable def cell0516 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0516.certificate 476 accepted0516
theorem accepted0517 : minorantGammaCheck GammaPanel0517.certificate 477=true := by decide +kernel
noncomputable def cell0517 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0517.certificate 477 accepted0517
theorem accepted0518 : minorantGammaCheck GammaPanel0518.certificate 478=true := by decide +kernel
noncomputable def cell0518 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0518.certificate 478 accepted0518
theorem accepted0519 : minorantGammaCheck GammaPanel0519.certificate 479=true := by decide +kernel
noncomputable def cell0519 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0519.certificate 479 accepted0519
noncomputable def cells : List CertifiedMinorantCell := [cell0512, cell0513, cell0514, cell0515, cell0516, cell0517, cell0518, cell0519]
theorem chainAccepted : minorantChainCheck (1589/10000) (321/2000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1589/10000) (321/2000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0064
