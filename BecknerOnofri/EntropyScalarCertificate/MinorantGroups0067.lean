module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0067

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0067
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0536 : minorantGammaCheck GammaPanel0536.certificate 496=true := by decide +kernel
noncomputable def cell0536 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0536.certificate 496 accepted0536
theorem accepted0537 : minorantGammaCheck GammaPanel0537.certificate 497=true := by decide +kernel
noncomputable def cell0537 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0537.certificate 497 accepted0537
theorem accepted0538 : minorantGammaCheck GammaPanel0538.certificate 498=true := by decide +kernel
noncomputable def cell0538 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0538.certificate 498 accepted0538
theorem accepted0539 : minorantGammaCheck GammaPanel0539.certificate 499=true := by decide +kernel
noncomputable def cell0539 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0539.certificate 499 accepted0539
theorem accepted0540 : minorantGammaCheck GammaPanel0540.certificate 500=true := by decide +kernel
noncomputable def cell0540 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0540.certificate 500 accepted0540
theorem accepted0541 : minorantGammaCheck GammaPanel0541.certificate 501=true := by decide +kernel
noncomputable def cell0541 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0541.certificate 501 accepted0541
theorem accepted0542 : minorantGammaCheck GammaPanel0542.certificate 502=true := by decide +kernel
noncomputable def cell0542 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0542.certificate 502 accepted0542
theorem accepted0543 : minorantGammaCheck GammaPanel0543.certificate 503=true := by decide +kernel
noncomputable def cell0543 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0543.certificate 503 accepted0543
noncomputable def cells : List CertifiedMinorantCell := [cell0536, cell0537, cell0538, cell0539, cell0540, cell0541, cell0542, cell0543]
theorem chainAccepted : minorantChainCheck (1637/10000) (1653/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1637/10000) (1653/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0067
