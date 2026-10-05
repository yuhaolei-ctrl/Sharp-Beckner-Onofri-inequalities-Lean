module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0074

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0074
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0592 : minorantGammaCheck GammaPanel0592.certificate 552=true := by decide +kernel
noncomputable def cell0592 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0592.certificate 552 accepted0592
theorem accepted0593 : minorantGammaCheck GammaPanel0593.certificate 553=true := by decide +kernel
noncomputable def cell0593 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0593.certificate 553 accepted0593
theorem accepted0594 : minorantGammaCheck GammaPanel0594.certificate 554=true := by decide +kernel
noncomputable def cell0594 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0594.certificate 554 accepted0594
theorem accepted0595 : minorantGammaCheck GammaPanel0595.certificate 555=true := by decide +kernel
noncomputable def cell0595 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0595.certificate 555 accepted0595
theorem accepted0596 : minorantGammaCheck GammaPanel0596.certificate 556=true := by decide +kernel
noncomputable def cell0596 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0596.certificate 556 accepted0596
theorem accepted0597 : minorantGammaCheck GammaPanel0597.certificate 557=true := by decide +kernel
noncomputable def cell0597 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0597.certificate 557 accepted0597
theorem accepted0598 : minorantGammaCheck GammaPanel0598.certificate 558=true := by decide +kernel
noncomputable def cell0598 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0598.certificate 558 accepted0598
theorem accepted0599 : minorantGammaCheck GammaPanel0599.certificate 559=true := by decide +kernel
noncomputable def cell0599 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0599.certificate 559 accepted0599
noncomputable def cells : List CertifiedMinorantCell := [cell0592, cell0593, cell0594, cell0595, cell0596, cell0597, cell0598, cell0599]
theorem chainAccepted : minorantChainCheck (1749/10000) (353/2000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1749/10000) (353/2000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0074
