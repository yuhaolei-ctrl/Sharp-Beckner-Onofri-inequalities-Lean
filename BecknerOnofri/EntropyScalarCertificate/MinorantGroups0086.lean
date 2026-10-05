module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0086

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0086
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0688 : minorantGammaCheck GammaPanel0688.certificate 616=true := by decide +kernel
noncomputable def cell0688 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0688.certificate 616 accepted0688
theorem accepted0689 : minorantGammaCheck GammaPanel0689.certificate 616=true := by decide +kernel
noncomputable def cell0689 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0689.certificate 616 accepted0689
theorem accepted0690 : minorantGammaCheck GammaPanel0690.certificate 616=true := by decide +kernel
noncomputable def cell0690 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0690.certificate 616 accepted0690
theorem accepted0691 : minorantGammaCheck GammaPanel0691.certificate 616=true := by decide +kernel
noncomputable def cell0691 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0691.certificate 616 accepted0691
theorem accepted0692 : minorantGammaCheck GammaPanel0692.certificate 616=true := by decide +kernel
noncomputable def cell0692 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0692.certificate 616 accepted0692
theorem accepted0693 : minorantGammaCheck GammaPanel0693.certificate 616=true := by decide +kernel
noncomputable def cell0693 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0693.certificate 616 accepted0693
theorem accepted0694 : minorantGammaCheck GammaPanel0694.certificate 616=true := by decide +kernel
noncomputable def cell0694 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0694.certificate 616 accepted0694
theorem accepted0695 : minorantGammaCheck GammaPanel0695.certificate 616=true := by decide +kernel
noncomputable def cell0695 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0695.certificate 616 accepted0695
noncomputable def cells : List CertifiedMinorantCell := [cell0688, cell0689, cell0690, cell0691, cell0692, cell0693, cell0694, cell0695]
theorem chainAccepted : minorantChainCheck (1941/10000) (1957/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1941/10000) (1957/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0086
