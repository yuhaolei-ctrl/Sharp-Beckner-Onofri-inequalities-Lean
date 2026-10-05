module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0093

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0093
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0744 : minorantGammaCheck GammaPanel0744.certificate 642=true := by decide +kernel
noncomputable def cell0744 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0744.certificate 642 accepted0744
theorem accepted0745 : minorantGammaCheck GammaPanel0745.certificate 643=true := by decide +kernel
noncomputable def cell0745 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0745.certificate 643 accepted0745
theorem accepted0746 : minorantGammaCheck GammaPanel0746.certificate 644=true := by decide +kernel
noncomputable def cell0746 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0746.certificate 644 accepted0746
theorem accepted0747 : minorantGammaCheck GammaPanel0747.certificate 645=true := by decide +kernel
noncomputable def cell0747 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0747.certificate 645 accepted0747
theorem accepted0748 : minorantGammaCheck GammaPanel0748.certificate 646=true := by decide +kernel
noncomputable def cell0748 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0748.certificate 646 accepted0748
theorem accepted0749 : minorantGammaCheck GammaPanel0749.certificate 647=true := by decide +kernel
noncomputable def cell0749 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0749.certificate 647 accepted0749
theorem accepted0750 : minorantGammaCheck GammaPanel0750.certificate 648=true := by decide +kernel
noncomputable def cell0750 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0750.certificate 648 accepted0750
theorem accepted0751 : minorantGammaCheck GammaPanel0751.certificate 649=true := by decide +kernel
noncomputable def cell0751 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0751.certificate 649 accepted0751
noncomputable def cells : List CertifiedMinorantCell := [cell0744, cell0745, cell0746, cell0747, cell0748, cell0749, cell0750, cell0751]
theorem chainAccepted : minorantChainCheck (113/500) (117/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (113/500) (117/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0093
