module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0095

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0095
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0760 : minorantGammaCheck GammaPanel0760.certificate 658=true := by decide +kernel
noncomputable def cell0760 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0760.certificate 658 accepted0760
theorem accepted0761 : minorantGammaCheck GammaPanel0761.certificate 659=true := by decide +kernel
noncomputable def cell0761 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0761.certificate 659 accepted0761
theorem accepted0762 : minorantGammaCheck GammaPanel0762.certificate 660=true := by decide +kernel
noncomputable def cell0762 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0762.certificate 660 accepted0762
theorem accepted0763 : minorantGammaCheck GammaPanel0763.certificate 661=true := by decide +kernel
noncomputable def cell0763 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0763.certificate 661 accepted0763
theorem accepted0764 : minorantGammaCheck GammaPanel0764.certificate 662=true := by decide +kernel
noncomputable def cell0764 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0764.certificate 662 accepted0764
theorem accepted0765 : minorantGammaCheck GammaPanel0765.certificate 663=true := by decide +kernel
noncomputable def cell0765 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0765.certificate 663 accepted0765
theorem accepted0766 : minorantGammaCheck GammaPanel0766.certificate 664=true := by decide +kernel
noncomputable def cell0766 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0766.certificate 664 accepted0766
theorem accepted0767 : minorantGammaCheck GammaPanel0767.certificate 665=true := by decide +kernel
noncomputable def cell0767 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0767.certificate 665 accepted0767
noncomputable def cells : List CertifiedMinorantCell := [cell0760, cell0761, cell0762, cell0763, cell0764, cell0765, cell0766, cell0767]
theorem chainAccepted : minorantChainCheck (121/500) (1/4) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (121/500) (1/4) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0095
