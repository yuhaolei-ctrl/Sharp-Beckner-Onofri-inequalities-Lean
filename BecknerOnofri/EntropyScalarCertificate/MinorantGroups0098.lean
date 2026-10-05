module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0098

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0098
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0784 : minorantGammaCheck GammaPanel0784.certificate 682=true := by decide +kernel
noncomputable def cell0784 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0784.certificate 682 accepted0784
theorem accepted0785 : minorantGammaCheck GammaPanel0785.certificate 683=true := by decide +kernel
noncomputable def cell0785 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0785.certificate 683 accepted0785
theorem accepted0786 : minorantGammaCheck GammaPanel0786.certificate 684=true := by decide +kernel
noncomputable def cell0786 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0786.certificate 684 accepted0786
theorem accepted0787 : minorantGammaCheck GammaPanel0787.certificate 685=true := by decide +kernel
noncomputable def cell0787 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0787.certificate 685 accepted0787
theorem accepted0788 : minorantGammaCheck GammaPanel0788.certificate 686=true := by decide +kernel
noncomputable def cell0788 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0788.certificate 686 accepted0788
theorem accepted0789 : minorantGammaCheck GammaPanel0789.certificate 687=true := by decide +kernel
noncomputable def cell0789 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0789.certificate 687 accepted0789
theorem accepted0790 : minorantGammaCheck GammaPanel0790.certificate 688=true := by decide +kernel
noncomputable def cell0790 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0790.certificate 688 accepted0790
theorem accepted0791 : minorantGammaCheck GammaPanel0791.certificate 689=true := by decide +kernel
noncomputable def cell0791 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0791.certificate 689 accepted0791
noncomputable def cells : List CertifiedMinorantCell := [cell0784, cell0785, cell0786, cell0787, cell0788, cell0789, cell0790, cell0791]
theorem chainAccepted : minorantChainCheck (133/500) (137/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (133/500) (137/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0098
