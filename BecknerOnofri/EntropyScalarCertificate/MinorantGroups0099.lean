module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0099

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0099
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0792 : minorantGammaCheck GammaPanel0792.certificate 690=true := by decide +kernel
noncomputable def cell0792 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0792.certificate 690 accepted0792
theorem accepted0793 : minorantGammaCheck GammaPanel0793.certificate 691=true := by decide +kernel
noncomputable def cell0793 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0793.certificate 691 accepted0793
theorem accepted0794 : minorantGammaCheck GammaPanel0794.certificate 692=true := by decide +kernel
noncomputable def cell0794 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0794.certificate 692 accepted0794
theorem accepted0795 : minorantGammaCheck GammaPanel0795.certificate 693=true := by decide +kernel
noncomputable def cell0795 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0795.certificate 693 accepted0795
theorem accepted0796 : minorantGammaCheck GammaPanel0796.certificate 694=true := by decide +kernel
noncomputable def cell0796 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0796.certificate 694 accepted0796
theorem accepted0797 : minorantGammaCheck GammaPanel0797.certificate 695=true := by decide +kernel
noncomputable def cell0797 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0797.certificate 695 accepted0797
theorem accepted0798 : minorantGammaCheck GammaPanel0798.certificate 696=true := by decide +kernel
noncomputable def cell0798 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0798.certificate 696 accepted0798
theorem accepted0799 : minorantGammaCheck GammaPanel0799.certificate 697=true := by decide +kernel
noncomputable def cell0799 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0799.certificate 697 accepted0799
noncomputable def cells : List CertifiedMinorantCell := [cell0792, cell0793, cell0794, cell0795, cell0796, cell0797, cell0798, cell0799]
theorem chainAccepted : minorantChainCheck (137/500) (141/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (137/500) (141/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0099
