module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0111

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0111
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0888 : minorantGammaCheck GammaPanel0888.certificate 786=true := by decide +kernel
noncomputable def cell0888 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0888.certificate 786 accepted0888
theorem accepted0889 : minorantGammaCheck GammaPanel0889.certificate 787=true := by decide +kernel
noncomputable def cell0889 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0889.certificate 787 accepted0889
theorem accepted0890 : minorantGammaCheck GammaPanel0890.certificate 788=true := by decide +kernel
noncomputable def cell0890 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0890.certificate 788 accepted0890
theorem accepted0891 : minorantGammaCheck GammaPanel0891.certificate 789=true := by decide +kernel
noncomputable def cell0891 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0891.certificate 789 accepted0891
theorem accepted0892 : minorantGammaCheck GammaPanel0892.certificate 790=true := by decide +kernel
noncomputable def cell0892 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0892.certificate 790 accepted0892
theorem accepted0893 : minorantGammaCheck GammaPanel0893.certificate 791=true := by decide +kernel
noncomputable def cell0893 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0893.certificate 791 accepted0893
theorem accepted0894 : minorantGammaCheck GammaPanel0894.certificate 792=true := by decide +kernel
noncomputable def cell0894 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0894.certificate 792 accepted0894
theorem accepted0895 : minorantGammaCheck GammaPanel0895.certificate 793=true := by decide +kernel
noncomputable def cell0895 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0895.certificate 793 accepted0895
noncomputable def cells : List CertifiedMinorantCell := [cell0888, cell0889, cell0890, cell0891, cell0892, cell0893, cell0894, cell0895]
theorem chainAccepted : minorantChainCheck (37/100) (189/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (37/100) (189/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0111
