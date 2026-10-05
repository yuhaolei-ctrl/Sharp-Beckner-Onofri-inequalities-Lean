module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0114

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0114
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0912 : minorantGammaCheck GammaPanel0912.certificate 810=true := by decide +kernel
noncomputable def cell0912 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0912.certificate 810 accepted0912
theorem accepted0913 : minorantGammaCheck GammaPanel0913.certificate 811=true := by decide +kernel
noncomputable def cell0913 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0913.certificate 811 accepted0913
theorem accepted0914 : minorantGammaCheck GammaPanel0914.certificate 812=true := by decide +kernel
noncomputable def cell0914 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0914.certificate 812 accepted0914
theorem accepted0915 : minorantGammaCheck GammaPanel0915.certificate 813=true := by decide +kernel
noncomputable def cell0915 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0915.certificate 813 accepted0915
theorem accepted0916 : minorantGammaCheck GammaPanel0916.certificate 814=true := by decide +kernel
noncomputable def cell0916 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0916.certificate 814 accepted0916
theorem accepted0917 : minorantGammaCheck GammaPanel0917.certificate 815=true := by decide +kernel
noncomputable def cell0917 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0917.certificate 815 accepted0917
theorem accepted0918 : minorantGammaCheck GammaPanel0918.certificate 816=true := by decide +kernel
noncomputable def cell0918 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0918.certificate 816 accepted0918
theorem accepted0919 : minorantGammaCheck GammaPanel0919.certificate 817=true := by decide +kernel
noncomputable def cell0919 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0919.certificate 817 accepted0919
noncomputable def cells : List CertifiedMinorantCell := [cell0912, cell0913, cell0914, cell0915, cell0916, cell0917, cell0918, cell0919]
theorem chainAccepted : minorantChainCheck (197/500) (201/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (197/500) (201/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0114
