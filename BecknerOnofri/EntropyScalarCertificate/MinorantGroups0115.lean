import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0115
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0115
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0920 : minorantGammaCheck GammaPanel0920.certificate 818=true := by decide +kernel
noncomputable def cell0920 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0920.certificate 818 accepted0920
theorem accepted0921 : minorantGammaCheck GammaPanel0921.certificate 819=true := by decide +kernel
noncomputable def cell0921 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0921.certificate 819 accepted0921
theorem accepted0922 : minorantGammaCheck GammaPanel0922.certificate 820=true := by decide +kernel
noncomputable def cell0922 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0922.certificate 820 accepted0922
theorem accepted0923 : minorantGammaCheck GammaPanel0923.certificate 821=true := by decide +kernel
noncomputable def cell0923 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0923.certificate 821 accepted0923
theorem accepted0924 : minorantGammaCheck GammaPanel0924.certificate 822=true := by decide +kernel
noncomputable def cell0924 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0924.certificate 822 accepted0924
theorem accepted0925 : minorantGammaCheck GammaPanel0925.certificate 823=true := by decide +kernel
noncomputable def cell0925 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0925.certificate 823 accepted0925
theorem accepted0926 : minorantGammaCheck GammaPanel0926.certificate 824=true := by decide +kernel
noncomputable def cell0926 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0926.certificate 824 accepted0926
theorem accepted0927 : minorantGammaCheck GammaPanel0927.certificate 825=true := by decide +kernel
noncomputable def cell0927 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0927.certificate 825 accepted0927
noncomputable def cells : List CertifiedMinorantCell := [cell0920, cell0921, cell0922, cell0923, cell0924, cell0925, cell0926, cell0927]
theorem chainAccepted : minorantChainCheck (201/500) (41/100) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (201/500) (41/100) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0115
