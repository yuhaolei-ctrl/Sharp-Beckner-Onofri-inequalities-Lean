module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0132

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0132
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1056 : minorantGammaCheck GammaPanel1056.certificate 954=true := by decide +kernel
noncomputable def cell1056 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1056.certificate 954 accepted1056
theorem accepted1057 : minorantGammaCheck GammaPanel1057.certificate 955=true := by decide +kernel
noncomputable def cell1057 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1057.certificate 955 accepted1057
theorem accepted1058 : minorantGammaCheck GammaPanel1058.certificate 956=true := by decide +kernel
noncomputable def cell1058 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1058.certificate 956 accepted1058
theorem accepted1059 : minorantGammaCheck GammaPanel1059.certificate 957=true := by decide +kernel
noncomputable def cell1059 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1059.certificate 957 accepted1059
theorem accepted1060 : minorantGammaCheck GammaPanel1060.certificate 958=true := by decide +kernel
noncomputable def cell1060 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1060.certificate 958 accepted1060
theorem accepted1061 : minorantGammaCheck GammaPanel1061.certificate 959=true := by decide +kernel
noncomputable def cell1061 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1061.certificate 959 accepted1061
theorem accepted1062 : minorantGammaCheck GammaPanel1062.certificate 960=true := by decide +kernel
noncomputable def cell1062 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1062.certificate 960 accepted1062
theorem accepted1063 : minorantGammaCheck GammaPanel1063.certificate 961=true := by decide +kernel
noncomputable def cell1063 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1063.certificate 961 accepted1063
noncomputable def cells : List CertifiedMinorantCell := [cell1056, cell1057, cell1058, cell1059, cell1060, cell1061, cell1062, cell1063]
theorem chainAccepted : minorantChainCheck (269/500) (273/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (269/500) (273/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0132
