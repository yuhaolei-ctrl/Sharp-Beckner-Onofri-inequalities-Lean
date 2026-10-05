module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0135

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0135
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1080 : minorantGammaCheck GammaPanel1080.certificate 978=true := by decide +kernel
noncomputable def cell1080 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1080.certificate 978 accepted1080
theorem accepted1081 : minorantGammaCheck GammaPanel1081.certificate 979=true := by decide +kernel
noncomputable def cell1081 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1081.certificate 979 accepted1081
theorem accepted1082 : minorantGammaCheck GammaPanel1082.certificate 980=true := by decide +kernel
noncomputable def cell1082 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1082.certificate 980 accepted1082
theorem accepted1083 : minorantGammaCheck GammaPanel1083.certificate 981=true := by decide +kernel
noncomputable def cell1083 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1083.certificate 981 accepted1083
theorem accepted1084 : minorantGammaCheck GammaPanel1084.certificate 982=true := by decide +kernel
noncomputable def cell1084 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1084.certificate 982 accepted1084
theorem accepted1085 : minorantGammaCheck GammaPanel1085.certificate 983=true := by decide +kernel
noncomputable def cell1085 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1085.certificate 983 accepted1085
theorem accepted1086 : minorantGammaCheck GammaPanel1086.certificate 984=true := by decide +kernel
noncomputable def cell1086 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1086.certificate 984 accepted1086
theorem accepted1087 : minorantGammaCheck GammaPanel1087.certificate 985=true := by decide +kernel
noncomputable def cell1087 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1087.certificate 985 accepted1087
noncomputable def cells : List CertifiedMinorantCell := [cell1080, cell1081, cell1082, cell1083, cell1084, cell1085, cell1086, cell1087]
theorem chainAccepted : minorantChainCheck (281/500) (57/100) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (281/500) (57/100) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0135
