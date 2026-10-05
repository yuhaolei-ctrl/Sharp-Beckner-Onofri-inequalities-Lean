module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0134

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0134
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1072 : minorantGammaCheck GammaPanel1072.certificate 970=true := by decide +kernel
noncomputable def cell1072 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1072.certificate 970 accepted1072
theorem accepted1073 : minorantGammaCheck GammaPanel1073.certificate 971=true := by decide +kernel
noncomputable def cell1073 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1073.certificate 971 accepted1073
theorem accepted1074 : minorantGammaCheck GammaPanel1074.certificate 972=true := by decide +kernel
noncomputable def cell1074 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1074.certificate 972 accepted1074
theorem accepted1075 : minorantGammaCheck GammaPanel1075.certificate 973=true := by decide +kernel
noncomputable def cell1075 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1075.certificate 973 accepted1075
theorem accepted1076 : minorantGammaCheck GammaPanel1076.certificate 974=true := by decide +kernel
noncomputable def cell1076 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1076.certificate 974 accepted1076
theorem accepted1077 : minorantGammaCheck GammaPanel1077.certificate 975=true := by decide +kernel
noncomputable def cell1077 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1077.certificate 975 accepted1077
theorem accepted1078 : minorantGammaCheck GammaPanel1078.certificate 976=true := by decide +kernel
noncomputable def cell1078 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1078.certificate 976 accepted1078
theorem accepted1079 : minorantGammaCheck GammaPanel1079.certificate 977=true := by decide +kernel
noncomputable def cell1079 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1079.certificate 977 accepted1079
noncomputable def cells : List CertifiedMinorantCell := [cell1072, cell1073, cell1074, cell1075, cell1076, cell1077, cell1078, cell1079]
theorem chainAccepted : minorantChainCheck (277/500) (281/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (277/500) (281/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0134
