module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0142

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0142
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1136 : minorantGammaCheck GammaPanel1136.certificate 1034=true := by decide +kernel
noncomputable def cell1136 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1136.certificate 1034 accepted1136
theorem accepted1137 : minorantGammaCheck GammaPanel1137.certificate 1035=true := by decide +kernel
noncomputable def cell1137 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1137.certificate 1035 accepted1137
theorem accepted1138 : minorantGammaCheck GammaPanel1138.certificate 1036=true := by decide +kernel
noncomputable def cell1138 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1138.certificate 1036 accepted1138
theorem accepted1139 : minorantGammaCheck GammaPanel1139.certificate 1037=true := by decide +kernel
noncomputable def cell1139 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1139.certificate 1037 accepted1139
theorem accepted1140 : minorantGammaCheck GammaPanel1140.certificate 1038=true := by decide +kernel
noncomputable def cell1140 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1140.certificate 1038 accepted1140
theorem accepted1141 : minorantGammaCheck GammaPanel1141.certificate 1039=true := by decide +kernel
noncomputable def cell1141 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1141.certificate 1039 accepted1141
theorem accepted1142 : minorantGammaCheck GammaPanel1142.certificate 1040=true := by decide +kernel
noncomputable def cell1142 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1142.certificate 1040 accepted1142
theorem accepted1143 : minorantGammaCheck GammaPanel1143.certificate 1041=true := by decide +kernel
noncomputable def cell1143 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1143.certificate 1041 accepted1143
noncomputable def cells : List CertifiedMinorantCell := [cell1136, cell1137, cell1138, cell1139, cell1140, cell1141, cell1142, cell1143]
theorem chainAccepted : minorantChainCheck (309/500) (313/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (309/500) (313/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0142
