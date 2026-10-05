module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0146

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0146
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1168 : minorantGammaCheck GammaPanel1168.certificate 1066=true := by decide +kernel
noncomputable def cell1168 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1168.certificate 1066 accepted1168
theorem accepted1169 : minorantGammaCheck GammaPanel1169.certificate 1067=true := by decide +kernel
noncomputable def cell1169 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1169.certificate 1067 accepted1169
theorem accepted1170 : minorantGammaCheck GammaPanel1170.certificate 1068=true := by decide +kernel
noncomputable def cell1170 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1170.certificate 1068 accepted1170
theorem accepted1171 : minorantGammaCheck GammaPanel1171.certificate 1069=true := by decide +kernel
noncomputable def cell1171 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1171.certificate 1069 accepted1171
theorem accepted1172 : minorantGammaCheck GammaPanel1172.certificate 1070=true := by decide +kernel
noncomputable def cell1172 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1172.certificate 1070 accepted1172
theorem accepted1173 : minorantGammaCheck GammaPanel1173.certificate 1071=true := by decide +kernel
noncomputable def cell1173 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1173.certificate 1071 accepted1173
theorem accepted1174 : minorantGammaCheck GammaPanel1174.certificate 1072=true := by decide +kernel
noncomputable def cell1174 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1174.certificate 1072 accepted1174
theorem accepted1175 : minorantGammaCheck GammaPanel1175.certificate 1073=true := by decide +kernel
noncomputable def cell1175 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1175.certificate 1073 accepted1175
noncomputable def cells : List CertifiedMinorantCell := [cell1168, cell1169, cell1170, cell1171, cell1172, cell1173, cell1174, cell1175]
theorem chainAccepted : minorantChainCheck (13/20) (329/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (13/20) (329/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0146
