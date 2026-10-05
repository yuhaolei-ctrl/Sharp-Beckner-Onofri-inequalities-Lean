module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0148

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0148
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1184 : minorantGammaCheck GammaPanel1184.certificate 1082=true := by decide +kernel
noncomputable def cell1184 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1184.certificate 1082 accepted1184
theorem accepted1185 : minorantGammaCheck GammaPanel1185.certificate 1083=true := by decide +kernel
noncomputable def cell1185 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1185.certificate 1083 accepted1185
theorem accepted1186 : minorantGammaCheck GammaPanel1186.certificate 1084=true := by decide +kernel
noncomputable def cell1186 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1186.certificate 1084 accepted1186
theorem accepted1187 : minorantGammaCheck GammaPanel1187.certificate 1085=true := by decide +kernel
noncomputable def cell1187 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1187.certificate 1085 accepted1187
theorem accepted1188 : minorantGammaCheck GammaPanel1188.certificate 1086=true := by decide +kernel
noncomputable def cell1188 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1188.certificate 1086 accepted1188
theorem accepted1189 : minorantGammaCheck GammaPanel1189.certificate 1087=true := by decide +kernel
noncomputable def cell1189 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1189.certificate 1087 accepted1189
theorem accepted1190 : minorantGammaCheck GammaPanel1190.certificate 1088=true := by decide +kernel
noncomputable def cell1190 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1190.certificate 1088 accepted1190
theorem accepted1191 : minorantGammaCheck GammaPanel1191.certificate 1089=true := by decide +kernel
noncomputable def cell1191 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1191.certificate 1089 accepted1191
noncomputable def cells : List CertifiedMinorantCell := [cell1184, cell1185, cell1186, cell1187, cell1188, cell1189, cell1190, cell1191]
theorem chainAccepted : minorantChainCheck (333/500) (337/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (333/500) (337/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0148
