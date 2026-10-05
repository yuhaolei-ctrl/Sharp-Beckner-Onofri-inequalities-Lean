module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0147

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0147
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1176 : minorantGammaCheck GammaPanel1176.certificate 1074=true := by decide +kernel
noncomputable def cell1176 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1176.certificate 1074 accepted1176
theorem accepted1177 : minorantGammaCheck GammaPanel1177.certificate 1075=true := by decide +kernel
noncomputable def cell1177 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1177.certificate 1075 accepted1177
theorem accepted1178 : minorantGammaCheck GammaPanel1178.certificate 1076=true := by decide +kernel
noncomputable def cell1178 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1178.certificate 1076 accepted1178
theorem accepted1179 : minorantGammaCheck GammaPanel1179.certificate 1077=true := by decide +kernel
noncomputable def cell1179 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1179.certificate 1077 accepted1179
theorem accepted1180 : minorantGammaCheck GammaPanel1180.certificate 1078=true := by decide +kernel
noncomputable def cell1180 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1180.certificate 1078 accepted1180
theorem accepted1181 : minorantGammaCheck GammaPanel1181.certificate 1079=true := by decide +kernel
noncomputable def cell1181 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1181.certificate 1079 accepted1181
theorem accepted1182 : minorantGammaCheck GammaPanel1182.certificate 1080=true := by decide +kernel
noncomputable def cell1182 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1182.certificate 1080 accepted1182
theorem accepted1183 : minorantGammaCheck GammaPanel1183.certificate 1081=true := by decide +kernel
noncomputable def cell1183 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1183.certificate 1081 accepted1183
noncomputable def cells : List CertifiedMinorantCell := [cell1176, cell1177, cell1178, cell1179, cell1180, cell1181, cell1182, cell1183]
theorem chainAccepted : minorantChainCheck (329/500) (333/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (329/500) (333/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0147
