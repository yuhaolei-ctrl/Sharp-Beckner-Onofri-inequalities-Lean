module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0152

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0152
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1216 : minorantGammaCheck GammaPanel1216.certificate 1114=true := by decide +kernel
noncomputable def cell1216 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1216.certificate 1114 accepted1216
theorem accepted1217 : minorantGammaCheck GammaPanel1217.certificate 1115=true := by decide +kernel
noncomputable def cell1217 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1217.certificate 1115 accepted1217
theorem accepted1218 : minorantGammaCheck GammaPanel1218.certificate 1116=true := by decide +kernel
noncomputable def cell1218 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1218.certificate 1116 accepted1218
theorem accepted1219 : minorantGammaCheck GammaPanel1219.certificate 1117=true := by decide +kernel
noncomputable def cell1219 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1219.certificate 1117 accepted1219
theorem accepted1220 : minorantGammaCheck GammaPanel1220.certificate 1118=true := by decide +kernel
noncomputable def cell1220 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1220.certificate 1118 accepted1220
theorem accepted1221 : minorantGammaCheck GammaPanel1221.certificate 1119=true := by decide +kernel
noncomputable def cell1221 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1221.certificate 1119 accepted1221
theorem accepted1222 : minorantGammaCheck GammaPanel1222.certificate 1120=true := by decide +kernel
noncomputable def cell1222 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1222.certificate 1120 accepted1222
theorem accepted1223 : minorantGammaCheck GammaPanel1223.certificate 1121=true := by decide +kernel
noncomputable def cell1223 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1223.certificate 1121 accepted1223
noncomputable def cells : List CertifiedMinorantCell := [cell1216, cell1217, cell1218, cell1219, cell1220, cell1221, cell1222, cell1223]
theorem chainAccepted : minorantChainCheck (349/500) (353/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (349/500) (353/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0152
