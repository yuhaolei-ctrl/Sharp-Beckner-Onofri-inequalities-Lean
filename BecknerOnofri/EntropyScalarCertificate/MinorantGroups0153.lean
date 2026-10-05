module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0153

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0153
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1224 : minorantGammaCheck GammaPanel1224.certificate 1122=true := by decide +kernel
noncomputable def cell1224 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1224.certificate 1122 accepted1224
theorem accepted1225 : minorantGammaCheck GammaPanel1225.certificate 1123=true := by decide +kernel
noncomputable def cell1225 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1225.certificate 1123 accepted1225
theorem accepted1226 : minorantGammaCheck GammaPanel1226.certificate 1124=true := by decide +kernel
noncomputable def cell1226 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1226.certificate 1124 accepted1226
theorem accepted1227 : minorantGammaCheck GammaPanel1227.certificate 1125=true := by decide +kernel
noncomputable def cell1227 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1227.certificate 1125 accepted1227
theorem accepted1228 : minorantGammaCheck GammaPanel1228.certificate 1126=true := by decide +kernel
noncomputable def cell1228 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1228.certificate 1126 accepted1228
theorem accepted1229 : minorantGammaCheck GammaPanel1229.certificate 1127=true := by decide +kernel
noncomputable def cell1229 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1229.certificate 1127 accepted1229
theorem accepted1230 : minorantGammaCheck GammaPanel1230.certificate 1128=true := by decide +kernel
noncomputable def cell1230 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1230.certificate 1128 accepted1230
theorem accepted1231 : minorantGammaCheck GammaPanel1231.certificate 1129=true := by decide +kernel
noncomputable def cell1231 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1231.certificate 1129 accepted1231
noncomputable def cells : List CertifiedMinorantCell := [cell1224, cell1225, cell1226, cell1227, cell1228, cell1229, cell1230, cell1231]
theorem chainAccepted : minorantChainCheck (353/500) (357/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (353/500) (357/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0153
