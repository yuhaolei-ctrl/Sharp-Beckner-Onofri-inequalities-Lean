module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0159

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0159
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1272 : minorantGammaCheck GammaPanel1272.certificate 1170=true := by decide +kernel
noncomputable def cell1272 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1272.certificate 1170 accepted1272
theorem accepted1273 : minorantGammaCheck GammaPanel1273.certificate 1171=true := by decide +kernel
noncomputable def cell1273 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1273.certificate 1171 accepted1273
theorem accepted1274 : minorantGammaCheck GammaPanel1274.certificate 1172=true := by decide +kernel
noncomputable def cell1274 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1274.certificate 1172 accepted1274
theorem accepted1275 : minorantGammaCheck GammaPanel1275.certificate 1173=true := by decide +kernel
noncomputable def cell1275 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1275.certificate 1173 accepted1275
theorem accepted1276 : minorantGammaCheck GammaPanel1276.certificate 1174=true := by decide +kernel
noncomputable def cell1276 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1276.certificate 1174 accepted1276
theorem accepted1277 : minorantGammaCheck GammaPanel1277.certificate 1175=true := by decide +kernel
noncomputable def cell1277 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1277.certificate 1175 accepted1277
theorem accepted1278 : minorantGammaCheck GammaPanel1278.certificate 1176=true := by decide +kernel
noncomputable def cell1278 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1278.certificate 1176 accepted1278
theorem accepted1279 : minorantGammaCheck GammaPanel1279.certificate 1177=true := by decide +kernel
noncomputable def cell1279 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1279.certificate 1177 accepted1279
noncomputable def cells : List CertifiedMinorantCell := [cell1272, cell1273, cell1274, cell1275, cell1276, cell1277, cell1278, cell1279]
theorem chainAccepted : minorantChainCheck (377/500) (381/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (377/500) (381/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0159
