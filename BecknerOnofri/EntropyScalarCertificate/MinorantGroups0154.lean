module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0154

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0154
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1232 : minorantGammaCheck GammaPanel1232.certificate 1130=true := by decide +kernel
noncomputable def cell1232 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1232.certificate 1130 accepted1232
theorem accepted1233 : minorantGammaCheck GammaPanel1233.certificate 1131=true := by decide +kernel
noncomputable def cell1233 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1233.certificate 1131 accepted1233
theorem accepted1234 : minorantGammaCheck GammaPanel1234.certificate 1132=true := by decide +kernel
noncomputable def cell1234 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1234.certificate 1132 accepted1234
theorem accepted1235 : minorantGammaCheck GammaPanel1235.certificate 1133=true := by decide +kernel
noncomputable def cell1235 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1235.certificate 1133 accepted1235
theorem accepted1236 : minorantGammaCheck GammaPanel1236.certificate 1134=true := by decide +kernel
noncomputable def cell1236 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1236.certificate 1134 accepted1236
theorem accepted1237 : minorantGammaCheck GammaPanel1237.certificate 1135=true := by decide +kernel
noncomputable def cell1237 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1237.certificate 1135 accepted1237
theorem accepted1238 : minorantGammaCheck GammaPanel1238.certificate 1136=true := by decide +kernel
noncomputable def cell1238 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1238.certificate 1136 accepted1238
theorem accepted1239 : minorantGammaCheck GammaPanel1239.certificate 1137=true := by decide +kernel
noncomputable def cell1239 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1239.certificate 1137 accepted1239
noncomputable def cells : List CertifiedMinorantCell := [cell1232, cell1233, cell1234, cell1235, cell1236, cell1237, cell1238, cell1239]
theorem chainAccepted : minorantChainCheck (357/500) (361/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (357/500) (361/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0154
