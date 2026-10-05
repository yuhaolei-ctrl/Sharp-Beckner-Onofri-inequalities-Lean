module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0138

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0138
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1104 : minorantGammaCheck GammaPanel1104.certificate 1002=true := by decide +kernel
noncomputable def cell1104 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1104.certificate 1002 accepted1104
theorem accepted1105 : minorantGammaCheck GammaPanel1105.certificate 1003=true := by decide +kernel
noncomputable def cell1105 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1105.certificate 1003 accepted1105
theorem accepted1106 : minorantGammaCheck GammaPanel1106.certificate 1004=true := by decide +kernel
noncomputable def cell1106 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1106.certificate 1004 accepted1106
theorem accepted1107 : minorantGammaCheck GammaPanel1107.certificate 1005=true := by decide +kernel
noncomputable def cell1107 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1107.certificate 1005 accepted1107
theorem accepted1108 : minorantGammaCheck GammaPanel1108.certificate 1006=true := by decide +kernel
noncomputable def cell1108 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1108.certificate 1006 accepted1108
theorem accepted1109 : minorantGammaCheck GammaPanel1109.certificate 1007=true := by decide +kernel
noncomputable def cell1109 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1109.certificate 1007 accepted1109
theorem accepted1110 : minorantGammaCheck GammaPanel1110.certificate 1008=true := by decide +kernel
noncomputable def cell1110 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1110.certificate 1008 accepted1110
theorem accepted1111 : minorantGammaCheck GammaPanel1111.certificate 1009=true := by decide +kernel
noncomputable def cell1111 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1111.certificate 1009 accepted1111
noncomputable def cells : List CertifiedMinorantCell := [cell1104, cell1105, cell1106, cell1107, cell1108, cell1109, cell1110, cell1111]
theorem chainAccepted : minorantChainCheck (293/500) (297/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (293/500) (297/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0138
