module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0145

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0145
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1160 : minorantGammaCheck GammaPanel1160.certificate 1058=true := by decide +kernel
noncomputable def cell1160 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1160.certificate 1058 accepted1160
theorem accepted1161 : minorantGammaCheck GammaPanel1161.certificate 1059=true := by decide +kernel
noncomputable def cell1161 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1161.certificate 1059 accepted1161
theorem accepted1162 : minorantGammaCheck GammaPanel1162.certificate 1060=true := by decide +kernel
noncomputable def cell1162 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1162.certificate 1060 accepted1162
theorem accepted1163 : minorantGammaCheck GammaPanel1163.certificate 1061=true := by decide +kernel
noncomputable def cell1163 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1163.certificate 1061 accepted1163
theorem accepted1164 : minorantGammaCheck GammaPanel1164.certificate 1062=true := by decide +kernel
noncomputable def cell1164 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1164.certificate 1062 accepted1164
theorem accepted1165 : minorantGammaCheck GammaPanel1165.certificate 1063=true := by decide +kernel
noncomputable def cell1165 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1165.certificate 1063 accepted1165
theorem accepted1166 : minorantGammaCheck GammaPanel1166.certificate 1064=true := by decide +kernel
noncomputable def cell1166 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1166.certificate 1064 accepted1166
theorem accepted1167 : minorantGammaCheck GammaPanel1167.certificate 1065=true := by decide +kernel
noncomputable def cell1167 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1167.certificate 1065 accepted1167
noncomputable def cells : List CertifiedMinorantCell := [cell1160, cell1161, cell1162, cell1163, cell1164, cell1165, cell1166, cell1167]
theorem chainAccepted : minorantChainCheck (321/500) (13/20) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (321/500) (13/20) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0145
