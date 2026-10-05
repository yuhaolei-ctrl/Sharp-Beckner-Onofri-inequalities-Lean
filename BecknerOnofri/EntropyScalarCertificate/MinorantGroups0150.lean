import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0150
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0150
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1200 : minorantGammaCheck GammaPanel1200.certificate 1098=true := by decide +kernel
noncomputable def cell1200 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1200.certificate 1098 accepted1200
theorem accepted1201 : minorantGammaCheck GammaPanel1201.certificate 1099=true := by decide +kernel
noncomputable def cell1201 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1201.certificate 1099 accepted1201
theorem accepted1202 : minorantGammaCheck GammaPanel1202.certificate 1100=true := by decide +kernel
noncomputable def cell1202 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1202.certificate 1100 accepted1202
theorem accepted1203 : minorantGammaCheck GammaPanel1203.certificate 1101=true := by decide +kernel
noncomputable def cell1203 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1203.certificate 1101 accepted1203
theorem accepted1204 : minorantGammaCheck GammaPanel1204.certificate 1102=true := by decide +kernel
noncomputable def cell1204 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1204.certificate 1102 accepted1204
theorem accepted1205 : minorantGammaCheck GammaPanel1205.certificate 1103=true := by decide +kernel
noncomputable def cell1205 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1205.certificate 1103 accepted1205
theorem accepted1206 : minorantGammaCheck GammaPanel1206.certificate 1104=true := by decide +kernel
noncomputable def cell1206 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1206.certificate 1104 accepted1206
theorem accepted1207 : minorantGammaCheck GammaPanel1207.certificate 1105=true := by decide +kernel
noncomputable def cell1207 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1207.certificate 1105 accepted1207
noncomputable def cells : List CertifiedMinorantCell := [cell1200, cell1201, cell1202, cell1203, cell1204, cell1205, cell1206, cell1207]
theorem chainAccepted : minorantChainCheck (341/500) (69/100) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (341/500) (69/100) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0150
