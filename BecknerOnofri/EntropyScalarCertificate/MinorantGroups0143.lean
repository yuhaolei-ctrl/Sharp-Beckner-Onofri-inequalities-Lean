import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0143
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0143
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1144 : minorantGammaCheck GammaPanel1144.certificate 1042=true := by decide +kernel
noncomputable def cell1144 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1144.certificate 1042 accepted1144
theorem accepted1145 : minorantGammaCheck GammaPanel1145.certificate 1043=true := by decide +kernel
noncomputable def cell1145 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1145.certificate 1043 accepted1145
theorem accepted1146 : minorantGammaCheck GammaPanel1146.certificate 1044=true := by decide +kernel
noncomputable def cell1146 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1146.certificate 1044 accepted1146
theorem accepted1147 : minorantGammaCheck GammaPanel1147.certificate 1045=true := by decide +kernel
noncomputable def cell1147 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1147.certificate 1045 accepted1147
theorem accepted1148 : minorantGammaCheck GammaPanel1148.certificate 1046=true := by decide +kernel
noncomputable def cell1148 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1148.certificate 1046 accepted1148
theorem accepted1149 : minorantGammaCheck GammaPanel1149.certificate 1047=true := by decide +kernel
noncomputable def cell1149 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1149.certificate 1047 accepted1149
theorem accepted1150 : minorantGammaCheck GammaPanel1150.certificate 1048=true := by decide +kernel
noncomputable def cell1150 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1150.certificate 1048 accepted1150
theorem accepted1151 : minorantGammaCheck GammaPanel1151.certificate 1049=true := by decide +kernel
noncomputable def cell1151 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1151.certificate 1049 accepted1151
noncomputable def cells : List CertifiedMinorantCell := [cell1144, cell1145, cell1146, cell1147, cell1148, cell1149, cell1150, cell1151]
theorem chainAccepted : minorantChainCheck (313/500) (317/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (313/500) (317/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0143
