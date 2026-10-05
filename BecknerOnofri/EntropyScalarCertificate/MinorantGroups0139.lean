import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0139
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0139
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1112 : minorantGammaCheck GammaPanel1112.certificate 1010=true := by decide +kernel
noncomputable def cell1112 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1112.certificate 1010 accepted1112
theorem accepted1113 : minorantGammaCheck GammaPanel1113.certificate 1011=true := by decide +kernel
noncomputable def cell1113 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1113.certificate 1011 accepted1113
theorem accepted1114 : minorantGammaCheck GammaPanel1114.certificate 1012=true := by decide +kernel
noncomputable def cell1114 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1114.certificate 1012 accepted1114
theorem accepted1115 : minorantGammaCheck GammaPanel1115.certificate 1013=true := by decide +kernel
noncomputable def cell1115 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1115.certificate 1013 accepted1115
theorem accepted1116 : minorantGammaCheck GammaPanel1116.certificate 1014=true := by decide +kernel
noncomputable def cell1116 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1116.certificate 1014 accepted1116
theorem accepted1117 : minorantGammaCheck GammaPanel1117.certificate 1015=true := by decide +kernel
noncomputable def cell1117 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1117.certificate 1015 accepted1117
theorem accepted1118 : minorantGammaCheck GammaPanel1118.certificate 1016=true := by decide +kernel
noncomputable def cell1118 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1118.certificate 1016 accepted1118
theorem accepted1119 : minorantGammaCheck GammaPanel1119.certificate 1017=true := by decide +kernel
noncomputable def cell1119 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1119.certificate 1017 accepted1119
noncomputable def cells : List CertifiedMinorantCell := [cell1112, cell1113, cell1114, cell1115, cell1116, cell1117, cell1118, cell1119]
theorem chainAccepted : minorantChainCheck (297/500) (301/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (297/500) (301/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0139
