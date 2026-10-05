import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0140
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0140
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1120 : minorantGammaCheck GammaPanel1120.certificate 1018=true := by decide +kernel
noncomputable def cell1120 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1120.certificate 1018 accepted1120
theorem accepted1121 : minorantGammaCheck GammaPanel1121.certificate 1019=true := by decide +kernel
noncomputable def cell1121 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1121.certificate 1019 accepted1121
theorem accepted1122 : minorantGammaCheck GammaPanel1122.certificate 1020=true := by decide +kernel
noncomputable def cell1122 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1122.certificate 1020 accepted1122
theorem accepted1123 : minorantGammaCheck GammaPanel1123.certificate 1021=true := by decide +kernel
noncomputable def cell1123 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1123.certificate 1021 accepted1123
theorem accepted1124 : minorantGammaCheck GammaPanel1124.certificate 1022=true := by decide +kernel
noncomputable def cell1124 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1124.certificate 1022 accepted1124
theorem accepted1125 : minorantGammaCheck GammaPanel1125.certificate 1023=true := by decide +kernel
noncomputable def cell1125 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1125.certificate 1023 accepted1125
theorem accepted1126 : minorantGammaCheck GammaPanel1126.certificate 1024=true := by decide +kernel
noncomputable def cell1126 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1126.certificate 1024 accepted1126
theorem accepted1127 : minorantGammaCheck GammaPanel1127.certificate 1025=true := by decide +kernel
noncomputable def cell1127 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1127.certificate 1025 accepted1127
noncomputable def cells : List CertifiedMinorantCell := [cell1120, cell1121, cell1122, cell1123, cell1124, cell1125, cell1126, cell1127]
theorem chainAccepted : minorantChainCheck (301/500) (61/100) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (301/500) (61/100) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0140
