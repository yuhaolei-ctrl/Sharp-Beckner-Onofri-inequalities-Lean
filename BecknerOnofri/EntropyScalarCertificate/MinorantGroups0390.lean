import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0390
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0390
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted3120 : minorantGammaCheck GammaPanel3120.certificate 1621=true := by decide +kernel
noncomputable def cell3120 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3120.certificate 1621 accepted3120
theorem accepted3121 : minorantGammaCheck GammaPanel3121.certificate 1621=true := by decide +kernel
noncomputable def cell3121 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3121.certificate 1621 accepted3121
theorem accepted3122 : minorantGammaCheck GammaPanel3122.certificate 1621=true := by decide +kernel
noncomputable def cell3122 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3122.certificate 1621 accepted3122
theorem accepted3123 : minorantGammaCheck GammaPanel3123.certificate 1621=true := by decide +kernel
noncomputable def cell3123 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3123.certificate 1621 accepted3123
theorem accepted3124 : minorantGammaCheck GammaPanel3124.certificate 1621=true := by decide +kernel
noncomputable def cell3124 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3124.certificate 1621 accepted3124
theorem accepted3125 : minorantGammaCheck GammaPanel3125.certificate 1621=true := by decide +kernel
noncomputable def cell3125 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3125.certificate 1621 accepted3125
theorem accepted3126 : minorantGammaCheck GammaPanel3126.certificate 1621=true := by decide +kernel
noncomputable def cell3126 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3126.certificate 1621 accepted3126
theorem accepted3127 : minorantGammaCheck GammaPanel3127.certificate 1621=true := by decide +kernel
noncomputable def cell3127 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3127.certificate 1621 accepted3127
noncomputable def cells : List CertifiedMinorantCell := [cell3120, cell3121, cell3122, cell3123, cell3124, cell3125, cell3126, cell3127]
theorem chainAccepted : minorantChainCheck (12487/12500) (999/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (12487/12500) (999/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0390
