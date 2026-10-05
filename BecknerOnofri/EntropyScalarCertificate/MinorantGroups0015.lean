import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0015
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0015
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0120 : minorantGammaCheck GammaPanel0120.certificate 80=true := by decide +kernel
noncomputable def cell0120 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0120.certificate 80 accepted0120
theorem accepted0121 : minorantGammaCheck GammaPanel0121.certificate 81=true := by decide +kernel
noncomputable def cell0121 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0121.certificate 81 accepted0121
theorem accepted0122 : minorantGammaCheck GammaPanel0122.certificate 82=true := by decide +kernel
noncomputable def cell0122 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0122.certificate 82 accepted0122
theorem accepted0123 : minorantGammaCheck GammaPanel0123.certificate 83=true := by decide +kernel
noncomputable def cell0123 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0123.certificate 83 accepted0123
theorem accepted0124 : minorantGammaCheck GammaPanel0124.certificate 84=true := by decide +kernel
noncomputable def cell0124 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0124.certificate 84 accepted0124
theorem accepted0125 : minorantGammaCheck GammaPanel0125.certificate 85=true := by decide +kernel
noncomputable def cell0125 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0125.certificate 85 accepted0125
theorem accepted0126 : minorantGammaCheck GammaPanel0126.certificate 86=true := by decide +kernel
noncomputable def cell0126 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0126.certificate 86 accepted0126
theorem accepted0127 : minorantGammaCheck GammaPanel0127.certificate 87=true := by decide +kernel
noncomputable def cell0127 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0127.certificate 87 accepted0127
noncomputable def cells : List CertifiedMinorantCell := [cell0120, cell0121, cell0122, cell0123, cell0124, cell0125, cell0126, cell0127]
theorem chainAccepted : minorantChainCheck (161/2000) (821/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (161/2000) (821/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0015
