import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0379
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0379
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted3032 : minorantGammaCheck GammaPanel3032.certificate 1621=true := by decide +kernel
noncomputable def cell3032 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3032.certificate 1621 accepted3032
theorem accepted3033 : minorantGammaCheck GammaPanel3033.certificate 1621=true := by decide +kernel
noncomputable def cell3033 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3033.certificate 1621 accepted3033
theorem accepted3034 : minorantGammaCheck GammaPanel3034.certificate 1621=true := by decide +kernel
noncomputable def cell3034 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3034.certificate 1621 accepted3034
theorem accepted3035 : minorantGammaCheck GammaPanel3035.certificate 1621=true := by decide +kernel
noncomputable def cell3035 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3035.certificate 1621 accepted3035
theorem accepted3036 : minorantGammaCheck GammaPanel3036.certificate 1621=true := by decide +kernel
noncomputable def cell3036 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3036.certificate 1621 accepted3036
theorem accepted3037 : minorantGammaCheck GammaPanel3037.certificate 1621=true := by decide +kernel
noncomputable def cell3037 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3037.certificate 1621 accepted3037
theorem accepted3038 : minorantGammaCheck GammaPanel3038.certificate 1621=true := by decide +kernel
noncomputable def cell3038 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3038.certificate 1621 accepted3038
theorem accepted3039 : minorantGammaCheck GammaPanel3039.certificate 1621=true := by decide +kernel
noncomputable def cell3039 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3039.certificate 1621 accepted3039
noncomputable def cells : List CertifiedMinorantCell := [cell3032, cell3033, cell3034, cell3035, cell3036, cell3037, cell3038, cell3039]
theorem chainAccepted : minorantChainCheck (24963/25000) (6241/6250) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24963/25000) (6241/6250) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0379
