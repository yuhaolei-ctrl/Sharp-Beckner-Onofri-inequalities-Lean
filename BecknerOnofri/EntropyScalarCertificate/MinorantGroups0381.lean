import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0381
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0381
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted3048 : minorantGammaCheck GammaPanel3048.certificate 1621=true := by decide +kernel
noncomputable def cell3048 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3048.certificate 1621 accepted3048
theorem accepted3049 : minorantGammaCheck GammaPanel3049.certificate 1621=true := by decide +kernel
noncomputable def cell3049 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3049.certificate 1621 accepted3049
theorem accepted3050 : minorantGammaCheck GammaPanel3050.certificate 1621=true := by decide +kernel
noncomputable def cell3050 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3050.certificate 1621 accepted3050
theorem accepted3051 : minorantGammaCheck GammaPanel3051.certificate 1621=true := by decide +kernel
noncomputable def cell3051 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3051.certificate 1621 accepted3051
theorem accepted3052 : minorantGammaCheck GammaPanel3052.certificate 1621=true := by decide +kernel
noncomputable def cell3052 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3052.certificate 1621 accepted3052
theorem accepted3053 : minorantGammaCheck GammaPanel3053.certificate 1621=true := by decide +kernel
noncomputable def cell3053 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3053.certificate 1621 accepted3053
theorem accepted3054 : minorantGammaCheck GammaPanel3054.certificate 1621=true := by decide +kernel
noncomputable def cell3054 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3054.certificate 1621 accepted3054
theorem accepted3055 : minorantGammaCheck GammaPanel3055.certificate 1621=true := by decide +kernel
noncomputable def cell3055 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3055.certificate 1621 accepted3055
noncomputable def cells : List CertifiedMinorantCell := [cell3048, cell3049, cell3050, cell3051, cell3052, cell3053, cell3054, cell3055]
theorem chainAccepted : minorantChainCheck (4993/5000) (12483/12500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4993/5000) (12483/12500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0381
