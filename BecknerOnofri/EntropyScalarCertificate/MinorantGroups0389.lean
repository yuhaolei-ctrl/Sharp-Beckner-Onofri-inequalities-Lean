import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0389
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0389
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted3112 : minorantGammaCheck GammaPanel3112.certificate 1621=true := by decide +kernel
noncomputable def cell3112 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3112.certificate 1621 accepted3112
theorem accepted3113 : minorantGammaCheck GammaPanel3113.certificate 1621=true := by decide +kernel
noncomputable def cell3113 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3113.certificate 1621 accepted3113
theorem accepted3114 : minorantGammaCheck GammaPanel3114.certificate 1621=true := by decide +kernel
noncomputable def cell3114 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3114.certificate 1621 accepted3114
theorem accepted3115 : minorantGammaCheck GammaPanel3115.certificate 1621=true := by decide +kernel
noncomputable def cell3115 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3115.certificate 1621 accepted3115
theorem accepted3116 : minorantGammaCheck GammaPanel3116.certificate 1621=true := by decide +kernel
noncomputable def cell3116 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3116.certificate 1621 accepted3116
theorem accepted3117 : minorantGammaCheck GammaPanel3117.certificate 1621=true := by decide +kernel
noncomputable def cell3117 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3117.certificate 1621 accepted3117
theorem accepted3118 : minorantGammaCheck GammaPanel3118.certificate 1621=true := by decide +kernel
noncomputable def cell3118 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3118.certificate 1621 accepted3118
theorem accepted3119 : minorantGammaCheck GammaPanel3119.certificate 1621=true := by decide +kernel
noncomputable def cell3119 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3119.certificate 1621 accepted3119
noncomputable def cells : List CertifiedMinorantCell := [cell3112, cell3113, cell3114, cell3115, cell3116, cell3117, cell3118, cell3119]
theorem chainAccepted : minorantChainCheck (24973/25000) (12487/12500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24973/25000) (12487/12500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0389
