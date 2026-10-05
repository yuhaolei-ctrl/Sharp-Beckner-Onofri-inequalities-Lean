import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0264
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0264
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2112 : minorantGammaCheck GammaPanel2112.certificate 1621=true := by decide +kernel
noncomputable def cell2112 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2112.certificate 1621 accepted2112
theorem accepted2113 : minorantGammaCheck GammaPanel2113.certificate 1621=true := by decide +kernel
noncomputable def cell2113 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2113.certificate 1621 accepted2113
theorem accepted2114 : minorantGammaCheck GammaPanel2114.certificate 1621=true := by decide +kernel
noncomputable def cell2114 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2114.certificate 1621 accepted2114
theorem accepted2115 : minorantGammaCheck GammaPanel2115.certificate 1621=true := by decide +kernel
noncomputable def cell2115 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2115.certificate 1621 accepted2115
theorem accepted2116 : minorantGammaCheck GammaPanel2116.certificate 1621=true := by decide +kernel
noncomputable def cell2116 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2116.certificate 1621 accepted2116
theorem accepted2117 : minorantGammaCheck GammaPanel2117.certificate 1621=true := by decide +kernel
noncomputable def cell2117 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2117.certificate 1621 accepted2117
theorem accepted2118 : minorantGammaCheck GammaPanel2118.certificate 1621=true := by decide +kernel
noncomputable def cell2118 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2118.certificate 1621 accepted2118
theorem accepted2119 : minorantGammaCheck GammaPanel2119.certificate 1621=true := by decide +kernel
noncomputable def cell2119 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2119.certificate 1621 accepted2119
noncomputable def cells : List CertifiedMinorantCell := [cell2112, cell2113, cell2114, cell2115, cell2116, cell2117, cell2118, cell2119]
theorem chainAccepted : minorantChainCheck (4817/5000) (4821/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4817/5000) (4821/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0264
