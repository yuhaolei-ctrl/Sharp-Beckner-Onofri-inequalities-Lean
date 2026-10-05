import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0271
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0271
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2168 : minorantGammaCheck GammaPanel2168.certificate 1621=true := by decide +kernel
noncomputable def cell2168 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2168.certificate 1621 accepted2168
theorem accepted2169 : minorantGammaCheck GammaPanel2169.certificate 1621=true := by decide +kernel
noncomputable def cell2169 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2169.certificate 1621 accepted2169
theorem accepted2170 : minorantGammaCheck GammaPanel2170.certificate 1621=true := by decide +kernel
noncomputable def cell2170 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2170.certificate 1621 accepted2170
theorem accepted2171 : minorantGammaCheck GammaPanel2171.certificate 1621=true := by decide +kernel
noncomputable def cell2171 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2171.certificate 1621 accepted2171
theorem accepted2172 : minorantGammaCheck GammaPanel2172.certificate 1621=true := by decide +kernel
noncomputable def cell2172 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2172.certificate 1621 accepted2172
theorem accepted2173 : minorantGammaCheck GammaPanel2173.certificate 1621=true := by decide +kernel
noncomputable def cell2173 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2173.certificate 1621 accepted2173
theorem accepted2174 : minorantGammaCheck GammaPanel2174.certificate 1621=true := by decide +kernel
noncomputable def cell2174 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2174.certificate 1621 accepted2174
theorem accepted2175 : minorantGammaCheck GammaPanel2175.certificate 1621=true := by decide +kernel
noncomputable def cell2175 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2175.certificate 1621 accepted2175
noncomputable def cells : List CertifiedMinorantCell := [cell2168, cell2169, cell2170, cell2171, cell2172, cell2173, cell2174, cell2175]
theorem chainAccepted : minorantChainCheck (969/1000) (4849/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (969/1000) (4849/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0271
