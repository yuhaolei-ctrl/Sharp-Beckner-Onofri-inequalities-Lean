import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0385
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0385
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted3080 : minorantGammaCheck GammaPanel3080.certificate 1621=true := by decide +kernel
noncomputable def cell3080 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3080.certificate 1621 accepted3080
theorem accepted3081 : minorantGammaCheck GammaPanel3081.certificate 1621=true := by decide +kernel
noncomputable def cell3081 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3081.certificate 1621 accepted3081
theorem accepted3082 : minorantGammaCheck GammaPanel3082.certificate 1621=true := by decide +kernel
noncomputable def cell3082 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3082.certificate 1621 accepted3082
theorem accepted3083 : minorantGammaCheck GammaPanel3083.certificate 1621=true := by decide +kernel
noncomputable def cell3083 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3083.certificate 1621 accepted3083
theorem accepted3084 : minorantGammaCheck GammaPanel3084.certificate 1621=true := by decide +kernel
noncomputable def cell3084 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3084.certificate 1621 accepted3084
theorem accepted3085 : minorantGammaCheck GammaPanel3085.certificate 1621=true := by decide +kernel
noncomputable def cell3085 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3085.certificate 1621 accepted3085
theorem accepted3086 : minorantGammaCheck GammaPanel3086.certificate 1621=true := by decide +kernel
noncomputable def cell3086 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3086.certificate 1621 accepted3086
theorem accepted3087 : minorantGammaCheck GammaPanel3087.certificate 1621=true := by decide +kernel
noncomputable def cell3087 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3087.certificate 1621 accepted3087
noncomputable def cells : List CertifiedMinorantCell := [cell3080, cell3081, cell3082, cell3083, cell3084, cell3085, cell3086, cell3087]
theorem chainAccepted : minorantChainCheck (24969/25000) (2497/2500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24969/25000) (2497/2500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0385
