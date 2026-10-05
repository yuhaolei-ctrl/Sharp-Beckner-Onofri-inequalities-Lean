import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0266
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0266
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2128 : minorantGammaCheck GammaPanel2128.certificate 1621=true := by decide +kernel
noncomputable def cell2128 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2128.certificate 1621 accepted2128
theorem accepted2129 : minorantGammaCheck GammaPanel2129.certificate 1621=true := by decide +kernel
noncomputable def cell2129 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2129.certificate 1621 accepted2129
theorem accepted2130 : minorantGammaCheck GammaPanel2130.certificate 1621=true := by decide +kernel
noncomputable def cell2130 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2130.certificate 1621 accepted2130
theorem accepted2131 : minorantGammaCheck GammaPanel2131.certificate 1621=true := by decide +kernel
noncomputable def cell2131 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2131.certificate 1621 accepted2131
theorem accepted2132 : minorantGammaCheck GammaPanel2132.certificate 1621=true := by decide +kernel
noncomputable def cell2132 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2132.certificate 1621 accepted2132
theorem accepted2133 : minorantGammaCheck GammaPanel2133.certificate 1621=true := by decide +kernel
noncomputable def cell2133 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2133.certificate 1621 accepted2133
theorem accepted2134 : minorantGammaCheck GammaPanel2134.certificate 1621=true := by decide +kernel
noncomputable def cell2134 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2134.certificate 1621 accepted2134
theorem accepted2135 : minorantGammaCheck GammaPanel2135.certificate 1621=true := by decide +kernel
noncomputable def cell2135 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2135.certificate 1621 accepted2135
noncomputable def cells : List CertifiedMinorantCell := [cell2128, cell2129, cell2130, cell2131, cell2132, cell2133, cell2134, cell2135]
theorem chainAccepted : minorantChainCheck (193/200) (4829/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (193/200) (4829/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0266
