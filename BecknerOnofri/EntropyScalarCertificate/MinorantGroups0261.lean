import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0261
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0261
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2088 : minorantGammaCheck GammaPanel2088.certificate 1621=true := by decide +kernel
noncomputable def cell2088 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2088.certificate 1621 accepted2088
theorem accepted2089 : minorantGammaCheck GammaPanel2089.certificate 1621=true := by decide +kernel
noncomputable def cell2089 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2089.certificate 1621 accepted2089
theorem accepted2090 : minorantGammaCheck GammaPanel2090.certificate 1621=true := by decide +kernel
noncomputable def cell2090 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2090.certificate 1621 accepted2090
theorem accepted2091 : minorantGammaCheck GammaPanel2091.certificate 1621=true := by decide +kernel
noncomputable def cell2091 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2091.certificate 1621 accepted2091
theorem accepted2092 : minorantGammaCheck GammaPanel2092.certificate 1621=true := by decide +kernel
noncomputable def cell2092 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2092.certificate 1621 accepted2092
theorem accepted2093 : minorantGammaCheck GammaPanel2093.certificate 1621=true := by decide +kernel
noncomputable def cell2093 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2093.certificate 1621 accepted2093
theorem accepted2094 : minorantGammaCheck GammaPanel2094.certificate 1621=true := by decide +kernel
noncomputable def cell2094 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2094.certificate 1621 accepted2094
theorem accepted2095 : minorantGammaCheck GammaPanel2095.certificate 1621=true := by decide +kernel
noncomputable def cell2095 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2095.certificate 1621 accepted2095
noncomputable def cells : List CertifiedMinorantCell := [cell2088, cell2089, cell2090, cell2091, cell2092, cell2093, cell2094, cell2095]
theorem chainAccepted : minorantChainCheck (961/1000) (4809/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (961/1000) (4809/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0261
