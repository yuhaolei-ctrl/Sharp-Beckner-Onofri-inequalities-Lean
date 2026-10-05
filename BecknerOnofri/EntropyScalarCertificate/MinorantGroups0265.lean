import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0265
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0265
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2120 : minorantGammaCheck GammaPanel2120.certificate 1621=true := by decide +kernel
noncomputable def cell2120 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2120.certificate 1621 accepted2120
theorem accepted2121 : minorantGammaCheck GammaPanel2121.certificate 1621=true := by decide +kernel
noncomputable def cell2121 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2121.certificate 1621 accepted2121
theorem accepted2122 : minorantGammaCheck GammaPanel2122.certificate 1621=true := by decide +kernel
noncomputable def cell2122 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2122.certificate 1621 accepted2122
theorem accepted2123 : minorantGammaCheck GammaPanel2123.certificate 1621=true := by decide +kernel
noncomputable def cell2123 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2123.certificate 1621 accepted2123
theorem accepted2124 : minorantGammaCheck GammaPanel2124.certificate 1621=true := by decide +kernel
noncomputable def cell2124 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2124.certificate 1621 accepted2124
theorem accepted2125 : minorantGammaCheck GammaPanel2125.certificate 1621=true := by decide +kernel
noncomputable def cell2125 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2125.certificate 1621 accepted2125
theorem accepted2126 : minorantGammaCheck GammaPanel2126.certificate 1621=true := by decide +kernel
noncomputable def cell2126 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2126.certificate 1621 accepted2126
theorem accepted2127 : minorantGammaCheck GammaPanel2127.certificate 1621=true := by decide +kernel
noncomputable def cell2127 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2127.certificate 1621 accepted2127
noncomputable def cells : List CertifiedMinorantCell := [cell2120, cell2121, cell2122, cell2123, cell2124, cell2125, cell2126, cell2127]
theorem chainAccepted : minorantChainCheck (4821/5000) (193/200) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4821/5000) (193/200) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0265
