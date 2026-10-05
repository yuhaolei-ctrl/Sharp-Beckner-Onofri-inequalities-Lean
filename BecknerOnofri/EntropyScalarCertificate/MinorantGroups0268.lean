import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0268
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0268
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2144 : minorantGammaCheck GammaPanel2144.certificate 1621=true := by decide +kernel
noncomputable def cell2144 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2144.certificate 1621 accepted2144
theorem accepted2145 : minorantGammaCheck GammaPanel2145.certificate 1621=true := by decide +kernel
noncomputable def cell2145 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2145.certificate 1621 accepted2145
theorem accepted2146 : minorantGammaCheck GammaPanel2146.certificate 1621=true := by decide +kernel
noncomputable def cell2146 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2146.certificate 1621 accepted2146
theorem accepted2147 : minorantGammaCheck GammaPanel2147.certificate 1621=true := by decide +kernel
noncomputable def cell2147 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2147.certificate 1621 accepted2147
theorem accepted2148 : minorantGammaCheck GammaPanel2148.certificate 1621=true := by decide +kernel
noncomputable def cell2148 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2148.certificate 1621 accepted2148
theorem accepted2149 : minorantGammaCheck GammaPanel2149.certificate 1621=true := by decide +kernel
noncomputable def cell2149 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2149.certificate 1621 accepted2149
theorem accepted2150 : minorantGammaCheck GammaPanel2150.certificate 1621=true := by decide +kernel
noncomputable def cell2150 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2150.certificate 1621 accepted2150
theorem accepted2151 : minorantGammaCheck GammaPanel2151.certificate 1621=true := by decide +kernel
noncomputable def cell2151 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2151.certificate 1621 accepted2151
noncomputable def cells : List CertifiedMinorantCell := [cell2144, cell2145, cell2146, cell2147, cell2148, cell2149, cell2150, cell2151]
theorem chainAccepted : minorantChainCheck (4833/5000) (4837/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4833/5000) (4837/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0268
