import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0257
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0257
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2056 : minorantGammaCheck GammaPanel2056.certificate 1621=true := by decide +kernel
noncomputable def cell2056 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2056.certificate 1621 accepted2056
theorem accepted2057 : minorantGammaCheck GammaPanel2057.certificate 1621=true := by decide +kernel
noncomputable def cell2057 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2057.certificate 1621 accepted2057
theorem accepted2058 : minorantGammaCheck GammaPanel2058.certificate 1621=true := by decide +kernel
noncomputable def cell2058 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2058.certificate 1621 accepted2058
theorem accepted2059 : minorantGammaCheck GammaPanel2059.certificate 1621=true := by decide +kernel
noncomputable def cell2059 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2059.certificate 1621 accepted2059
theorem accepted2060 : minorantGammaCheck GammaPanel2060.certificate 1621=true := by decide +kernel
noncomputable def cell2060 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2060.certificate 1621 accepted2060
theorem accepted2061 : minorantGammaCheck GammaPanel2061.certificate 1621=true := by decide +kernel
noncomputable def cell2061 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2061.certificate 1621 accepted2061
theorem accepted2062 : minorantGammaCheck GammaPanel2062.certificate 1621=true := by decide +kernel
noncomputable def cell2062 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2062.certificate 1621 accepted2062
theorem accepted2063 : minorantGammaCheck GammaPanel2063.certificate 1621=true := by decide +kernel
noncomputable def cell2063 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2063.certificate 1621 accepted2063
noncomputable def cells : List CertifiedMinorantCell := [cell2056, cell2057, cell2058, cell2059, cell2060, cell2061, cell2062, cell2063]
theorem chainAccepted : minorantChainCheck (4789/5000) (4793/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4789/5000) (4793/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0257
