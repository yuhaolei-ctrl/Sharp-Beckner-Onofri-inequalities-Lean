import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0258
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0258
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2064 : minorantGammaCheck GammaPanel2064.certificate 1621=true := by decide +kernel
noncomputable def cell2064 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2064.certificate 1621 accepted2064
theorem accepted2065 : minorantGammaCheck GammaPanel2065.certificate 1621=true := by decide +kernel
noncomputable def cell2065 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2065.certificate 1621 accepted2065
theorem accepted2066 : minorantGammaCheck GammaPanel2066.certificate 1621=true := by decide +kernel
noncomputable def cell2066 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2066.certificate 1621 accepted2066
theorem accepted2067 : minorantGammaCheck GammaPanel2067.certificate 1621=true := by decide +kernel
noncomputable def cell2067 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2067.certificate 1621 accepted2067
theorem accepted2068 : minorantGammaCheck GammaPanel2068.certificate 1621=true := by decide +kernel
noncomputable def cell2068 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2068.certificate 1621 accepted2068
theorem accepted2069 : minorantGammaCheck GammaPanel2069.certificate 1621=true := by decide +kernel
noncomputable def cell2069 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2069.certificate 1621 accepted2069
theorem accepted2070 : minorantGammaCheck GammaPanel2070.certificate 1621=true := by decide +kernel
noncomputable def cell2070 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2070.certificate 1621 accepted2070
theorem accepted2071 : minorantGammaCheck GammaPanel2071.certificate 1621=true := by decide +kernel
noncomputable def cell2071 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2071.certificate 1621 accepted2071
noncomputable def cells : List CertifiedMinorantCell := [cell2064, cell2065, cell2066, cell2067, cell2068, cell2069, cell2070, cell2071]
theorem chainAccepted : minorantChainCheck (4793/5000) (4797/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4793/5000) (4797/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0258
