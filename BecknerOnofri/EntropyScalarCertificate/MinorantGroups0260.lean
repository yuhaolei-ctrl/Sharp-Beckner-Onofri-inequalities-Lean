import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0260
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0260
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2080 : minorantGammaCheck GammaPanel2080.certificate 1621=true := by decide +kernel
noncomputable def cell2080 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2080.certificate 1621 accepted2080
theorem accepted2081 : minorantGammaCheck GammaPanel2081.certificate 1621=true := by decide +kernel
noncomputable def cell2081 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2081.certificate 1621 accepted2081
theorem accepted2082 : minorantGammaCheck GammaPanel2082.certificate 1621=true := by decide +kernel
noncomputable def cell2082 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2082.certificate 1621 accepted2082
theorem accepted2083 : minorantGammaCheck GammaPanel2083.certificate 1621=true := by decide +kernel
noncomputable def cell2083 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2083.certificate 1621 accepted2083
theorem accepted2084 : minorantGammaCheck GammaPanel2084.certificate 1621=true := by decide +kernel
noncomputable def cell2084 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2084.certificate 1621 accepted2084
theorem accepted2085 : minorantGammaCheck GammaPanel2085.certificate 1621=true := by decide +kernel
noncomputable def cell2085 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2085.certificate 1621 accepted2085
theorem accepted2086 : minorantGammaCheck GammaPanel2086.certificate 1621=true := by decide +kernel
noncomputable def cell2086 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2086.certificate 1621 accepted2086
theorem accepted2087 : minorantGammaCheck GammaPanel2087.certificate 1621=true := by decide +kernel
noncomputable def cell2087 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2087.certificate 1621 accepted2087
noncomputable def cells : List CertifiedMinorantCell := [cell2080, cell2081, cell2082, cell2083, cell2084, cell2085, cell2086, cell2087]
theorem chainAccepted : minorantChainCheck (4801/5000) (961/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4801/5000) (961/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0260
