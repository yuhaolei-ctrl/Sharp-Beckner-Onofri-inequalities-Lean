import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0255
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0255
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2040 : minorantGammaCheck GammaPanel2040.certificate 1621=true := by decide +kernel
noncomputable def cell2040 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2040.certificate 1621 accepted2040
theorem accepted2041 : minorantGammaCheck GammaPanel2041.certificate 1621=true := by decide +kernel
noncomputable def cell2041 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2041.certificate 1621 accepted2041
theorem accepted2042 : minorantGammaCheck GammaPanel2042.certificate 1621=true := by decide +kernel
noncomputable def cell2042 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2042.certificate 1621 accepted2042
theorem accepted2043 : minorantGammaCheck GammaPanel2043.certificate 1621=true := by decide +kernel
noncomputable def cell2043 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2043.certificate 1621 accepted2043
theorem accepted2044 : minorantGammaCheck GammaPanel2044.certificate 1621=true := by decide +kernel
noncomputable def cell2044 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2044.certificate 1621 accepted2044
theorem accepted2045 : minorantGammaCheck GammaPanel2045.certificate 1621=true := by decide +kernel
noncomputable def cell2045 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2045.certificate 1621 accepted2045
theorem accepted2046 : minorantGammaCheck GammaPanel2046.certificate 1621=true := by decide +kernel
noncomputable def cell2046 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2046.certificate 1621 accepted2046
theorem accepted2047 : minorantGammaCheck GammaPanel2047.certificate 1621=true := by decide +kernel
noncomputable def cell2047 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2047.certificate 1621 accepted2047
noncomputable def cells : List CertifiedMinorantCell := [cell2040, cell2041, cell2042, cell2043, cell2044, cell2045, cell2046, cell2047]
theorem chainAccepted : minorantChainCheck (4781/5000) (957/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4781/5000) (957/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0255
