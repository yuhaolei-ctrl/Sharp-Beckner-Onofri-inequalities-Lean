import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0259
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0259
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2072 : minorantGammaCheck GammaPanel2072.certificate 1621=true := by decide +kernel
noncomputable def cell2072 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2072.certificate 1621 accepted2072
theorem accepted2073 : minorantGammaCheck GammaPanel2073.certificate 1621=true := by decide +kernel
noncomputable def cell2073 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2073.certificate 1621 accepted2073
theorem accepted2074 : minorantGammaCheck GammaPanel2074.certificate 1621=true := by decide +kernel
noncomputable def cell2074 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2074.certificate 1621 accepted2074
theorem accepted2075 : minorantGammaCheck GammaPanel2075.certificate 1621=true := by decide +kernel
noncomputable def cell2075 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2075.certificate 1621 accepted2075
theorem accepted2076 : minorantGammaCheck GammaPanel2076.certificate 1621=true := by decide +kernel
noncomputable def cell2076 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2076.certificate 1621 accepted2076
theorem accepted2077 : minorantGammaCheck GammaPanel2077.certificate 1621=true := by decide +kernel
noncomputable def cell2077 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2077.certificate 1621 accepted2077
theorem accepted2078 : minorantGammaCheck GammaPanel2078.certificate 1621=true := by decide +kernel
noncomputable def cell2078 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2078.certificate 1621 accepted2078
theorem accepted2079 : minorantGammaCheck GammaPanel2079.certificate 1621=true := by decide +kernel
noncomputable def cell2079 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2079.certificate 1621 accepted2079
noncomputable def cells : List CertifiedMinorantCell := [cell2072, cell2073, cell2074, cell2075, cell2076, cell2077, cell2078, cell2079]
theorem chainAccepted : minorantChainCheck (4797/5000) (4801/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4797/5000) (4801/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0259
