module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0254

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0254
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2032 : minorantGammaCheck GammaPanel2032.certificate 1621=true := by decide +kernel
noncomputable def cell2032 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2032.certificate 1621 accepted2032
theorem accepted2033 : minorantGammaCheck GammaPanel2033.certificate 1621=true := by decide +kernel
noncomputable def cell2033 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2033.certificate 1621 accepted2033
theorem accepted2034 : minorantGammaCheck GammaPanel2034.certificate 1621=true := by decide +kernel
noncomputable def cell2034 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2034.certificate 1621 accepted2034
theorem accepted2035 : minorantGammaCheck GammaPanel2035.certificate 1621=true := by decide +kernel
noncomputable def cell2035 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2035.certificate 1621 accepted2035
theorem accepted2036 : minorantGammaCheck GammaPanel2036.certificate 1621=true := by decide +kernel
noncomputable def cell2036 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2036.certificate 1621 accepted2036
theorem accepted2037 : minorantGammaCheck GammaPanel2037.certificate 1621=true := by decide +kernel
noncomputable def cell2037 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2037.certificate 1621 accepted2037
theorem accepted2038 : minorantGammaCheck GammaPanel2038.certificate 1621=true := by decide +kernel
noncomputable def cell2038 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2038.certificate 1621 accepted2038
theorem accepted2039 : minorantGammaCheck GammaPanel2039.certificate 1621=true := by decide +kernel
noncomputable def cell2039 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2039.certificate 1621 accepted2039
noncomputable def cells : List CertifiedMinorantCell := [cell2032, cell2033, cell2034, cell2035, cell2036, cell2037, cell2038, cell2039]
theorem chainAccepted : minorantChainCheck (4777/5000) (4781/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4777/5000) (4781/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0254
