import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0281
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0281
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2248 : minorantGammaCheck GammaPanel2248.certificate 1621=true := by decide +kernel
noncomputable def cell2248 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2248.certificate 1621 accepted2248
theorem accepted2249 : minorantGammaCheck GammaPanel2249.certificate 1621=true := by decide +kernel
noncomputable def cell2249 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2249.certificate 1621 accepted2249
theorem accepted2250 : minorantGammaCheck GammaPanel2250.certificate 1621=true := by decide +kernel
noncomputable def cell2250 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2250.certificate 1621 accepted2250
theorem accepted2251 : minorantGammaCheck GammaPanel2251.certificate 1621=true := by decide +kernel
noncomputable def cell2251 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2251.certificate 1621 accepted2251
theorem accepted2252 : minorantGammaCheck GammaPanel2252.certificate 1621=true := by decide +kernel
noncomputable def cell2252 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2252.certificate 1621 accepted2252
theorem accepted2253 : minorantGammaCheck GammaPanel2253.certificate 1621=true := by decide +kernel
noncomputable def cell2253 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2253.certificate 1621 accepted2253
theorem accepted2254 : minorantGammaCheck GammaPanel2254.certificate 1621=true := by decide +kernel
noncomputable def cell2254 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2254.certificate 1621 accepted2254
theorem accepted2255 : minorantGammaCheck GammaPanel2255.certificate 1621=true := by decide +kernel
noncomputable def cell2255 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2255.certificate 1621 accepted2255
noncomputable def cells : List CertifiedMinorantCell := [cell2248, cell2249, cell2250, cell2251, cell2252, cell2253, cell2254, cell2255]
theorem chainAccepted : minorantChainCheck (977/1000) (4889/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (977/1000) (4889/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0281
