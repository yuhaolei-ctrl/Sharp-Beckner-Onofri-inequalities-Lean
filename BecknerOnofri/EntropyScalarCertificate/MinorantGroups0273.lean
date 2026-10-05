import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0273
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0273
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2184 : minorantGammaCheck GammaPanel2184.certificate 1621=true := by decide +kernel
noncomputable def cell2184 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2184.certificate 1621 accepted2184
theorem accepted2185 : minorantGammaCheck GammaPanel2185.certificate 1621=true := by decide +kernel
noncomputable def cell2185 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2185.certificate 1621 accepted2185
theorem accepted2186 : minorantGammaCheck GammaPanel2186.certificate 1621=true := by decide +kernel
noncomputable def cell2186 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2186.certificate 1621 accepted2186
theorem accepted2187 : minorantGammaCheck GammaPanel2187.certificate 1621=true := by decide +kernel
noncomputable def cell2187 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2187.certificate 1621 accepted2187
theorem accepted2188 : minorantGammaCheck GammaPanel2188.certificate 1621=true := by decide +kernel
noncomputable def cell2188 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2188.certificate 1621 accepted2188
theorem accepted2189 : minorantGammaCheck GammaPanel2189.certificate 1621=true := by decide +kernel
noncomputable def cell2189 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2189.certificate 1621 accepted2189
theorem accepted2190 : minorantGammaCheck GammaPanel2190.certificate 1621=true := by decide +kernel
noncomputable def cell2190 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2190.certificate 1621 accepted2190
theorem accepted2191 : minorantGammaCheck GammaPanel2191.certificate 1621=true := by decide +kernel
noncomputable def cell2191 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2191.certificate 1621 accepted2191
noncomputable def cells : List CertifiedMinorantCell := [cell2184, cell2185, cell2186, cell2187, cell2188, cell2189, cell2190, cell2191]
theorem chainAccepted : minorantChainCheck (4853/5000) (4857/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4853/5000) (4857/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0273
