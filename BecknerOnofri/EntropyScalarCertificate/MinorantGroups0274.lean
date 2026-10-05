module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0274

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0274
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2192 : minorantGammaCheck GammaPanel2192.certificate 1621=true := by decide +kernel
noncomputable def cell2192 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2192.certificate 1621 accepted2192
theorem accepted2193 : minorantGammaCheck GammaPanel2193.certificate 1621=true := by decide +kernel
noncomputable def cell2193 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2193.certificate 1621 accepted2193
theorem accepted2194 : minorantGammaCheck GammaPanel2194.certificate 1621=true := by decide +kernel
noncomputable def cell2194 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2194.certificate 1621 accepted2194
theorem accepted2195 : minorantGammaCheck GammaPanel2195.certificate 1621=true := by decide +kernel
noncomputable def cell2195 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2195.certificate 1621 accepted2195
theorem accepted2196 : minorantGammaCheck GammaPanel2196.certificate 1621=true := by decide +kernel
noncomputable def cell2196 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2196.certificate 1621 accepted2196
theorem accepted2197 : minorantGammaCheck GammaPanel2197.certificate 1621=true := by decide +kernel
noncomputable def cell2197 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2197.certificate 1621 accepted2197
theorem accepted2198 : minorantGammaCheck GammaPanel2198.certificate 1621=true := by decide +kernel
noncomputable def cell2198 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2198.certificate 1621 accepted2198
theorem accepted2199 : minorantGammaCheck GammaPanel2199.certificate 1621=true := by decide +kernel
noncomputable def cell2199 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2199.certificate 1621 accepted2199
noncomputable def cells : List CertifiedMinorantCell := [cell2192, cell2193, cell2194, cell2195, cell2196, cell2197, cell2198, cell2199]
theorem chainAccepted : minorantChainCheck (4857/5000) (4861/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4857/5000) (4861/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0274
