module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0280

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0280
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2240 : minorantGammaCheck GammaPanel2240.certificate 1621=true := by decide +kernel
noncomputable def cell2240 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2240.certificate 1621 accepted2240
theorem accepted2241 : minorantGammaCheck GammaPanel2241.certificate 1621=true := by decide +kernel
noncomputable def cell2241 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2241.certificate 1621 accepted2241
theorem accepted2242 : minorantGammaCheck GammaPanel2242.certificate 1621=true := by decide +kernel
noncomputable def cell2242 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2242.certificate 1621 accepted2242
theorem accepted2243 : minorantGammaCheck GammaPanel2243.certificate 1621=true := by decide +kernel
noncomputable def cell2243 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2243.certificate 1621 accepted2243
theorem accepted2244 : minorantGammaCheck GammaPanel2244.certificate 1621=true := by decide +kernel
noncomputable def cell2244 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2244.certificate 1621 accepted2244
theorem accepted2245 : minorantGammaCheck GammaPanel2245.certificate 1621=true := by decide +kernel
noncomputable def cell2245 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2245.certificate 1621 accepted2245
theorem accepted2246 : minorantGammaCheck GammaPanel2246.certificate 1621=true := by decide +kernel
noncomputable def cell2246 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2246.certificate 1621 accepted2246
theorem accepted2247 : minorantGammaCheck GammaPanel2247.certificate 1621=true := by decide +kernel
noncomputable def cell2247 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2247.certificate 1621 accepted2247
noncomputable def cells : List CertifiedMinorantCell := [cell2240, cell2241, cell2242, cell2243, cell2244, cell2245, cell2246, cell2247]
theorem chainAccepted : minorantChainCheck (4881/5000) (977/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4881/5000) (977/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0280
