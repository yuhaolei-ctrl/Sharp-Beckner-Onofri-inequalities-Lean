module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0284

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0284
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2272 : minorantGammaCheck GammaPanel2272.certificate 1621=true := by decide +kernel
noncomputable def cell2272 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2272.certificate 1621 accepted2272
theorem accepted2273 : minorantGammaCheck GammaPanel2273.certificate 1621=true := by decide +kernel
noncomputable def cell2273 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2273.certificate 1621 accepted2273
theorem accepted2274 : minorantGammaCheck GammaPanel2274.certificate 1621=true := by decide +kernel
noncomputable def cell2274 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2274.certificate 1621 accepted2274
theorem accepted2275 : minorantGammaCheck GammaPanel2275.certificate 1621=true := by decide +kernel
noncomputable def cell2275 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2275.certificate 1621 accepted2275
theorem accepted2276 : minorantGammaCheck GammaPanel2276.certificate 1621=true := by decide +kernel
noncomputable def cell2276 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2276.certificate 1621 accepted2276
theorem accepted2277 : minorantGammaCheck GammaPanel2277.certificate 1621=true := by decide +kernel
noncomputable def cell2277 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2277.certificate 1621 accepted2277
theorem accepted2278 : minorantGammaCheck GammaPanel2278.certificate 1621=true := by decide +kernel
noncomputable def cell2278 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2278.certificate 1621 accepted2278
theorem accepted2279 : minorantGammaCheck GammaPanel2279.certificate 1621=true := by decide +kernel
noncomputable def cell2279 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2279.certificate 1621 accepted2279
noncomputable def cells : List CertifiedMinorantCell := [cell2272, cell2273, cell2274, cell2275, cell2276, cell2277, cell2278, cell2279]
theorem chainAccepted : minorantChainCheck (4897/5000) (4901/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4897/5000) (4901/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0284
