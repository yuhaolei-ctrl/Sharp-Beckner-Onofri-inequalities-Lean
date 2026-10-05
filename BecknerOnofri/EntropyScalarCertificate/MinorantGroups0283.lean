module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0283

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0283
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2264 : minorantGammaCheck GammaPanel2264.certificate 1621=true := by decide +kernel
noncomputable def cell2264 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2264.certificate 1621 accepted2264
theorem accepted2265 : minorantGammaCheck GammaPanel2265.certificate 1621=true := by decide +kernel
noncomputable def cell2265 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2265.certificate 1621 accepted2265
theorem accepted2266 : minorantGammaCheck GammaPanel2266.certificate 1621=true := by decide +kernel
noncomputable def cell2266 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2266.certificate 1621 accepted2266
theorem accepted2267 : minorantGammaCheck GammaPanel2267.certificate 1621=true := by decide +kernel
noncomputable def cell2267 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2267.certificate 1621 accepted2267
theorem accepted2268 : minorantGammaCheck GammaPanel2268.certificate 1621=true := by decide +kernel
noncomputable def cell2268 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2268.certificate 1621 accepted2268
theorem accepted2269 : minorantGammaCheck GammaPanel2269.certificate 1621=true := by decide +kernel
noncomputable def cell2269 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2269.certificate 1621 accepted2269
theorem accepted2270 : minorantGammaCheck GammaPanel2270.certificate 1621=true := by decide +kernel
noncomputable def cell2270 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2270.certificate 1621 accepted2270
theorem accepted2271 : minorantGammaCheck GammaPanel2271.certificate 1621=true := by decide +kernel
noncomputable def cell2271 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2271.certificate 1621 accepted2271
noncomputable def cells : List CertifiedMinorantCell := [cell2264, cell2265, cell2266, cell2267, cell2268, cell2269, cell2270, cell2271]
theorem chainAccepted : minorantChainCheck (4893/5000) (4897/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4893/5000) (4897/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0283
