module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0294

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0294
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2352 : minorantGammaCheck GammaPanel2352.certificate 1621=true := by decide +kernel
noncomputable def cell2352 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2352.certificate 1621 accepted2352
theorem accepted2353 : minorantGammaCheck GammaPanel2353.certificate 1621=true := by decide +kernel
noncomputable def cell2353 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2353.certificate 1621 accepted2353
theorem accepted2354 : minorantGammaCheck GammaPanel2354.certificate 1621=true := by decide +kernel
noncomputable def cell2354 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2354.certificate 1621 accepted2354
theorem accepted2355 : minorantGammaCheck GammaPanel2355.certificate 1621=true := by decide +kernel
noncomputable def cell2355 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2355.certificate 1621 accepted2355
theorem accepted2356 : minorantGammaCheck GammaPanel2356.certificate 1621=true := by decide +kernel
noncomputable def cell2356 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2356.certificate 1621 accepted2356
theorem accepted2357 : minorantGammaCheck GammaPanel2357.certificate 1621=true := by decide +kernel
noncomputable def cell2357 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2357.certificate 1621 accepted2357
theorem accepted2358 : minorantGammaCheck GammaPanel2358.certificate 1621=true := by decide +kernel
noncomputable def cell2358 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2358.certificate 1621 accepted2358
theorem accepted2359 : minorantGammaCheck GammaPanel2359.certificate 1621=true := by decide +kernel
noncomputable def cell2359 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2359.certificate 1621 accepted2359
noncomputable def cells : List CertifiedMinorantCell := [cell2352, cell2353, cell2354, cell2355, cell2356, cell2357, cell2358, cell2359]
theorem chainAccepted : minorantChainCheck (4937/5000) (4941/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4937/5000) (4941/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0294
