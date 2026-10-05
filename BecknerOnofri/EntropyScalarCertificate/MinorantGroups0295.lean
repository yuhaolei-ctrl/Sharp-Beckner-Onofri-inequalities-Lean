module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0295

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0295
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2360 : minorantGammaCheck GammaPanel2360.certificate 1621=true := by decide +kernel
noncomputable def cell2360 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2360.certificate 1621 accepted2360
theorem accepted2361 : minorantGammaCheck GammaPanel2361.certificate 1621=true := by decide +kernel
noncomputable def cell2361 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2361.certificate 1621 accepted2361
theorem accepted2362 : minorantGammaCheck GammaPanel2362.certificate 1621=true := by decide +kernel
noncomputable def cell2362 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2362.certificate 1621 accepted2362
theorem accepted2363 : minorantGammaCheck GammaPanel2363.certificate 1621=true := by decide +kernel
noncomputable def cell2363 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2363.certificate 1621 accepted2363
theorem accepted2364 : minorantGammaCheck GammaPanel2364.certificate 1621=true := by decide +kernel
noncomputable def cell2364 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2364.certificate 1621 accepted2364
theorem accepted2365 : minorantGammaCheck GammaPanel2365.certificate 1621=true := by decide +kernel
noncomputable def cell2365 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2365.certificate 1621 accepted2365
theorem accepted2366 : minorantGammaCheck GammaPanel2366.certificate 1621=true := by decide +kernel
noncomputable def cell2366 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2366.certificate 1621 accepted2366
theorem accepted2367 : minorantGammaCheck GammaPanel2367.certificate 1621=true := by decide +kernel
noncomputable def cell2367 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2367.certificate 1621 accepted2367
noncomputable def cells : List CertifiedMinorantCell := [cell2360, cell2361, cell2362, cell2363, cell2364, cell2365, cell2366, cell2367]
theorem chainAccepted : minorantChainCheck (4941/5000) (989/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4941/5000) (989/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0295
