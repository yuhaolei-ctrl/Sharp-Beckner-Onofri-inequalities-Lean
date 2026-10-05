module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0296

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0296
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2368 : minorantGammaCheck GammaPanel2368.certificate 1621=true := by decide +kernel
noncomputable def cell2368 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2368.certificate 1621 accepted2368
theorem accepted2369 : minorantGammaCheck GammaPanel2369.certificate 1621=true := by decide +kernel
noncomputable def cell2369 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2369.certificate 1621 accepted2369
theorem accepted2370 : minorantGammaCheck GammaPanel2370.certificate 1621=true := by decide +kernel
noncomputable def cell2370 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2370.certificate 1621 accepted2370
theorem accepted2371 : minorantGammaCheck GammaPanel2371.certificate 1621=true := by decide +kernel
noncomputable def cell2371 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2371.certificate 1621 accepted2371
theorem accepted2372 : minorantGammaCheck GammaPanel2372.certificate 1621=true := by decide +kernel
noncomputable def cell2372 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2372.certificate 1621 accepted2372
theorem accepted2373 : minorantGammaCheck GammaPanel2373.certificate 1621=true := by decide +kernel
noncomputable def cell2373 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2373.certificate 1621 accepted2373
theorem accepted2374 : minorantGammaCheck GammaPanel2374.certificate 1621=true := by decide +kernel
noncomputable def cell2374 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2374.certificate 1621 accepted2374
theorem accepted2375 : minorantGammaCheck GammaPanel2375.certificate 1621=true := by decide +kernel
noncomputable def cell2375 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2375.certificate 1621 accepted2375
noncomputable def cells : List CertifiedMinorantCell := [cell2368, cell2369, cell2370, cell2371, cell2372, cell2373, cell2374, cell2375]
theorem chainAccepted : minorantChainCheck (989/1000) (4949/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (989/1000) (4949/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0296
