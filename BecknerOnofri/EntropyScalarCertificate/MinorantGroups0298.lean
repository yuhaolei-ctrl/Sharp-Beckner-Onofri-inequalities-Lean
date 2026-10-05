module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0298

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0298
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2384 : minorantGammaCheck GammaPanel2384.certificate 1621=true := by decide +kernel
noncomputable def cell2384 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2384.certificate 1621 accepted2384
theorem accepted2385 : minorantGammaCheck GammaPanel2385.certificate 1621=true := by decide +kernel
noncomputable def cell2385 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2385.certificate 1621 accepted2385
theorem accepted2386 : minorantGammaCheck GammaPanel2386.certificate 1621=true := by decide +kernel
noncomputable def cell2386 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2386.certificate 1621 accepted2386
theorem accepted2387 : minorantGammaCheck GammaPanel2387.certificate 1621=true := by decide +kernel
noncomputable def cell2387 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2387.certificate 1621 accepted2387
theorem accepted2388 : minorantGammaCheck GammaPanel2388.certificate 1621=true := by decide +kernel
noncomputable def cell2388 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2388.certificate 1621 accepted2388
theorem accepted2389 : minorantGammaCheck GammaPanel2389.certificate 1621=true := by decide +kernel
noncomputable def cell2389 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2389.certificate 1621 accepted2389
theorem accepted2390 : minorantGammaCheck GammaPanel2390.certificate 1621=true := by decide +kernel
noncomputable def cell2390 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2390.certificate 1621 accepted2390
theorem accepted2391 : minorantGammaCheck GammaPanel2391.certificate 1621=true := by decide +kernel
noncomputable def cell2391 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2391.certificate 1621 accepted2391
noncomputable def cells : List CertifiedMinorantCell := [cell2384, cell2385, cell2386, cell2387, cell2388, cell2389, cell2390, cell2391]
theorem chainAccepted : minorantChainCheck (24753/25000) (24757/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24753/25000) (24757/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0298
