import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0311
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0311
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2488 : minorantGammaCheck GammaPanel2488.certificate 1621=true := by decide +kernel
noncomputable def cell2488 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2488.certificate 1621 accepted2488
theorem accepted2489 : minorantGammaCheck GammaPanel2489.certificate 1621=true := by decide +kernel
noncomputable def cell2489 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2489.certificate 1621 accepted2489
theorem accepted2490 : minorantGammaCheck GammaPanel2490.certificate 1621=true := by decide +kernel
noncomputable def cell2490 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2490.certificate 1621 accepted2490
theorem accepted2491 : minorantGammaCheck GammaPanel2491.certificate 1621=true := by decide +kernel
noncomputable def cell2491 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2491.certificate 1621 accepted2491
theorem accepted2492 : minorantGammaCheck GammaPanel2492.certificate 1621=true := by decide +kernel
noncomputable def cell2492 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2492.certificate 1621 accepted2492
theorem accepted2493 : minorantGammaCheck GammaPanel2493.certificate 1621=true := by decide +kernel
noncomputable def cell2493 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2493.certificate 1621 accepted2493
theorem accepted2494 : minorantGammaCheck GammaPanel2494.certificate 1621=true := by decide +kernel
noncomputable def cell2494 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2494.certificate 1621 accepted2494
theorem accepted2495 : minorantGammaCheck GammaPanel2495.certificate 1621=true := by decide +kernel
noncomputable def cell2495 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2495.certificate 1621 accepted2495
noncomputable def cells : List CertifiedMinorantCell := [cell2488, cell2489, cell2490, cell2491, cell2492, cell2493, cell2494, cell2495]
theorem chainAccepted : minorantChainCheck (4961/5000) (24809/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4961/5000) (24809/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0311
