module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0312

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0312
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2496 : minorantGammaCheck GammaPanel2496.certificate 1621=true := by decide +kernel
noncomputable def cell2496 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2496.certificate 1621 accepted2496
theorem accepted2497 : minorantGammaCheck GammaPanel2497.certificate 1621=true := by decide +kernel
noncomputable def cell2497 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2497.certificate 1621 accepted2497
theorem accepted2498 : minorantGammaCheck GammaPanel2498.certificate 1621=true := by decide +kernel
noncomputable def cell2498 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2498.certificate 1621 accepted2498
theorem accepted2499 : minorantGammaCheck GammaPanel2499.certificate 1621=true := by decide +kernel
noncomputable def cell2499 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2499.certificate 1621 accepted2499
theorem accepted2500 : minorantGammaCheck GammaPanel2500.certificate 1621=true := by decide +kernel
noncomputable def cell2500 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2500.certificate 1621 accepted2500
theorem accepted2501 : minorantGammaCheck GammaPanel2501.certificate 1621=true := by decide +kernel
noncomputable def cell2501 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2501.certificate 1621 accepted2501
theorem accepted2502 : minorantGammaCheck GammaPanel2502.certificate 1621=true := by decide +kernel
noncomputable def cell2502 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2502.certificate 1621 accepted2502
theorem accepted2503 : minorantGammaCheck GammaPanel2503.certificate 1621=true := by decide +kernel
noncomputable def cell2503 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2503.certificate 1621 accepted2503
noncomputable def cells : List CertifiedMinorantCell := [cell2496, cell2497, cell2498, cell2499, cell2500, cell2501, cell2502, cell2503]
theorem chainAccepted : minorantChainCheck (24809/25000) (24813/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24809/25000) (24813/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0312
