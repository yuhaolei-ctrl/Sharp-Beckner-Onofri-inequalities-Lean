module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0319

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0319
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2552 : minorantGammaCheck GammaPanel2552.certificate 1621=true := by decide +kernel
noncomputable def cell2552 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2552.certificate 1621 accepted2552
theorem accepted2553 : minorantGammaCheck GammaPanel2553.certificate 1621=true := by decide +kernel
noncomputable def cell2553 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2553.certificate 1621 accepted2553
theorem accepted2554 : minorantGammaCheck GammaPanel2554.certificate 1621=true := by decide +kernel
noncomputable def cell2554 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2554.certificate 1621 accepted2554
theorem accepted2555 : minorantGammaCheck GammaPanel2555.certificate 1621=true := by decide +kernel
noncomputable def cell2555 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2555.certificate 1621 accepted2555
theorem accepted2556 : minorantGammaCheck GammaPanel2556.certificate 1621=true := by decide +kernel
noncomputable def cell2556 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2556.certificate 1621 accepted2556
theorem accepted2557 : minorantGammaCheck GammaPanel2557.certificate 1621=true := by decide +kernel
noncomputable def cell2557 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2557.certificate 1621 accepted2557
theorem accepted2558 : minorantGammaCheck GammaPanel2558.certificate 1621=true := by decide +kernel
noncomputable def cell2558 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2558.certificate 1621 accepted2558
theorem accepted2559 : minorantGammaCheck GammaPanel2559.certificate 1621=true := by decide +kernel
noncomputable def cell2559 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2559.certificate 1621 accepted2559
noncomputable def cells : List CertifiedMinorantCell := [cell2552, cell2553, cell2554, cell2555, cell2556, cell2557, cell2558, cell2559]
theorem chainAccepted : minorantChainCheck (24837/25000) (24841/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24837/25000) (24841/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0319
