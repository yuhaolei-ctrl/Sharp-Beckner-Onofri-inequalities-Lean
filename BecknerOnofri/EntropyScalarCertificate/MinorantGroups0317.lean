module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0317

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0317
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2536 : minorantGammaCheck GammaPanel2536.certificate 1621=true := by decide +kernel
noncomputable def cell2536 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2536.certificate 1621 accepted2536
theorem accepted2537 : minorantGammaCheck GammaPanel2537.certificate 1621=true := by decide +kernel
noncomputable def cell2537 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2537.certificate 1621 accepted2537
theorem accepted2538 : minorantGammaCheck GammaPanel2538.certificate 1621=true := by decide +kernel
noncomputable def cell2538 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2538.certificate 1621 accepted2538
theorem accepted2539 : minorantGammaCheck GammaPanel2539.certificate 1621=true := by decide +kernel
noncomputable def cell2539 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2539.certificate 1621 accepted2539
theorem accepted2540 : minorantGammaCheck GammaPanel2540.certificate 1621=true := by decide +kernel
noncomputable def cell2540 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2540.certificate 1621 accepted2540
theorem accepted2541 : minorantGammaCheck GammaPanel2541.certificate 1621=true := by decide +kernel
noncomputable def cell2541 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2541.certificate 1621 accepted2541
theorem accepted2542 : minorantGammaCheck GammaPanel2542.certificate 1621=true := by decide +kernel
noncomputable def cell2542 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2542.certificate 1621 accepted2542
theorem accepted2543 : minorantGammaCheck GammaPanel2543.certificate 1621=true := by decide +kernel
noncomputable def cell2543 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2543.certificate 1621 accepted2543
noncomputable def cells : List CertifiedMinorantCell := [cell2536, cell2537, cell2538, cell2539, cell2540, cell2541, cell2542, cell2543]
theorem chainAccepted : minorantChainCheck (24829/25000) (24833/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24829/25000) (24833/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0317
