module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0315

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0315
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2520 : minorantGammaCheck GammaPanel2520.certificate 1621=true := by decide +kernel
noncomputable def cell2520 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2520.certificate 1621 accepted2520
theorem accepted2521 : minorantGammaCheck GammaPanel2521.certificate 1621=true := by decide +kernel
noncomputable def cell2521 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2521.certificate 1621 accepted2521
theorem accepted2522 : minorantGammaCheck GammaPanel2522.certificate 1621=true := by decide +kernel
noncomputable def cell2522 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2522.certificate 1621 accepted2522
theorem accepted2523 : minorantGammaCheck GammaPanel2523.certificate 1621=true := by decide +kernel
noncomputable def cell2523 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2523.certificate 1621 accepted2523
theorem accepted2524 : minorantGammaCheck GammaPanel2524.certificate 1621=true := by decide +kernel
noncomputable def cell2524 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2524.certificate 1621 accepted2524
theorem accepted2525 : minorantGammaCheck GammaPanel2525.certificate 1621=true := by decide +kernel
noncomputable def cell2525 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2525.certificate 1621 accepted2525
theorem accepted2526 : minorantGammaCheck GammaPanel2526.certificate 1621=true := by decide +kernel
noncomputable def cell2526 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2526.certificate 1621 accepted2526
theorem accepted2527 : minorantGammaCheck GammaPanel2527.certificate 1621=true := by decide +kernel
noncomputable def cell2527 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2527.certificate 1621 accepted2527
noncomputable def cells : List CertifiedMinorantCell := [cell2520, cell2521, cell2522, cell2523, cell2524, cell2525, cell2526, cell2527]
theorem chainAccepted : minorantChainCheck (24821/25000) (993/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24821/25000) (993/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0315
