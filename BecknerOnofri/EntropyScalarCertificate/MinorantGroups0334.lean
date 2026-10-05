module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0334

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0334
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2672 : minorantGammaCheck GammaPanel2672.certificate 1621=true := by decide +kernel
noncomputable def cell2672 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2672.certificate 1621 accepted2672
theorem accepted2673 : minorantGammaCheck GammaPanel2673.certificate 1621=true := by decide +kernel
noncomputable def cell2673 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2673.certificate 1621 accepted2673
theorem accepted2674 : minorantGammaCheck GammaPanel2674.certificate 1621=true := by decide +kernel
noncomputable def cell2674 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2674.certificate 1621 accepted2674
theorem accepted2675 : minorantGammaCheck GammaPanel2675.certificate 1621=true := by decide +kernel
noncomputable def cell2675 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2675.certificate 1621 accepted2675
theorem accepted2676 : minorantGammaCheck GammaPanel2676.certificate 1621=true := by decide +kernel
noncomputable def cell2676 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2676.certificate 1621 accepted2676
theorem accepted2677 : minorantGammaCheck GammaPanel2677.certificate 1621=true := by decide +kernel
noncomputable def cell2677 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2677.certificate 1621 accepted2677
theorem accepted2678 : minorantGammaCheck GammaPanel2678.certificate 1621=true := by decide +kernel
noncomputable def cell2678 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2678.certificate 1621 accepted2678
theorem accepted2679 : minorantGammaCheck GammaPanel2679.certificate 1621=true := by decide +kernel
noncomputable def cell2679 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2679.certificate 1621 accepted2679
noncomputable def cells : List CertifiedMinorantCell := [cell2672, cell2673, cell2674, cell2675, cell2676, cell2677, cell2678, cell2679]
theorem chainAccepted : minorantChainCheck (24897/25000) (24901/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24897/25000) (24901/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0334
