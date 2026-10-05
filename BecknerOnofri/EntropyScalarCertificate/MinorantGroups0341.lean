module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0341

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0341
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2728 : minorantGammaCheck GammaPanel2728.certificate 1621=true := by decide +kernel
noncomputable def cell2728 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2728.certificate 1621 accepted2728
theorem accepted2729 : minorantGammaCheck GammaPanel2729.certificate 1621=true := by decide +kernel
noncomputable def cell2729 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2729.certificate 1621 accepted2729
theorem accepted2730 : minorantGammaCheck GammaPanel2730.certificate 1621=true := by decide +kernel
noncomputable def cell2730 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2730.certificate 1621 accepted2730
theorem accepted2731 : minorantGammaCheck GammaPanel2731.certificate 1621=true := by decide +kernel
noncomputable def cell2731 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2731.certificate 1621 accepted2731
theorem accepted2732 : minorantGammaCheck GammaPanel2732.certificate 1621=true := by decide +kernel
noncomputable def cell2732 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2732.certificate 1621 accepted2732
theorem accepted2733 : minorantGammaCheck GammaPanel2733.certificate 1621=true := by decide +kernel
noncomputable def cell2733 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2733.certificate 1621 accepted2733
theorem accepted2734 : minorantGammaCheck GammaPanel2734.certificate 1621=true := by decide +kernel
noncomputable def cell2734 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2734.certificate 1621 accepted2734
theorem accepted2735 : minorantGammaCheck GammaPanel2735.certificate 1621=true := by decide +kernel
noncomputable def cell2735 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2735.certificate 1621 accepted2735
noncomputable def cells : List CertifiedMinorantCell := [cell2728, cell2729, cell2730, cell2731, cell2732, cell2733, cell2734, cell2735]
theorem chainAccepted : minorantChainCheck (997/1000) (12463/12500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (997/1000) (12463/12500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0341
