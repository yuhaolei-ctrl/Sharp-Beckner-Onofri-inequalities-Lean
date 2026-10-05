module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0342

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0342
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2736 : minorantGammaCheck GammaPanel2736.certificate 1621=true := by decide +kernel
noncomputable def cell2736 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2736.certificate 1621 accepted2736
theorem accepted2737 : minorantGammaCheck GammaPanel2737.certificate 1621=true := by decide +kernel
noncomputable def cell2737 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2737.certificate 1621 accepted2737
theorem accepted2738 : minorantGammaCheck GammaPanel2738.certificate 1621=true := by decide +kernel
noncomputable def cell2738 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2738.certificate 1621 accepted2738
theorem accepted2739 : minorantGammaCheck GammaPanel2739.certificate 1621=true := by decide +kernel
noncomputable def cell2739 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2739.certificate 1621 accepted2739
theorem accepted2740 : minorantGammaCheck GammaPanel2740.certificate 1621=true := by decide +kernel
noncomputable def cell2740 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2740.certificate 1621 accepted2740
theorem accepted2741 : minorantGammaCheck GammaPanel2741.certificate 1621=true := by decide +kernel
noncomputable def cell2741 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2741.certificate 1621 accepted2741
theorem accepted2742 : minorantGammaCheck GammaPanel2742.certificate 1621=true := by decide +kernel
noncomputable def cell2742 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2742.certificate 1621 accepted2742
theorem accepted2743 : minorantGammaCheck GammaPanel2743.certificate 1621=true := by decide +kernel
noncomputable def cell2743 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2743.certificate 1621 accepted2743
noncomputable def cells : List CertifiedMinorantCell := [cell2736, cell2737, cell2738, cell2739, cell2740, cell2741, cell2742, cell2743]
theorem chainAccepted : minorantChainCheck (12463/12500) (24927/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (12463/12500) (24927/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0342
