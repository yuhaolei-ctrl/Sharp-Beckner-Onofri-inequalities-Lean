module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0344

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0344
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2752 : minorantGammaCheck GammaPanel2752.certificate 1621=true := by decide +kernel
noncomputable def cell2752 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2752.certificate 1621 accepted2752
theorem accepted2753 : minorantGammaCheck GammaPanel2753.certificate 1621=true := by decide +kernel
noncomputable def cell2753 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2753.certificate 1621 accepted2753
theorem accepted2754 : minorantGammaCheck GammaPanel2754.certificate 1621=true := by decide +kernel
noncomputable def cell2754 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2754.certificate 1621 accepted2754
theorem accepted2755 : minorantGammaCheck GammaPanel2755.certificate 1621=true := by decide +kernel
noncomputable def cell2755 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2755.certificate 1621 accepted2755
theorem accepted2756 : minorantGammaCheck GammaPanel2756.certificate 1621=true := by decide +kernel
noncomputable def cell2756 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2756.certificate 1621 accepted2756
theorem accepted2757 : minorantGammaCheck GammaPanel2757.certificate 1621=true := by decide +kernel
noncomputable def cell2757 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2757.certificate 1621 accepted2757
theorem accepted2758 : minorantGammaCheck GammaPanel2758.certificate 1621=true := by decide +kernel
noncomputable def cell2758 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2758.certificate 1621 accepted2758
theorem accepted2759 : minorantGammaCheck GammaPanel2759.certificate 1621=true := by decide +kernel
noncomputable def cell2759 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2759.certificate 1621 accepted2759
noncomputable def cells : List CertifiedMinorantCell := [cell2752, cell2753, cell2754, cell2755, cell2756, cell2757, cell2758, cell2759]
theorem chainAccepted : minorantChainCheck (3116/3125) (24929/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (3116/3125) (24929/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0344
