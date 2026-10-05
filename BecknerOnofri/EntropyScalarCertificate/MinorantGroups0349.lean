module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0349

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0349
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2792 : minorantGammaCheck GammaPanel2792.certificate 1621=true := by decide +kernel
noncomputable def cell2792 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2792.certificate 1621 accepted2792
theorem accepted2793 : minorantGammaCheck GammaPanel2793.certificate 1621=true := by decide +kernel
noncomputable def cell2793 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2793.certificate 1621 accepted2793
theorem accepted2794 : minorantGammaCheck GammaPanel2794.certificate 1621=true := by decide +kernel
noncomputable def cell2794 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2794.certificate 1621 accepted2794
theorem accepted2795 : minorantGammaCheck GammaPanel2795.certificate 1621=true := by decide +kernel
noncomputable def cell2795 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2795.certificate 1621 accepted2795
theorem accepted2796 : minorantGammaCheck GammaPanel2796.certificate 1621=true := by decide +kernel
noncomputable def cell2796 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2796.certificate 1621 accepted2796
theorem accepted2797 : minorantGammaCheck GammaPanel2797.certificate 1621=true := by decide +kernel
noncomputable def cell2797 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2797.certificate 1621 accepted2797
theorem accepted2798 : minorantGammaCheck GammaPanel2798.certificate 1621=true := by decide +kernel
noncomputable def cell2798 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2798.certificate 1621 accepted2798
theorem accepted2799 : minorantGammaCheck GammaPanel2799.certificate 1621=true := by decide +kernel
noncomputable def cell2799 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2799.certificate 1621 accepted2799
noncomputable def cells : List CertifiedMinorantCell := [cell2792, cell2793, cell2794, cell2795, cell2796, cell2797, cell2798, cell2799]
theorem chainAccepted : minorantChainCheck (24933/25000) (12467/12500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24933/25000) (12467/12500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0349
