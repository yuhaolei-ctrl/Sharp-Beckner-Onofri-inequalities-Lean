module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0358

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0358
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2864 : minorantGammaCheck GammaPanel2864.certificate 1621=true := by decide +kernel
noncomputable def cell2864 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2864.certificate 1621 accepted2864
theorem accepted2865 : minorantGammaCheck GammaPanel2865.certificate 1621=true := by decide +kernel
noncomputable def cell2865 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2865.certificate 1621 accepted2865
theorem accepted2866 : minorantGammaCheck GammaPanel2866.certificate 1621=true := by decide +kernel
noncomputable def cell2866 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2866.certificate 1621 accepted2866
theorem accepted2867 : minorantGammaCheck GammaPanel2867.certificate 1621=true := by decide +kernel
noncomputable def cell2867 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2867.certificate 1621 accepted2867
theorem accepted2868 : minorantGammaCheck GammaPanel2868.certificate 1621=true := by decide +kernel
noncomputable def cell2868 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2868.certificate 1621 accepted2868
theorem accepted2869 : minorantGammaCheck GammaPanel2869.certificate 1621=true := by decide +kernel
noncomputable def cell2869 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2869.certificate 1621 accepted2869
theorem accepted2870 : minorantGammaCheck GammaPanel2870.certificate 1621=true := by decide +kernel
noncomputable def cell2870 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2870.certificate 1621 accepted2870
theorem accepted2871 : minorantGammaCheck GammaPanel2871.certificate 1621=true := by decide +kernel
noncomputable def cell2871 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2871.certificate 1621 accepted2871
noncomputable def cells : List CertifiedMinorantCell := [cell2864, cell2865, cell2866, cell2867, cell2868, cell2869, cell2870, cell2871]
theorem chainAccepted : minorantChainCheck (12471/12500) (24943/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (12471/12500) (24943/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0358
