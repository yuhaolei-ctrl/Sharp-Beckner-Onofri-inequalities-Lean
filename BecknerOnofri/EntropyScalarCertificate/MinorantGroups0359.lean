module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0359

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0359
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2872 : minorantGammaCheck GammaPanel2872.certificate 1621=true := by decide +kernel
noncomputable def cell2872 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2872.certificate 1621 accepted2872
theorem accepted2873 : minorantGammaCheck GammaPanel2873.certificate 1621=true := by decide +kernel
noncomputable def cell2873 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2873.certificate 1621 accepted2873
theorem accepted2874 : minorantGammaCheck GammaPanel2874.certificate 1621=true := by decide +kernel
noncomputable def cell2874 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2874.certificate 1621 accepted2874
theorem accepted2875 : minorantGammaCheck GammaPanel2875.certificate 1621=true := by decide +kernel
noncomputable def cell2875 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2875.certificate 1621 accepted2875
theorem accepted2876 : minorantGammaCheck GammaPanel2876.certificate 1621=true := by decide +kernel
noncomputable def cell2876 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2876.certificate 1621 accepted2876
theorem accepted2877 : minorantGammaCheck GammaPanel2877.certificate 1621=true := by decide +kernel
noncomputable def cell2877 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2877.certificate 1621 accepted2877
theorem accepted2878 : minorantGammaCheck GammaPanel2878.certificate 1621=true := by decide +kernel
noncomputable def cell2878 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2878.certificate 1621 accepted2878
theorem accepted2879 : minorantGammaCheck GammaPanel2879.certificate 1621=true := by decide +kernel
noncomputable def cell2879 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2879.certificate 1621 accepted2879
noncomputable def cells : List CertifiedMinorantCell := [cell2872, cell2873, cell2874, cell2875, cell2876, cell2877, cell2878, cell2879]
theorem chainAccepted : minorantChainCheck (24943/25000) (3118/3125) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24943/25000) (3118/3125) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0359
