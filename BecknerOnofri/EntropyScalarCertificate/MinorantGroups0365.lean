module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0365

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0365
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2920 : minorantGammaCheck GammaPanel2920.certificate 1621=true := by decide +kernel
noncomputable def cell2920 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2920.certificate 1621 accepted2920
theorem accepted2921 : minorantGammaCheck GammaPanel2921.certificate 1621=true := by decide +kernel
noncomputable def cell2921 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2921.certificate 1621 accepted2921
theorem accepted2922 : minorantGammaCheck GammaPanel2922.certificate 1621=true := by decide +kernel
noncomputable def cell2922 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2922.certificate 1621 accepted2922
theorem accepted2923 : minorantGammaCheck GammaPanel2923.certificate 1621=true := by decide +kernel
noncomputable def cell2923 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2923.certificate 1621 accepted2923
theorem accepted2924 : minorantGammaCheck GammaPanel2924.certificate 1621=true := by decide +kernel
noncomputable def cell2924 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2924.certificate 1621 accepted2924
theorem accepted2925 : minorantGammaCheck GammaPanel2925.certificate 1621=true := by decide +kernel
noncomputable def cell2925 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2925.certificate 1621 accepted2925
theorem accepted2926 : minorantGammaCheck GammaPanel2926.certificate 1621=true := by decide +kernel
noncomputable def cell2926 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2926.certificate 1621 accepted2926
theorem accepted2927 : minorantGammaCheck GammaPanel2927.certificate 1621=true := by decide +kernel
noncomputable def cell2927 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2927.certificate 1621 accepted2927
noncomputable def cells : List CertifiedMinorantCell := [cell2920, cell2921, cell2922, cell2923, cell2924, cell2925, cell2926, cell2927]
theorem chainAccepted : minorantChainCheck (24949/25000) (499/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24949/25000) (499/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0365
