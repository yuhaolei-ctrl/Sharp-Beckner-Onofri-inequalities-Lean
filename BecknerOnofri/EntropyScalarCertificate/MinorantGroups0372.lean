module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0372

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0372
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2976 : minorantGammaCheck GammaPanel2976.certificate 1621=true := by decide +kernel
noncomputable def cell2976 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2976.certificate 1621 accepted2976
theorem accepted2977 : minorantGammaCheck GammaPanel2977.certificate 1621=true := by decide +kernel
noncomputable def cell2977 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2977.certificate 1621 accepted2977
theorem accepted2978 : minorantGammaCheck GammaPanel2978.certificate 1621=true := by decide +kernel
noncomputable def cell2978 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2978.certificate 1621 accepted2978
theorem accepted2979 : minorantGammaCheck GammaPanel2979.certificate 1621=true := by decide +kernel
noncomputable def cell2979 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2979.certificate 1621 accepted2979
theorem accepted2980 : minorantGammaCheck GammaPanel2980.certificate 1621=true := by decide +kernel
noncomputable def cell2980 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2980.certificate 1621 accepted2980
theorem accepted2981 : minorantGammaCheck GammaPanel2981.certificate 1621=true := by decide +kernel
noncomputable def cell2981 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2981.certificate 1621 accepted2981
theorem accepted2982 : minorantGammaCheck GammaPanel2982.certificate 1621=true := by decide +kernel
noncomputable def cell2982 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2982.certificate 1621 accepted2982
theorem accepted2983 : minorantGammaCheck GammaPanel2983.certificate 1621=true := by decide +kernel
noncomputable def cell2983 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2983.certificate 1621 accepted2983
noncomputable def cells : List CertifiedMinorantCell := [cell2976, cell2977, cell2978, cell2979, cell2980, cell2981, cell2982, cell2983]
theorem chainAccepted : minorantChainCheck (6239/6250) (24957/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (6239/6250) (24957/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0372
