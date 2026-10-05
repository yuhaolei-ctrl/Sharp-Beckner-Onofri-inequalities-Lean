module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0374

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0374
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2992 : minorantGammaCheck GammaPanel2992.certificate 1621=true := by decide +kernel
noncomputable def cell2992 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2992.certificate 1621 accepted2992
theorem accepted2993 : minorantGammaCheck GammaPanel2993.certificate 1621=true := by decide +kernel
noncomputable def cell2993 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2993.certificate 1621 accepted2993
theorem accepted2994 : minorantGammaCheck GammaPanel2994.certificate 1621=true := by decide +kernel
noncomputable def cell2994 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2994.certificate 1621 accepted2994
theorem accepted2995 : minorantGammaCheck GammaPanel2995.certificate 1621=true := by decide +kernel
noncomputable def cell2995 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2995.certificate 1621 accepted2995
theorem accepted2996 : minorantGammaCheck GammaPanel2996.certificate 1621=true := by decide +kernel
noncomputable def cell2996 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2996.certificate 1621 accepted2996
theorem accepted2997 : minorantGammaCheck GammaPanel2997.certificate 1621=true := by decide +kernel
noncomputable def cell2997 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2997.certificate 1621 accepted2997
theorem accepted2998 : minorantGammaCheck GammaPanel2998.certificate 1621=true := by decide +kernel
noncomputable def cell2998 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2998.certificate 1621 accepted2998
theorem accepted2999 : minorantGammaCheck GammaPanel2999.certificate 1621=true := by decide +kernel
noncomputable def cell2999 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2999.certificate 1621 accepted2999
noncomputable def cells : List CertifiedMinorantCell := [cell2992, cell2993, cell2994, cell2995, cell2996, cell2997, cell2998, cell2999]
theorem chainAccepted : minorantChainCheck (12479/12500) (24959/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (12479/12500) (24959/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0374
