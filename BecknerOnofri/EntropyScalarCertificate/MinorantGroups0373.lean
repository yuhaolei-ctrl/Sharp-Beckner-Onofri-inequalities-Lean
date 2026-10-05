module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0373

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0373
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2984 : minorantGammaCheck GammaPanel2984.certificate 1621=true := by decide +kernel
noncomputable def cell2984 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2984.certificate 1621 accepted2984
theorem accepted2985 : minorantGammaCheck GammaPanel2985.certificate 1621=true := by decide +kernel
noncomputable def cell2985 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2985.certificate 1621 accepted2985
theorem accepted2986 : minorantGammaCheck GammaPanel2986.certificate 1621=true := by decide +kernel
noncomputable def cell2986 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2986.certificate 1621 accepted2986
theorem accepted2987 : minorantGammaCheck GammaPanel2987.certificate 1621=true := by decide +kernel
noncomputable def cell2987 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2987.certificate 1621 accepted2987
theorem accepted2988 : minorantGammaCheck GammaPanel2988.certificate 1621=true := by decide +kernel
noncomputable def cell2988 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2988.certificate 1621 accepted2988
theorem accepted2989 : minorantGammaCheck GammaPanel2989.certificate 1621=true := by decide +kernel
noncomputable def cell2989 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2989.certificate 1621 accepted2989
theorem accepted2990 : minorantGammaCheck GammaPanel2990.certificate 1621=true := by decide +kernel
noncomputable def cell2990 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2990.certificate 1621 accepted2990
theorem accepted2991 : minorantGammaCheck GammaPanel2991.certificate 1621=true := by decide +kernel
noncomputable def cell2991 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2991.certificate 1621 accepted2991
noncomputable def cells : List CertifiedMinorantCell := [cell2984, cell2985, cell2986, cell2987, cell2988, cell2989, cell2990, cell2991]
theorem chainAccepted : minorantChainCheck (24957/25000) (12479/12500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24957/25000) (12479/12500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0373
