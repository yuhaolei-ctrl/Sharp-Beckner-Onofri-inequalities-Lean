module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0371

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0371
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2968 : minorantGammaCheck GammaPanel2968.certificate 1621=true := by decide +kernel
noncomputable def cell2968 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2968.certificate 1621 accepted2968
theorem accepted2969 : minorantGammaCheck GammaPanel2969.certificate 1621=true := by decide +kernel
noncomputable def cell2969 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2969.certificate 1621 accepted2969
theorem accepted2970 : minorantGammaCheck GammaPanel2970.certificate 1621=true := by decide +kernel
noncomputable def cell2970 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2970.certificate 1621 accepted2970
theorem accepted2971 : minorantGammaCheck GammaPanel2971.certificate 1621=true := by decide +kernel
noncomputable def cell2971 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2971.certificate 1621 accepted2971
theorem accepted2972 : minorantGammaCheck GammaPanel2972.certificate 1621=true := by decide +kernel
noncomputable def cell2972 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2972.certificate 1621 accepted2972
theorem accepted2973 : minorantGammaCheck GammaPanel2973.certificate 1621=true := by decide +kernel
noncomputable def cell2973 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2973.certificate 1621 accepted2973
theorem accepted2974 : minorantGammaCheck GammaPanel2974.certificate 1621=true := by decide +kernel
noncomputable def cell2974 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2974.certificate 1621 accepted2974
theorem accepted2975 : minorantGammaCheck GammaPanel2975.certificate 1621=true := by decide +kernel
noncomputable def cell2975 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2975.certificate 1621 accepted2975
noncomputable def cells : List CertifiedMinorantCell := [cell2968, cell2969, cell2970, cell2971, cell2972, cell2973, cell2974, cell2975]
theorem chainAccepted : minorantChainCheck (4991/5000) (6239/6250) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4991/5000) (6239/6250) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0371
