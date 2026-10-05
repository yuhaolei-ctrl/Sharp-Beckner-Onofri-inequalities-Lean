module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0370

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0370
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2960 : minorantGammaCheck GammaPanel2960.certificate 1621=true := by decide +kernel
noncomputable def cell2960 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2960.certificate 1621 accepted2960
theorem accepted2961 : minorantGammaCheck GammaPanel2961.certificate 1621=true := by decide +kernel
noncomputable def cell2961 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2961.certificate 1621 accepted2961
theorem accepted2962 : minorantGammaCheck GammaPanel2962.certificate 1621=true := by decide +kernel
noncomputable def cell2962 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2962.certificate 1621 accepted2962
theorem accepted2963 : minorantGammaCheck GammaPanel2963.certificate 1621=true := by decide +kernel
noncomputable def cell2963 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2963.certificate 1621 accepted2963
theorem accepted2964 : minorantGammaCheck GammaPanel2964.certificate 1621=true := by decide +kernel
noncomputable def cell2964 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2964.certificate 1621 accepted2964
theorem accepted2965 : minorantGammaCheck GammaPanel2965.certificate 1621=true := by decide +kernel
noncomputable def cell2965 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2965.certificate 1621 accepted2965
theorem accepted2966 : minorantGammaCheck GammaPanel2966.certificate 1621=true := by decide +kernel
noncomputable def cell2966 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2966.certificate 1621 accepted2966
theorem accepted2967 : minorantGammaCheck GammaPanel2967.certificate 1621=true := by decide +kernel
noncomputable def cell2967 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2967.certificate 1621 accepted2967
noncomputable def cells : List CertifiedMinorantCell := [cell2960, cell2961, cell2962, cell2963, cell2964, cell2965, cell2966, cell2967]
theorem chainAccepted : minorantChainCheck (12477/12500) (4991/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (12477/12500) (4991/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0370
