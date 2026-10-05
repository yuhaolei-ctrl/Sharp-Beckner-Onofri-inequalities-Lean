module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0362

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0362
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2896 : minorantGammaCheck GammaPanel2896.certificate 1621=true := by decide +kernel
noncomputable def cell2896 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2896.certificate 1621 accepted2896
theorem accepted2897 : minorantGammaCheck GammaPanel2897.certificate 1621=true := by decide +kernel
noncomputable def cell2897 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2897.certificate 1621 accepted2897
theorem accepted2898 : minorantGammaCheck GammaPanel2898.certificate 1621=true := by decide +kernel
noncomputable def cell2898 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2898.certificate 1621 accepted2898
theorem accepted2899 : minorantGammaCheck GammaPanel2899.certificate 1621=true := by decide +kernel
noncomputable def cell2899 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2899.certificate 1621 accepted2899
theorem accepted2900 : minorantGammaCheck GammaPanel2900.certificate 1621=true := by decide +kernel
noncomputable def cell2900 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2900.certificate 1621 accepted2900
theorem accepted2901 : minorantGammaCheck GammaPanel2901.certificate 1621=true := by decide +kernel
noncomputable def cell2901 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2901.certificate 1621 accepted2901
theorem accepted2902 : minorantGammaCheck GammaPanel2902.certificate 1621=true := by decide +kernel
noncomputable def cell2902 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2902.certificate 1621 accepted2902
theorem accepted2903 : minorantGammaCheck GammaPanel2903.certificate 1621=true := by decide +kernel
noncomputable def cell2903 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2903.certificate 1621 accepted2903
noncomputable def cells : List CertifiedMinorantCell := [cell2896, cell2897, cell2898, cell2899, cell2900, cell2901, cell2902, cell2903]
theorem chainAccepted : minorantChainCheck (12473/12500) (24947/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (12473/12500) (24947/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0362
