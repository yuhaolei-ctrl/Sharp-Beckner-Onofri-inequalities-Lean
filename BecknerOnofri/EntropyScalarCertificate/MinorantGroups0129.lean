module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0129

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0129
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1032 : minorantGammaCheck GammaPanel1032.certificate 930=true := by decide +kernel
noncomputable def cell1032 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1032.certificate 930 accepted1032
theorem accepted1033 : minorantGammaCheck GammaPanel1033.certificate 931=true := by decide +kernel
noncomputable def cell1033 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1033.certificate 931 accepted1033
theorem accepted1034 : minorantGammaCheck GammaPanel1034.certificate 932=true := by decide +kernel
noncomputable def cell1034 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1034.certificate 932 accepted1034
theorem accepted1035 : minorantGammaCheck GammaPanel1035.certificate 933=true := by decide +kernel
noncomputable def cell1035 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1035.certificate 933 accepted1035
theorem accepted1036 : minorantGammaCheck GammaPanel1036.certificate 934=true := by decide +kernel
noncomputable def cell1036 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1036.certificate 934 accepted1036
theorem accepted1037 : minorantGammaCheck GammaPanel1037.certificate 935=true := by decide +kernel
noncomputable def cell1037 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1037.certificate 935 accepted1037
theorem accepted1038 : minorantGammaCheck GammaPanel1038.certificate 936=true := by decide +kernel
noncomputable def cell1038 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1038.certificate 936 accepted1038
theorem accepted1039 : minorantGammaCheck GammaPanel1039.certificate 937=true := by decide +kernel
noncomputable def cell1039 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1039.certificate 937 accepted1039
noncomputable def cells : List CertifiedMinorantCell := [cell1032, cell1033, cell1034, cell1035, cell1036, cell1037, cell1038, cell1039]
theorem chainAccepted : minorantChainCheck (257/500) (261/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (257/500) (261/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0129
