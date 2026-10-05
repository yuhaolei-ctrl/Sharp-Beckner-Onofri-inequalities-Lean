module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0133

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0133
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1064 : minorantGammaCheck GammaPanel1064.certificate 962=true := by decide +kernel
noncomputable def cell1064 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1064.certificate 962 accepted1064
theorem accepted1065 : minorantGammaCheck GammaPanel1065.certificate 963=true := by decide +kernel
noncomputable def cell1065 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1065.certificate 963 accepted1065
theorem accepted1066 : minorantGammaCheck GammaPanel1066.certificate 964=true := by decide +kernel
noncomputable def cell1066 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1066.certificate 964 accepted1066
theorem accepted1067 : minorantGammaCheck GammaPanel1067.certificate 965=true := by decide +kernel
noncomputable def cell1067 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1067.certificate 965 accepted1067
theorem accepted1068 : minorantGammaCheck GammaPanel1068.certificate 966=true := by decide +kernel
noncomputable def cell1068 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1068.certificate 966 accepted1068
theorem accepted1069 : minorantGammaCheck GammaPanel1069.certificate 967=true := by decide +kernel
noncomputable def cell1069 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1069.certificate 967 accepted1069
theorem accepted1070 : minorantGammaCheck GammaPanel1070.certificate 968=true := by decide +kernel
noncomputable def cell1070 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1070.certificate 968 accepted1070
theorem accepted1071 : minorantGammaCheck GammaPanel1071.certificate 969=true := by decide +kernel
noncomputable def cell1071 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1071.certificate 969 accepted1071
noncomputable def cells : List CertifiedMinorantCell := [cell1064, cell1065, cell1066, cell1067, cell1068, cell1069, cell1070, cell1071]
theorem chainAccepted : minorantChainCheck (273/500) (277/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (273/500) (277/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0133
