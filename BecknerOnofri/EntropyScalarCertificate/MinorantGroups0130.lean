module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0130

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0130
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1040 : minorantGammaCheck GammaPanel1040.certificate 938=true := by decide +kernel
noncomputable def cell1040 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1040.certificate 938 accepted1040
theorem accepted1041 : minorantGammaCheck GammaPanel1041.certificate 939=true := by decide +kernel
noncomputable def cell1041 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1041.certificate 939 accepted1041
theorem accepted1042 : minorantGammaCheck GammaPanel1042.certificate 940=true := by decide +kernel
noncomputable def cell1042 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1042.certificate 940 accepted1042
theorem accepted1043 : minorantGammaCheck GammaPanel1043.certificate 941=true := by decide +kernel
noncomputable def cell1043 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1043.certificate 941 accepted1043
theorem accepted1044 : minorantGammaCheck GammaPanel1044.certificate 942=true := by decide +kernel
noncomputable def cell1044 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1044.certificate 942 accepted1044
theorem accepted1045 : minorantGammaCheck GammaPanel1045.certificate 943=true := by decide +kernel
noncomputable def cell1045 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1045.certificate 943 accepted1045
theorem accepted1046 : minorantGammaCheck GammaPanel1046.certificate 944=true := by decide +kernel
noncomputable def cell1046 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1046.certificate 944 accepted1046
theorem accepted1047 : minorantGammaCheck GammaPanel1047.certificate 945=true := by decide +kernel
noncomputable def cell1047 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1047.certificate 945 accepted1047
noncomputable def cells : List CertifiedMinorantCell := [cell1040, cell1041, cell1042, cell1043, cell1044, cell1045, cell1046, cell1047]
theorem chainAccepted : minorantChainCheck (261/500) (53/100) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (261/500) (53/100) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0130
