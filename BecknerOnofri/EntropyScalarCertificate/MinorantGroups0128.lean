module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0128

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0128
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1024 : minorantGammaCheck GammaPanel1024.certificate 922=true := by decide +kernel
noncomputable def cell1024 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1024.certificate 922 accepted1024
theorem accepted1025 : minorantGammaCheck GammaPanel1025.certificate 923=true := by decide +kernel
noncomputable def cell1025 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1025.certificate 923 accepted1025
theorem accepted1026 : minorantGammaCheck GammaPanel1026.certificate 924=true := by decide +kernel
noncomputable def cell1026 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1026.certificate 924 accepted1026
theorem accepted1027 : minorantGammaCheck GammaPanel1027.certificate 925=true := by decide +kernel
noncomputable def cell1027 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1027.certificate 925 accepted1027
theorem accepted1028 : minorantGammaCheck GammaPanel1028.certificate 926=true := by decide +kernel
noncomputable def cell1028 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1028.certificate 926 accepted1028
theorem accepted1029 : minorantGammaCheck GammaPanel1029.certificate 927=true := by decide +kernel
noncomputable def cell1029 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1029.certificate 927 accepted1029
theorem accepted1030 : minorantGammaCheck GammaPanel1030.certificate 928=true := by decide +kernel
noncomputable def cell1030 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1030.certificate 928 accepted1030
theorem accepted1031 : minorantGammaCheck GammaPanel1031.certificate 929=true := by decide +kernel
noncomputable def cell1031 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1031.certificate 929 accepted1031
noncomputable def cells : List CertifiedMinorantCell := [cell1024, cell1025, cell1026, cell1027, cell1028, cell1029, cell1030, cell1031]
theorem chainAccepted : minorantChainCheck (253/500) (257/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (253/500) (257/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0128
