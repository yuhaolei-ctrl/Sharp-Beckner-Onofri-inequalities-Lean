import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0131
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0131
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1048 : minorantGammaCheck GammaPanel1048.certificate 946=true := by decide +kernel
noncomputable def cell1048 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1048.certificate 946 accepted1048
theorem accepted1049 : minorantGammaCheck GammaPanel1049.certificate 947=true := by decide +kernel
noncomputable def cell1049 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1049.certificate 947 accepted1049
theorem accepted1050 : minorantGammaCheck GammaPanel1050.certificate 948=true := by decide +kernel
noncomputable def cell1050 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1050.certificate 948 accepted1050
theorem accepted1051 : minorantGammaCheck GammaPanel1051.certificate 949=true := by decide +kernel
noncomputable def cell1051 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1051.certificate 949 accepted1051
theorem accepted1052 : minorantGammaCheck GammaPanel1052.certificate 950=true := by decide +kernel
noncomputable def cell1052 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1052.certificate 950 accepted1052
theorem accepted1053 : minorantGammaCheck GammaPanel1053.certificate 951=true := by decide +kernel
noncomputable def cell1053 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1053.certificate 951 accepted1053
theorem accepted1054 : minorantGammaCheck GammaPanel1054.certificate 952=true := by decide +kernel
noncomputable def cell1054 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1054.certificate 952 accepted1054
theorem accepted1055 : minorantGammaCheck GammaPanel1055.certificate 953=true := by decide +kernel
noncomputable def cell1055 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1055.certificate 953 accepted1055
noncomputable def cells : List CertifiedMinorantCell := [cell1048, cell1049, cell1050, cell1051, cell1052, cell1053, cell1054, cell1055]
theorem chainAccepted : minorantChainCheck (53/100) (269/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (53/100) (269/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0131
