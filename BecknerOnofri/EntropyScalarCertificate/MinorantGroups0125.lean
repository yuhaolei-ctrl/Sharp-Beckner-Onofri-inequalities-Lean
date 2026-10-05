import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0125
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0125
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1000 : minorantGammaCheck GammaPanel1000.certificate 898=true := by decide +kernel
noncomputable def cell1000 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1000.certificate 898 accepted1000
theorem accepted1001 : minorantGammaCheck GammaPanel1001.certificate 899=true := by decide +kernel
noncomputable def cell1001 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1001.certificate 899 accepted1001
theorem accepted1002 : minorantGammaCheck GammaPanel1002.certificate 900=true := by decide +kernel
noncomputable def cell1002 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1002.certificate 900 accepted1002
theorem accepted1003 : minorantGammaCheck GammaPanel1003.certificate 901=true := by decide +kernel
noncomputable def cell1003 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1003.certificate 901 accepted1003
theorem accepted1004 : minorantGammaCheck GammaPanel1004.certificate 902=true := by decide +kernel
noncomputable def cell1004 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1004.certificate 902 accepted1004
theorem accepted1005 : minorantGammaCheck GammaPanel1005.certificate 903=true := by decide +kernel
noncomputable def cell1005 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1005.certificate 903 accepted1005
theorem accepted1006 : minorantGammaCheck GammaPanel1006.certificate 904=true := by decide +kernel
noncomputable def cell1006 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1006.certificate 904 accepted1006
theorem accepted1007 : minorantGammaCheck GammaPanel1007.certificate 905=true := by decide +kernel
noncomputable def cell1007 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1007.certificate 905 accepted1007
noncomputable def cells : List CertifiedMinorantCell := [cell1000, cell1001, cell1002, cell1003, cell1004, cell1005, cell1006, cell1007]
theorem chainAccepted : minorantChainCheck (241/500) (49/100) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (241/500) (49/100) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0125
