import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0248
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0248
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1984 : minorantGammaCheck GammaPanel1984.certificate 1621=true := by decide +kernel
noncomputable def cell1984 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1984.certificate 1621 accepted1984
theorem accepted1985 : minorantGammaCheck GammaPanel1985.certificate 1621=true := by decide +kernel
noncomputable def cell1985 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1985.certificate 1621 accepted1985
theorem accepted1986 : minorantGammaCheck GammaPanel1986.certificate 1621=true := by decide +kernel
noncomputable def cell1986 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1986.certificate 1621 accepted1986
theorem accepted1987 : minorantGammaCheck GammaPanel1987.certificate 1621=true := by decide +kernel
noncomputable def cell1987 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1987.certificate 1621 accepted1987
theorem accepted1988 : minorantGammaCheck GammaPanel1988.certificate 1621=true := by decide +kernel
noncomputable def cell1988 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1988.certificate 1621 accepted1988
theorem accepted1989 : minorantGammaCheck GammaPanel1989.certificate 1621=true := by decide +kernel
noncomputable def cell1989 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1989.certificate 1621 accepted1989
theorem accepted1990 : minorantGammaCheck GammaPanel1990.certificate 1621=true := by decide +kernel
noncomputable def cell1990 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1990.certificate 1621 accepted1990
theorem accepted1991 : minorantGammaCheck GammaPanel1991.certificate 1621=true := by decide +kernel
noncomputable def cell1991 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1991.certificate 1621 accepted1991
noncomputable def cells : List CertifiedMinorantCell := [cell1984, cell1985, cell1986, cell1987, cell1988, cell1989, cell1990, cell1991]
theorem chainAccepted : minorantChainCheck (4753/5000) (4757/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4753/5000) (4757/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0248
