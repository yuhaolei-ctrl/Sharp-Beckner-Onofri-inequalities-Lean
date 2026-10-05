import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0249
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0249
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1992 : minorantGammaCheck GammaPanel1992.certificate 1621=true := by decide +kernel
noncomputable def cell1992 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1992.certificate 1621 accepted1992
theorem accepted1993 : minorantGammaCheck GammaPanel1993.certificate 1621=true := by decide +kernel
noncomputable def cell1993 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1993.certificate 1621 accepted1993
theorem accepted1994 : minorantGammaCheck GammaPanel1994.certificate 1621=true := by decide +kernel
noncomputable def cell1994 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1994.certificate 1621 accepted1994
theorem accepted1995 : minorantGammaCheck GammaPanel1995.certificate 1621=true := by decide +kernel
noncomputable def cell1995 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1995.certificate 1621 accepted1995
theorem accepted1996 : minorantGammaCheck GammaPanel1996.certificate 1621=true := by decide +kernel
noncomputable def cell1996 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1996.certificate 1621 accepted1996
theorem accepted1997 : minorantGammaCheck GammaPanel1997.certificate 1621=true := by decide +kernel
noncomputable def cell1997 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1997.certificate 1621 accepted1997
theorem accepted1998 : minorantGammaCheck GammaPanel1998.certificate 1621=true := by decide +kernel
noncomputable def cell1998 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1998.certificate 1621 accepted1998
theorem accepted1999 : minorantGammaCheck GammaPanel1999.certificate 1621=true := by decide +kernel
noncomputable def cell1999 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1999.certificate 1621 accepted1999
noncomputable def cells : List CertifiedMinorantCell := [cell1992, cell1993, cell1994, cell1995, cell1996, cell1997, cell1998, cell1999]
theorem chainAccepted : minorantChainCheck (4757/5000) (4761/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4757/5000) (4761/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0249
