import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0250
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0250
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2000 : minorantGammaCheck GammaPanel2000.certificate 1621=true := by decide +kernel
noncomputable def cell2000 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2000.certificate 1621 accepted2000
theorem accepted2001 : minorantGammaCheck GammaPanel2001.certificate 1621=true := by decide +kernel
noncomputable def cell2001 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2001.certificate 1621 accepted2001
theorem accepted2002 : minorantGammaCheck GammaPanel2002.certificate 1621=true := by decide +kernel
noncomputable def cell2002 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2002.certificate 1621 accepted2002
theorem accepted2003 : minorantGammaCheck GammaPanel2003.certificate 1621=true := by decide +kernel
noncomputable def cell2003 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2003.certificate 1621 accepted2003
theorem accepted2004 : minorantGammaCheck GammaPanel2004.certificate 1621=true := by decide +kernel
noncomputable def cell2004 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2004.certificate 1621 accepted2004
theorem accepted2005 : minorantGammaCheck GammaPanel2005.certificate 1621=true := by decide +kernel
noncomputable def cell2005 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2005.certificate 1621 accepted2005
theorem accepted2006 : minorantGammaCheck GammaPanel2006.certificate 1621=true := by decide +kernel
noncomputable def cell2006 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2006.certificate 1621 accepted2006
theorem accepted2007 : minorantGammaCheck GammaPanel2007.certificate 1621=true := by decide +kernel
noncomputable def cell2007 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2007.certificate 1621 accepted2007
noncomputable def cells : List CertifiedMinorantCell := [cell2000, cell2001, cell2002, cell2003, cell2004, cell2005, cell2006, cell2007]
theorem chainAccepted : minorantChainCheck (4761/5000) (953/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4761/5000) (953/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0250
