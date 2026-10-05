module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0237

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0237
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1896 : minorantGammaCheck GammaPanel1896.certificate 1540=true := by decide +kernel
noncomputable def cell1896 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1896.certificate 1540 accepted1896
theorem accepted1897 : minorantGammaCheck GammaPanel1897.certificate 1541=true := by decide +kernel
noncomputable def cell1897 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1897.certificate 1541 accepted1897
theorem accepted1898 : minorantGammaCheck GammaPanel1898.certificate 1542=true := by decide +kernel
noncomputable def cell1898 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1898.certificate 1542 accepted1898
theorem accepted1899 : minorantGammaCheck GammaPanel1899.certificate 1543=true := by decide +kernel
noncomputable def cell1899 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1899.certificate 1543 accepted1899
theorem accepted1900 : minorantGammaCheck GammaPanel1900.certificate 1544=true := by decide +kernel
noncomputable def cell1900 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1900.certificate 1544 accepted1900
theorem accepted1901 : minorantGammaCheck GammaPanel1901.certificate 1545=true := by decide +kernel
noncomputable def cell1901 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1901.certificate 1545 accepted1901
theorem accepted1902 : minorantGammaCheck GammaPanel1902.certificate 1546=true := by decide +kernel
noncomputable def cell1902 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1902.certificate 1546 accepted1902
theorem accepted1903 : minorantGammaCheck GammaPanel1903.certificate 1547=true := by decide +kernel
noncomputable def cell1903 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1903.certificate 1547 accepted1903
noncomputable def cells : List CertifiedMinorantCell := [cell1896, cell1897, cell1898, cell1899, cell1900, cell1901, cell1902, cell1903]
theorem chainAccepted : minorantChainCheck (909/1000) (913/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (909/1000) (913/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0237
