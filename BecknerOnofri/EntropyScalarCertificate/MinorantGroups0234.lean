module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0234

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0234
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1872 : minorantGammaCheck GammaPanel1872.certificate 1516=true := by decide +kernel
noncomputable def cell1872 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1872.certificate 1516 accepted1872
theorem accepted1873 : minorantGammaCheck GammaPanel1873.certificate 1517=true := by decide +kernel
noncomputable def cell1873 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1873.certificate 1517 accepted1873
theorem accepted1874 : minorantGammaCheck GammaPanel1874.certificate 1518=true := by decide +kernel
noncomputable def cell1874 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1874.certificate 1518 accepted1874
theorem accepted1875 : minorantGammaCheck GammaPanel1875.certificate 1519=true := by decide +kernel
noncomputable def cell1875 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1875.certificate 1519 accepted1875
theorem accepted1876 : minorantGammaCheck GammaPanel1876.certificate 1520=true := by decide +kernel
noncomputable def cell1876 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1876.certificate 1520 accepted1876
theorem accepted1877 : minorantGammaCheck GammaPanel1877.certificate 1521=true := by decide +kernel
noncomputable def cell1877 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1877.certificate 1521 accepted1877
theorem accepted1878 : minorantGammaCheck GammaPanel1878.certificate 1522=true := by decide +kernel
noncomputable def cell1878 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1878.certificate 1522 accepted1878
theorem accepted1879 : minorantGammaCheck GammaPanel1879.certificate 1523=true := by decide +kernel
noncomputable def cell1879 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1879.certificate 1523 accepted1879
noncomputable def cells : List CertifiedMinorantCell := [cell1872, cell1873, cell1874, cell1875, cell1876, cell1877, cell1878, cell1879]
theorem chainAccepted : minorantChainCheck (897/1000) (901/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (897/1000) (901/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0234
