module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0236

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0236
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1888 : minorantGammaCheck GammaPanel1888.certificate 1532=true := by decide +kernel
noncomputable def cell1888 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1888.certificate 1532 accepted1888
theorem accepted1889 : minorantGammaCheck GammaPanel1889.certificate 1533=true := by decide +kernel
noncomputable def cell1889 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1889.certificate 1533 accepted1889
theorem accepted1890 : minorantGammaCheck GammaPanel1890.certificate 1534=true := by decide +kernel
noncomputable def cell1890 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1890.certificate 1534 accepted1890
theorem accepted1891 : minorantGammaCheck GammaPanel1891.certificate 1535=true := by decide +kernel
noncomputable def cell1891 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1891.certificate 1535 accepted1891
theorem accepted1892 : minorantGammaCheck GammaPanel1892.certificate 1536=true := by decide +kernel
noncomputable def cell1892 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1892.certificate 1536 accepted1892
theorem accepted1893 : minorantGammaCheck GammaPanel1893.certificate 1537=true := by decide +kernel
noncomputable def cell1893 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1893.certificate 1537 accepted1893
theorem accepted1894 : minorantGammaCheck GammaPanel1894.certificate 1538=true := by decide +kernel
noncomputable def cell1894 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1894.certificate 1538 accepted1894
theorem accepted1895 : minorantGammaCheck GammaPanel1895.certificate 1539=true := by decide +kernel
noncomputable def cell1895 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1895.certificate 1539 accepted1895
noncomputable def cells : List CertifiedMinorantCell := [cell1888, cell1889, cell1890, cell1891, cell1892, cell1893, cell1894, cell1895]
theorem chainAccepted : minorantChainCheck (181/200) (909/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (181/200) (909/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0236
