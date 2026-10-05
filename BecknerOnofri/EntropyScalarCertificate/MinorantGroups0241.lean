module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0241

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0241
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1928 : minorantGammaCheck GammaPanel1928.certificate 1572=true := by decide +kernel
noncomputable def cell1928 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1928.certificate 1572 accepted1928
theorem accepted1929 : minorantGammaCheck GammaPanel1929.certificate 1573=true := by decide +kernel
noncomputable def cell1929 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1929.certificate 1573 accepted1929
theorem accepted1930 : minorantGammaCheck GammaPanel1930.certificate 1574=true := by decide +kernel
noncomputable def cell1930 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1930.certificate 1574 accepted1930
theorem accepted1931 : minorantGammaCheck GammaPanel1931.certificate 1575=true := by decide +kernel
noncomputable def cell1931 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1931.certificate 1575 accepted1931
theorem accepted1932 : minorantGammaCheck GammaPanel1932.certificate 1576=true := by decide +kernel
noncomputable def cell1932 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1932.certificate 1576 accepted1932
theorem accepted1933 : minorantGammaCheck GammaPanel1933.certificate 1577=true := by decide +kernel
noncomputable def cell1933 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1933.certificate 1577 accepted1933
theorem accepted1934 : minorantGammaCheck GammaPanel1934.certificate 1578=true := by decide +kernel
noncomputable def cell1934 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1934.certificate 1578 accepted1934
theorem accepted1935 : minorantGammaCheck GammaPanel1935.certificate 1579=true := by decide +kernel
noncomputable def cell1935 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1935.certificate 1579 accepted1935
noncomputable def cells : List CertifiedMinorantCell := [cell1928, cell1929, cell1930, cell1931, cell1932, cell1933, cell1934, cell1935]
theorem chainAccepted : minorantChainCheck (37/40) (929/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (37/40) (929/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0241
