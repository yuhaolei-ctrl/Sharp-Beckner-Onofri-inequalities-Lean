module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0240

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0240
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1920 : minorantGammaCheck GammaPanel1920.certificate 1564=true := by decide +kernel
noncomputable def cell1920 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1920.certificate 1564 accepted1920
theorem accepted1921 : minorantGammaCheck GammaPanel1921.certificate 1565=true := by decide +kernel
noncomputable def cell1921 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1921.certificate 1565 accepted1921
theorem accepted1922 : minorantGammaCheck GammaPanel1922.certificate 1566=true := by decide +kernel
noncomputable def cell1922 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1922.certificate 1566 accepted1922
theorem accepted1923 : minorantGammaCheck GammaPanel1923.certificate 1567=true := by decide +kernel
noncomputable def cell1923 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1923.certificate 1567 accepted1923
theorem accepted1924 : minorantGammaCheck GammaPanel1924.certificate 1568=true := by decide +kernel
noncomputable def cell1924 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1924.certificate 1568 accepted1924
theorem accepted1925 : minorantGammaCheck GammaPanel1925.certificate 1569=true := by decide +kernel
noncomputable def cell1925 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1925.certificate 1569 accepted1925
theorem accepted1926 : minorantGammaCheck GammaPanel1926.certificate 1570=true := by decide +kernel
noncomputable def cell1926 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1926.certificate 1570 accepted1926
theorem accepted1927 : minorantGammaCheck GammaPanel1927.certificate 1571=true := by decide +kernel
noncomputable def cell1927 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1927.certificate 1571 accepted1927
noncomputable def cells : List CertifiedMinorantCell := [cell1920, cell1921, cell1922, cell1923, cell1924, cell1925, cell1926, cell1927]
theorem chainAccepted : minorantChainCheck (921/1000) (37/40) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (921/1000) (37/40) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0240
