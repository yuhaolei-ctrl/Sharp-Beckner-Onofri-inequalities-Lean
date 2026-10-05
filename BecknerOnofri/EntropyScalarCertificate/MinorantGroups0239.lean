module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0239

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0239
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1912 : minorantGammaCheck GammaPanel1912.certificate 1556=true := by decide +kernel
noncomputable def cell1912 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1912.certificate 1556 accepted1912
theorem accepted1913 : minorantGammaCheck GammaPanel1913.certificate 1557=true := by decide +kernel
noncomputable def cell1913 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1913.certificate 1557 accepted1913
theorem accepted1914 : minorantGammaCheck GammaPanel1914.certificate 1558=true := by decide +kernel
noncomputable def cell1914 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1914.certificate 1558 accepted1914
theorem accepted1915 : minorantGammaCheck GammaPanel1915.certificate 1559=true := by decide +kernel
noncomputable def cell1915 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1915.certificate 1559 accepted1915
theorem accepted1916 : minorantGammaCheck GammaPanel1916.certificate 1560=true := by decide +kernel
noncomputable def cell1916 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1916.certificate 1560 accepted1916
theorem accepted1917 : minorantGammaCheck GammaPanel1917.certificate 1561=true := by decide +kernel
noncomputable def cell1917 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1917.certificate 1561 accepted1917
theorem accepted1918 : minorantGammaCheck GammaPanel1918.certificate 1562=true := by decide +kernel
noncomputable def cell1918 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1918.certificate 1562 accepted1918
theorem accepted1919 : minorantGammaCheck GammaPanel1919.certificate 1563=true := by decide +kernel
noncomputable def cell1919 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1919.certificate 1563 accepted1919
noncomputable def cells : List CertifiedMinorantCell := [cell1912, cell1913, cell1914, cell1915, cell1916, cell1917, cell1918, cell1919]
theorem chainAccepted : minorantChainCheck (917/1000) (921/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (917/1000) (921/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0239
