import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0235
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0235
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1880 : minorantGammaCheck GammaPanel1880.certificate 1524=true := by decide +kernel
noncomputable def cell1880 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1880.certificate 1524 accepted1880
theorem accepted1881 : minorantGammaCheck GammaPanel1881.certificate 1525=true := by decide +kernel
noncomputable def cell1881 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1881.certificate 1525 accepted1881
theorem accepted1882 : minorantGammaCheck GammaPanel1882.certificate 1526=true := by decide +kernel
noncomputable def cell1882 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1882.certificate 1526 accepted1882
theorem accepted1883 : minorantGammaCheck GammaPanel1883.certificate 1527=true := by decide +kernel
noncomputable def cell1883 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1883.certificate 1527 accepted1883
theorem accepted1884 : minorantGammaCheck GammaPanel1884.certificate 1528=true := by decide +kernel
noncomputable def cell1884 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1884.certificate 1528 accepted1884
theorem accepted1885 : minorantGammaCheck GammaPanel1885.certificate 1529=true := by decide +kernel
noncomputable def cell1885 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1885.certificate 1529 accepted1885
theorem accepted1886 : minorantGammaCheck GammaPanel1886.certificate 1530=true := by decide +kernel
noncomputable def cell1886 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1886.certificate 1530 accepted1886
theorem accepted1887 : minorantGammaCheck GammaPanel1887.certificate 1531=true := by decide +kernel
noncomputable def cell1887 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1887.certificate 1531 accepted1887
noncomputable def cells : List CertifiedMinorantCell := [cell1880, cell1881, cell1882, cell1883, cell1884, cell1885, cell1886, cell1887]
theorem chainAccepted : minorantChainCheck (901/1000) (181/200) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (901/1000) (181/200) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0235
