import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0233
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0233
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1864 : minorantGammaCheck GammaPanel1864.certificate 1508=true := by decide +kernel
noncomputable def cell1864 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1864.certificate 1508 accepted1864
theorem accepted1865 : minorantGammaCheck GammaPanel1865.certificate 1509=true := by decide +kernel
noncomputable def cell1865 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1865.certificate 1509 accepted1865
theorem accepted1866 : minorantGammaCheck GammaPanel1866.certificate 1510=true := by decide +kernel
noncomputable def cell1866 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1866.certificate 1510 accepted1866
theorem accepted1867 : minorantGammaCheck GammaPanel1867.certificate 1511=true := by decide +kernel
noncomputable def cell1867 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1867.certificate 1511 accepted1867
theorem accepted1868 : minorantGammaCheck GammaPanel1868.certificate 1512=true := by decide +kernel
noncomputable def cell1868 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1868.certificate 1512 accepted1868
theorem accepted1869 : minorantGammaCheck GammaPanel1869.certificate 1513=true := by decide +kernel
noncomputable def cell1869 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1869.certificate 1513 accepted1869
theorem accepted1870 : minorantGammaCheck GammaPanel1870.certificate 1514=true := by decide +kernel
noncomputable def cell1870 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1870.certificate 1514 accepted1870
theorem accepted1871 : minorantGammaCheck GammaPanel1871.certificate 1515=true := by decide +kernel
noncomputable def cell1871 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1871.certificate 1515 accepted1871
noncomputable def cells : List CertifiedMinorantCell := [cell1864, cell1865, cell1866, cell1867, cell1868, cell1869, cell1870, cell1871]
theorem chainAccepted : minorantChainCheck (893/1000) (897/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (893/1000) (897/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0233
