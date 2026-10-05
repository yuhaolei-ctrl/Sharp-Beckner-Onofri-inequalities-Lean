module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0247

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0247
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1976 : minorantGammaCheck GammaPanel1976.certificate 1620=true := by decide +kernel
noncomputable def cell1976 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1976.certificate 1620 accepted1976
theorem accepted1977 : minorantGammaCheck GammaPanel1977.certificate 1621=true := by decide +kernel
noncomputable def cell1977 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1977.certificate 1621 accepted1977
theorem accepted1978 : minorantGammaCheck GammaPanel1978.certificate 1621=true := by decide +kernel
noncomputable def cell1978 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1978.certificate 1621 accepted1978
theorem accepted1979 : minorantGammaCheck GammaPanel1979.certificate 1621=true := by decide +kernel
noncomputable def cell1979 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1979.certificate 1621 accepted1979
theorem accepted1980 : minorantGammaCheck GammaPanel1980.certificate 1621=true := by decide +kernel
noncomputable def cell1980 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1980.certificate 1621 accepted1980
theorem accepted1981 : minorantGammaCheck GammaPanel1981.certificate 1621=true := by decide +kernel
noncomputable def cell1981 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1981.certificate 1621 accepted1981
theorem accepted1982 : minorantGammaCheck GammaPanel1982.certificate 1621=true := by decide +kernel
noncomputable def cell1982 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1982.certificate 1621 accepted1982
theorem accepted1983 : minorantGammaCheck GammaPanel1983.certificate 1621=true := by decide +kernel
noncomputable def cell1983 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1983.certificate 1621 accepted1983
noncomputable def cells : List CertifiedMinorantCell := [cell1976, cell1977, cell1978, cell1979, cell1980, cell1981, cell1982, cell1983]
theorem chainAccepted : minorantChainCheck (949/1000) (4753/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (949/1000) (4753/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0247
