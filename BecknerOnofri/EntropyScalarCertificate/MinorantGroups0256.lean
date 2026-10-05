module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0256

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0256
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2048 : minorantGammaCheck GammaPanel2048.certificate 1621=true := by decide +kernel
noncomputable def cell2048 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2048.certificate 1621 accepted2048
theorem accepted2049 : minorantGammaCheck GammaPanel2049.certificate 1621=true := by decide +kernel
noncomputable def cell2049 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2049.certificate 1621 accepted2049
theorem accepted2050 : minorantGammaCheck GammaPanel2050.certificate 1621=true := by decide +kernel
noncomputable def cell2050 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2050.certificate 1621 accepted2050
theorem accepted2051 : minorantGammaCheck GammaPanel2051.certificate 1621=true := by decide +kernel
noncomputable def cell2051 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2051.certificate 1621 accepted2051
theorem accepted2052 : minorantGammaCheck GammaPanel2052.certificate 1621=true := by decide +kernel
noncomputable def cell2052 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2052.certificate 1621 accepted2052
theorem accepted2053 : minorantGammaCheck GammaPanel2053.certificate 1621=true := by decide +kernel
noncomputable def cell2053 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2053.certificate 1621 accepted2053
theorem accepted2054 : minorantGammaCheck GammaPanel2054.certificate 1621=true := by decide +kernel
noncomputable def cell2054 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2054.certificate 1621 accepted2054
theorem accepted2055 : minorantGammaCheck GammaPanel2055.certificate 1621=true := by decide +kernel
noncomputable def cell2055 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2055.certificate 1621 accepted2055
noncomputable def cells : List CertifiedMinorantCell := [cell2048, cell2049, cell2050, cell2051, cell2052, cell2053, cell2054, cell2055]
theorem chainAccepted : minorantChainCheck (957/1000) (4789/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (957/1000) (4789/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0256
