module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0269

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0269
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2152 : minorantGammaCheck GammaPanel2152.certificate 1621=true := by decide +kernel
noncomputable def cell2152 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2152.certificate 1621 accepted2152
theorem accepted2153 : minorantGammaCheck GammaPanel2153.certificate 1621=true := by decide +kernel
noncomputable def cell2153 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2153.certificate 1621 accepted2153
theorem accepted2154 : minorantGammaCheck GammaPanel2154.certificate 1621=true := by decide +kernel
noncomputable def cell2154 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2154.certificate 1621 accepted2154
theorem accepted2155 : minorantGammaCheck GammaPanel2155.certificate 1621=true := by decide +kernel
noncomputable def cell2155 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2155.certificate 1621 accepted2155
theorem accepted2156 : minorantGammaCheck GammaPanel2156.certificate 1621=true := by decide +kernel
noncomputable def cell2156 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2156.certificate 1621 accepted2156
theorem accepted2157 : minorantGammaCheck GammaPanel2157.certificate 1621=true := by decide +kernel
noncomputable def cell2157 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2157.certificate 1621 accepted2157
theorem accepted2158 : minorantGammaCheck GammaPanel2158.certificate 1621=true := by decide +kernel
noncomputable def cell2158 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2158.certificate 1621 accepted2158
theorem accepted2159 : minorantGammaCheck GammaPanel2159.certificate 1621=true := by decide +kernel
noncomputable def cell2159 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2159.certificate 1621 accepted2159
noncomputable def cells : List CertifiedMinorantCell := [cell2152, cell2153, cell2154, cell2155, cell2156, cell2157, cell2158, cell2159]
theorem chainAccepted : minorantChainCheck (4837/5000) (4841/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4837/5000) (4841/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0269
