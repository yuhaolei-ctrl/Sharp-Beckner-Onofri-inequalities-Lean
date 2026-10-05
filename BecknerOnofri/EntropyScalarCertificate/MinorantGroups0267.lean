module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0267

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0267
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2136 : minorantGammaCheck GammaPanel2136.certificate 1621=true := by decide +kernel
noncomputable def cell2136 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2136.certificate 1621 accepted2136
theorem accepted2137 : minorantGammaCheck GammaPanel2137.certificate 1621=true := by decide +kernel
noncomputable def cell2137 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2137.certificate 1621 accepted2137
theorem accepted2138 : minorantGammaCheck GammaPanel2138.certificate 1621=true := by decide +kernel
noncomputable def cell2138 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2138.certificate 1621 accepted2138
theorem accepted2139 : minorantGammaCheck GammaPanel2139.certificate 1621=true := by decide +kernel
noncomputable def cell2139 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2139.certificate 1621 accepted2139
theorem accepted2140 : minorantGammaCheck GammaPanel2140.certificate 1621=true := by decide +kernel
noncomputable def cell2140 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2140.certificate 1621 accepted2140
theorem accepted2141 : minorantGammaCheck GammaPanel2141.certificate 1621=true := by decide +kernel
noncomputable def cell2141 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2141.certificate 1621 accepted2141
theorem accepted2142 : minorantGammaCheck GammaPanel2142.certificate 1621=true := by decide +kernel
noncomputable def cell2142 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2142.certificate 1621 accepted2142
theorem accepted2143 : minorantGammaCheck GammaPanel2143.certificate 1621=true := by decide +kernel
noncomputable def cell2143 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2143.certificate 1621 accepted2143
noncomputable def cells : List CertifiedMinorantCell := [cell2136, cell2137, cell2138, cell2139, cell2140, cell2141, cell2142, cell2143]
theorem chainAccepted : minorantChainCheck (4829/5000) (4833/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4829/5000) (4833/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0267
