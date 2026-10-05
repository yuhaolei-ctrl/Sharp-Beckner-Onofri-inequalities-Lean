module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0270

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0270
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2160 : minorantGammaCheck GammaPanel2160.certificate 1621=true := by decide +kernel
noncomputable def cell2160 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2160.certificate 1621 accepted2160
theorem accepted2161 : minorantGammaCheck GammaPanel2161.certificate 1621=true := by decide +kernel
noncomputable def cell2161 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2161.certificate 1621 accepted2161
theorem accepted2162 : minorantGammaCheck GammaPanel2162.certificate 1621=true := by decide +kernel
noncomputable def cell2162 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2162.certificate 1621 accepted2162
theorem accepted2163 : minorantGammaCheck GammaPanel2163.certificate 1621=true := by decide +kernel
noncomputable def cell2163 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2163.certificate 1621 accepted2163
theorem accepted2164 : minorantGammaCheck GammaPanel2164.certificate 1621=true := by decide +kernel
noncomputable def cell2164 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2164.certificate 1621 accepted2164
theorem accepted2165 : minorantGammaCheck GammaPanel2165.certificate 1621=true := by decide +kernel
noncomputable def cell2165 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2165.certificate 1621 accepted2165
theorem accepted2166 : minorantGammaCheck GammaPanel2166.certificate 1621=true := by decide +kernel
noncomputable def cell2166 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2166.certificate 1621 accepted2166
theorem accepted2167 : minorantGammaCheck GammaPanel2167.certificate 1621=true := by decide +kernel
noncomputable def cell2167 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2167.certificate 1621 accepted2167
noncomputable def cells : List CertifiedMinorantCell := [cell2160, cell2161, cell2162, cell2163, cell2164, cell2165, cell2166, cell2167]
theorem chainAccepted : minorantChainCheck (4841/5000) (969/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4841/5000) (969/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0270
