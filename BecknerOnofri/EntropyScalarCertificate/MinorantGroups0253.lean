module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0253

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0253
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2024 : minorantGammaCheck GammaPanel2024.certificate 1621=true := by decide +kernel
noncomputable def cell2024 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2024.certificate 1621 accepted2024
theorem accepted2025 : minorantGammaCheck GammaPanel2025.certificate 1621=true := by decide +kernel
noncomputable def cell2025 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2025.certificate 1621 accepted2025
theorem accepted2026 : minorantGammaCheck GammaPanel2026.certificate 1621=true := by decide +kernel
noncomputable def cell2026 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2026.certificate 1621 accepted2026
theorem accepted2027 : minorantGammaCheck GammaPanel2027.certificate 1621=true := by decide +kernel
noncomputable def cell2027 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2027.certificate 1621 accepted2027
theorem accepted2028 : minorantGammaCheck GammaPanel2028.certificate 1621=true := by decide +kernel
noncomputable def cell2028 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2028.certificate 1621 accepted2028
theorem accepted2029 : minorantGammaCheck GammaPanel2029.certificate 1621=true := by decide +kernel
noncomputable def cell2029 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2029.certificate 1621 accepted2029
theorem accepted2030 : minorantGammaCheck GammaPanel2030.certificate 1621=true := by decide +kernel
noncomputable def cell2030 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2030.certificate 1621 accepted2030
theorem accepted2031 : minorantGammaCheck GammaPanel2031.certificate 1621=true := by decide +kernel
noncomputable def cell2031 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2031.certificate 1621 accepted2031
noncomputable def cells : List CertifiedMinorantCell := [cell2024, cell2025, cell2026, cell2027, cell2028, cell2029, cell2030, cell2031]
theorem chainAccepted : minorantChainCheck (4773/5000) (4777/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4773/5000) (4777/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0253
