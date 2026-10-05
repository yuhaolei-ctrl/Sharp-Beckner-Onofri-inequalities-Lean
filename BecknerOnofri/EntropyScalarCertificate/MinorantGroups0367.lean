import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0367
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0367
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2936 : minorantGammaCheck GammaPanel2936.certificate 1621=true := by decide +kernel
noncomputable def cell2936 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2936.certificate 1621 accepted2936
theorem accepted2937 : minorantGammaCheck GammaPanel2937.certificate 1621=true := by decide +kernel
noncomputable def cell2937 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2937.certificate 1621 accepted2937
theorem accepted2938 : minorantGammaCheck GammaPanel2938.certificate 1621=true := by decide +kernel
noncomputable def cell2938 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2938.certificate 1621 accepted2938
theorem accepted2939 : minorantGammaCheck GammaPanel2939.certificate 1621=true := by decide +kernel
noncomputable def cell2939 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2939.certificate 1621 accepted2939
theorem accepted2940 : minorantGammaCheck GammaPanel2940.certificate 1621=true := by decide +kernel
noncomputable def cell2940 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2940.certificate 1621 accepted2940
theorem accepted2941 : minorantGammaCheck GammaPanel2941.certificate 1621=true := by decide +kernel
noncomputable def cell2941 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2941.certificate 1621 accepted2941
theorem accepted2942 : minorantGammaCheck GammaPanel2942.certificate 1621=true := by decide +kernel
noncomputable def cell2942 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2942.certificate 1621 accepted2942
theorem accepted2943 : minorantGammaCheck GammaPanel2943.certificate 1621=true := by decide +kernel
noncomputable def cell2943 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2943.certificate 1621 accepted2943
noncomputable def cells : List CertifiedMinorantCell := [cell2936, cell2937, cell2938, cell2939, cell2940, cell2941, cell2942, cell2943]
theorem chainAccepted : minorantChainCheck (24951/25000) (3119/3125) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24951/25000) (3119/3125) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0367
