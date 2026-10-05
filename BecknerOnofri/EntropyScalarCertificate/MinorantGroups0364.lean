import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0364
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0364
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2912 : minorantGammaCheck GammaPanel2912.certificate 1621=true := by decide +kernel
noncomputable def cell2912 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2912.certificate 1621 accepted2912
theorem accepted2913 : minorantGammaCheck GammaPanel2913.certificate 1621=true := by decide +kernel
noncomputable def cell2913 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2913.certificate 1621 accepted2913
theorem accepted2914 : minorantGammaCheck GammaPanel2914.certificate 1621=true := by decide +kernel
noncomputable def cell2914 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2914.certificate 1621 accepted2914
theorem accepted2915 : minorantGammaCheck GammaPanel2915.certificate 1621=true := by decide +kernel
noncomputable def cell2915 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2915.certificate 1621 accepted2915
theorem accepted2916 : minorantGammaCheck GammaPanel2916.certificate 1621=true := by decide +kernel
noncomputable def cell2916 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2916.certificate 1621 accepted2916
theorem accepted2917 : minorantGammaCheck GammaPanel2917.certificate 1621=true := by decide +kernel
noncomputable def cell2917 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2917.certificate 1621 accepted2917
theorem accepted2918 : minorantGammaCheck GammaPanel2918.certificate 1621=true := by decide +kernel
noncomputable def cell2918 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2918.certificate 1621 accepted2918
theorem accepted2919 : minorantGammaCheck GammaPanel2919.certificate 1621=true := by decide +kernel
noncomputable def cell2919 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2919.certificate 1621 accepted2919
noncomputable def cells : List CertifiedMinorantCell := [cell2912, cell2913, cell2914, cell2915, cell2916, cell2917, cell2918, cell2919]
theorem chainAccepted : minorantChainCheck (6237/6250) (24949/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (6237/6250) (24949/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0364
