import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0360
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0360
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2880 : minorantGammaCheck GammaPanel2880.certificate 1621=true := by decide +kernel
noncomputable def cell2880 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2880.certificate 1621 accepted2880
theorem accepted2881 : minorantGammaCheck GammaPanel2881.certificate 1621=true := by decide +kernel
noncomputable def cell2881 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2881.certificate 1621 accepted2881
theorem accepted2882 : minorantGammaCheck GammaPanel2882.certificate 1621=true := by decide +kernel
noncomputable def cell2882 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2882.certificate 1621 accepted2882
theorem accepted2883 : minorantGammaCheck GammaPanel2883.certificate 1621=true := by decide +kernel
noncomputable def cell2883 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2883.certificate 1621 accepted2883
theorem accepted2884 : minorantGammaCheck GammaPanel2884.certificate 1621=true := by decide +kernel
noncomputable def cell2884 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2884.certificate 1621 accepted2884
theorem accepted2885 : minorantGammaCheck GammaPanel2885.certificate 1621=true := by decide +kernel
noncomputable def cell2885 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2885.certificate 1621 accepted2885
theorem accepted2886 : minorantGammaCheck GammaPanel2886.certificate 1621=true := by decide +kernel
noncomputable def cell2886 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2886.certificate 1621 accepted2886
theorem accepted2887 : minorantGammaCheck GammaPanel2887.certificate 1621=true := by decide +kernel
noncomputable def cell2887 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2887.certificate 1621 accepted2887
noncomputable def cells : List CertifiedMinorantCell := [cell2880, cell2881, cell2882, cell2883, cell2884, cell2885, cell2886, cell2887]
theorem chainAccepted : minorantChainCheck (3118/3125) (4989/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (3118/3125) (4989/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0360
