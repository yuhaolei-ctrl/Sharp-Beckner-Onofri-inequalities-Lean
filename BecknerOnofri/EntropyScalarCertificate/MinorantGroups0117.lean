import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0117
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0117
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0936 : minorantGammaCheck GammaPanel0936.certificate 834=true := by decide +kernel
noncomputable def cell0936 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0936.certificate 834 accepted0936
theorem accepted0937 : minorantGammaCheck GammaPanel0937.certificate 835=true := by decide +kernel
noncomputable def cell0937 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0937.certificate 835 accepted0937
theorem accepted0938 : minorantGammaCheck GammaPanel0938.certificate 836=true := by decide +kernel
noncomputable def cell0938 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0938.certificate 836 accepted0938
theorem accepted0939 : minorantGammaCheck GammaPanel0939.certificate 837=true := by decide +kernel
noncomputable def cell0939 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0939.certificate 837 accepted0939
theorem accepted0940 : minorantGammaCheck GammaPanel0940.certificate 838=true := by decide +kernel
noncomputable def cell0940 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0940.certificate 838 accepted0940
theorem accepted0941 : minorantGammaCheck GammaPanel0941.certificate 839=true := by decide +kernel
noncomputable def cell0941 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0941.certificate 839 accepted0941
theorem accepted0942 : minorantGammaCheck GammaPanel0942.certificate 840=true := by decide +kernel
noncomputable def cell0942 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0942.certificate 840 accepted0942
theorem accepted0943 : minorantGammaCheck GammaPanel0943.certificate 841=true := by decide +kernel
noncomputable def cell0943 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0943.certificate 841 accepted0943
noncomputable def cells : List CertifiedMinorantCell := [cell0936, cell0937, cell0938, cell0939, cell0940, cell0941, cell0942, cell0943]
theorem chainAccepted : minorantChainCheck (209/500) (213/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (209/500) (213/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0117
