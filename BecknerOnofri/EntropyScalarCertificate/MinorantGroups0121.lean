import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0121
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0121
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0968 : minorantGammaCheck GammaPanel0968.certificate 866=true := by decide +kernel
noncomputable def cell0968 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0968.certificate 866 accepted0968
theorem accepted0969 : minorantGammaCheck GammaPanel0969.certificate 867=true := by decide +kernel
noncomputable def cell0969 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0969.certificate 867 accepted0969
theorem accepted0970 : minorantGammaCheck GammaPanel0970.certificate 868=true := by decide +kernel
noncomputable def cell0970 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0970.certificate 868 accepted0970
theorem accepted0971 : minorantGammaCheck GammaPanel0971.certificate 869=true := by decide +kernel
noncomputable def cell0971 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0971.certificate 869 accepted0971
theorem accepted0972 : minorantGammaCheck GammaPanel0972.certificate 870=true := by decide +kernel
noncomputable def cell0972 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0972.certificate 870 accepted0972
theorem accepted0973 : minorantGammaCheck GammaPanel0973.certificate 871=true := by decide +kernel
noncomputable def cell0973 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0973.certificate 871 accepted0973
theorem accepted0974 : minorantGammaCheck GammaPanel0974.certificate 872=true := by decide +kernel
noncomputable def cell0974 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0974.certificate 872 accepted0974
theorem accepted0975 : minorantGammaCheck GammaPanel0975.certificate 873=true := by decide +kernel
noncomputable def cell0975 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0975.certificate 873 accepted0975
noncomputable def cells : List CertifiedMinorantCell := [cell0968, cell0969, cell0970, cell0971, cell0972, cell0973, cell0974, cell0975]
theorem chainAccepted : minorantChainCheck (9/20) (229/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (9/20) (229/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0121
