import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0006
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0006
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0048 : minorantGammaCheck GammaPanel0048.certificate 8=true := by decide +kernel
noncomputable def cell0048 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0048.certificate 8 accepted0048
theorem accepted0049 : minorantGammaCheck GammaPanel0049.certificate 9=true := by decide +kernel
noncomputable def cell0049 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0049.certificate 9 accepted0049
theorem accepted0050 : minorantGammaCheck GammaPanel0050.certificate 10=true := by decide +kernel
noncomputable def cell0050 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0050.certificate 10 accepted0050
theorem accepted0051 : minorantGammaCheck GammaPanel0051.certificate 11=true := by decide +kernel
noncomputable def cell0051 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0051.certificate 11 accepted0051
theorem accepted0052 : minorantGammaCheck GammaPanel0052.certificate 12=true := by decide +kernel
noncomputable def cell0052 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0052.certificate 12 accepted0052
theorem accepted0053 : minorantGammaCheck GammaPanel0053.certificate 13=true := by decide +kernel
noncomputable def cell0053 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0053.certificate 13 accepted0053
theorem accepted0054 : minorantGammaCheck GammaPanel0054.certificate 14=true := by decide +kernel
noncomputable def cell0054 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0054.certificate 14 accepted0054
theorem accepted0055 : minorantGammaCheck GammaPanel0055.certificate 15=true := by decide +kernel
noncomputable def cell0055 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0055.certificate 15 accepted0055
noncomputable def cells : List CertifiedMinorantCell := [cell0048, cell0049, cell0050, cell0051, cell0052, cell0053, cell0054, cell0055]
theorem chainAccepted : minorantChainCheck (661/10000) (677/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (661/10000) (677/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0006
