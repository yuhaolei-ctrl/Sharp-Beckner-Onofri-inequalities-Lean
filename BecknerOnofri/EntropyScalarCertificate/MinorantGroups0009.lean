import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0009
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0009
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0072 : minorantGammaCheck GammaPanel0072.certificate 32=true := by decide +kernel
noncomputable def cell0072 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0072.certificate 32 accepted0072
theorem accepted0073 : minorantGammaCheck GammaPanel0073.certificate 33=true := by decide +kernel
noncomputable def cell0073 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0073.certificate 33 accepted0073
theorem accepted0074 : minorantGammaCheck GammaPanel0074.certificate 34=true := by decide +kernel
noncomputable def cell0074 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0074.certificate 34 accepted0074
theorem accepted0075 : minorantGammaCheck GammaPanel0075.certificate 35=true := by decide +kernel
noncomputable def cell0075 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0075.certificate 35 accepted0075
theorem accepted0076 : minorantGammaCheck GammaPanel0076.certificate 36=true := by decide +kernel
noncomputable def cell0076 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0076.certificate 36 accepted0076
theorem accepted0077 : minorantGammaCheck GammaPanel0077.certificate 37=true := by decide +kernel
noncomputable def cell0077 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0077.certificate 37 accepted0077
theorem accepted0078 : minorantGammaCheck GammaPanel0078.certificate 38=true := by decide +kernel
noncomputable def cell0078 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0078.certificate 38 accepted0078
theorem accepted0079 : minorantGammaCheck GammaPanel0079.certificate 39=true := by decide +kernel
noncomputable def cell0079 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0079.certificate 39 accepted0079
noncomputable def cells : List CertifiedMinorantCell := [cell0072, cell0073, cell0074, cell0075, cell0076, cell0077, cell0078, cell0079]
theorem chainAccepted : minorantChainCheck (709/10000) (29/400) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (709/10000) (29/400) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0009
