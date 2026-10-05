module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0011

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0011
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0088 : minorantGammaCheck GammaPanel0088.certificate 48=true := by decide +kernel
noncomputable def cell0088 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0088.certificate 48 accepted0088
theorem accepted0089 : minorantGammaCheck GammaPanel0089.certificate 49=true := by decide +kernel
noncomputable def cell0089 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0089.certificate 49 accepted0089
theorem accepted0090 : minorantGammaCheck GammaPanel0090.certificate 50=true := by decide +kernel
noncomputable def cell0090 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0090.certificate 50 accepted0090
theorem accepted0091 : minorantGammaCheck GammaPanel0091.certificate 51=true := by decide +kernel
noncomputable def cell0091 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0091.certificate 51 accepted0091
theorem accepted0092 : minorantGammaCheck GammaPanel0092.certificate 52=true := by decide +kernel
noncomputable def cell0092 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0092.certificate 52 accepted0092
theorem accepted0093 : minorantGammaCheck GammaPanel0093.certificate 53=true := by decide +kernel
noncomputable def cell0093 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0093.certificate 53 accepted0093
theorem accepted0094 : minorantGammaCheck GammaPanel0094.certificate 54=true := by decide +kernel
noncomputable def cell0094 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0094.certificate 54 accepted0094
theorem accepted0095 : minorantGammaCheck GammaPanel0095.certificate 55=true := by decide +kernel
noncomputable def cell0095 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0095.certificate 55 accepted0095
noncomputable def cells : List CertifiedMinorantCell := [cell0088, cell0089, cell0090, cell0091, cell0092, cell0093, cell0094, cell0095]
theorem chainAccepted : minorantChainCheck (741/10000) (757/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (741/10000) (757/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0011
