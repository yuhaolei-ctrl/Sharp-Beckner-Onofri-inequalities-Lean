module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0004

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0004
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0032 : minorantGammaCheck GammaPanel0032.certificate 0=true := by decide +kernel
noncomputable def cell0032 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0032.certificate 0 accepted0032
theorem accepted0033 : minorantGammaCheck GammaPanel0033.certificate 0=true := by decide +kernel
noncomputable def cell0033 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0033.certificate 0 accepted0033
theorem accepted0034 : minorantGammaCheck GammaPanel0034.certificate 0=true := by decide +kernel
noncomputable def cell0034 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0034.certificate 0 accepted0034
theorem accepted0035 : minorantGammaCheck GammaPanel0035.certificate 0=true := by decide +kernel
noncomputable def cell0035 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0035.certificate 0 accepted0035
theorem accepted0036 : minorantGammaCheck GammaPanel0036.certificate 0=true := by decide +kernel
noncomputable def cell0036 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0036.certificate 0 accepted0036
theorem accepted0037 : minorantGammaCheck GammaPanel0037.certificate 0=true := by decide +kernel
noncomputable def cell0037 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0037.certificate 0 accepted0037
theorem accepted0038 : minorantGammaCheck GammaPanel0038.certificate 0=true := by decide +kernel
noncomputable def cell0038 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0038.certificate 0 accepted0038
theorem accepted0039 : minorantGammaCheck GammaPanel0039.certificate 0=true := by decide +kernel
noncomputable def cell0039 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0039.certificate 0 accepted0039
noncomputable def cells : List CertifiedMinorantCell := [cell0032, cell0033, cell0034, cell0035, cell0036, cell0037, cell0038, cell0039]
theorem chainAccepted : minorantChainCheck (641/10000) (129/2000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (641/10000) (129/2000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0004
