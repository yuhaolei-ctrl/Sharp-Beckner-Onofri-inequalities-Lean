module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0010

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0010
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0080 : minorantGammaCheck GammaPanel0080.certificate 40=true := by decide +kernel
noncomputable def cell0080 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0080.certificate 40 accepted0080
theorem accepted0081 : minorantGammaCheck GammaPanel0081.certificate 41=true := by decide +kernel
noncomputable def cell0081 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0081.certificate 41 accepted0081
theorem accepted0082 : minorantGammaCheck GammaPanel0082.certificate 42=true := by decide +kernel
noncomputable def cell0082 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0082.certificate 42 accepted0082
theorem accepted0083 : minorantGammaCheck GammaPanel0083.certificate 43=true := by decide +kernel
noncomputable def cell0083 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0083.certificate 43 accepted0083
theorem accepted0084 : minorantGammaCheck GammaPanel0084.certificate 44=true := by decide +kernel
noncomputable def cell0084 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0084.certificate 44 accepted0084
theorem accepted0085 : minorantGammaCheck GammaPanel0085.certificate 45=true := by decide +kernel
noncomputable def cell0085 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0085.certificate 45 accepted0085
theorem accepted0086 : minorantGammaCheck GammaPanel0086.certificate 46=true := by decide +kernel
noncomputable def cell0086 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0086.certificate 46 accepted0086
theorem accepted0087 : minorantGammaCheck GammaPanel0087.certificate 47=true := by decide +kernel
noncomputable def cell0087 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0087.certificate 47 accepted0087
noncomputable def cells : List CertifiedMinorantCell := [cell0080, cell0081, cell0082, cell0083, cell0084, cell0085, cell0086, cell0087]
theorem chainAccepted : minorantChainCheck (29/400) (741/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (29/400) (741/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0010
