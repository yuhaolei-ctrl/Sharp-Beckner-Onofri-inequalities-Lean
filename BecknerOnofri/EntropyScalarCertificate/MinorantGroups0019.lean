module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0019

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0019
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0152 : minorantGammaCheck GammaPanel0152.certificate 112=true := by decide +kernel
noncomputable def cell0152 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0152.certificate 112 accepted0152
theorem accepted0153 : minorantGammaCheck GammaPanel0153.certificate 113=true := by decide +kernel
noncomputable def cell0153 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0153.certificate 113 accepted0153
theorem accepted0154 : minorantGammaCheck GammaPanel0154.certificate 114=true := by decide +kernel
noncomputable def cell0154 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0154.certificate 114 accepted0154
theorem accepted0155 : minorantGammaCheck GammaPanel0155.certificate 115=true := by decide +kernel
noncomputable def cell0155 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0155.certificate 115 accepted0155
theorem accepted0156 : minorantGammaCheck GammaPanel0156.certificate 116=true := by decide +kernel
noncomputable def cell0156 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0156.certificate 116 accepted0156
theorem accepted0157 : minorantGammaCheck GammaPanel0157.certificate 117=true := by decide +kernel
noncomputable def cell0157 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0157.certificate 117 accepted0157
theorem accepted0158 : minorantGammaCheck GammaPanel0158.certificate 118=true := by decide +kernel
noncomputable def cell0158 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0158.certificate 118 accepted0158
theorem accepted0159 : minorantGammaCheck GammaPanel0159.certificate 119=true := by decide +kernel
noncomputable def cell0159 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0159.certificate 119 accepted0159
noncomputable def cells : List CertifiedMinorantCell := [cell0152, cell0153, cell0154, cell0155, cell0156, cell0157, cell0158, cell0159]
theorem chainAccepted : minorantChainCheck (869/10000) (177/2000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (869/10000) (177/2000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0019
