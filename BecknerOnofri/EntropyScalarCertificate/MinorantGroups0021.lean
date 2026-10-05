module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0021

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0021
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0168 : minorantGammaCheck GammaPanel0168.certificate 128=true := by decide +kernel
noncomputable def cell0168 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0168.certificate 128 accepted0168
theorem accepted0169 : minorantGammaCheck GammaPanel0169.certificate 129=true := by decide +kernel
noncomputable def cell0169 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0169.certificate 129 accepted0169
theorem accepted0170 : minorantGammaCheck GammaPanel0170.certificate 130=true := by decide +kernel
noncomputable def cell0170 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0170.certificate 130 accepted0170
theorem accepted0171 : minorantGammaCheck GammaPanel0171.certificate 131=true := by decide +kernel
noncomputable def cell0171 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0171.certificate 131 accepted0171
theorem accepted0172 : minorantGammaCheck GammaPanel0172.certificate 132=true := by decide +kernel
noncomputable def cell0172 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0172.certificate 132 accepted0172
theorem accepted0173 : minorantGammaCheck GammaPanel0173.certificate 133=true := by decide +kernel
noncomputable def cell0173 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0173.certificate 133 accepted0173
theorem accepted0174 : minorantGammaCheck GammaPanel0174.certificate 134=true := by decide +kernel
noncomputable def cell0174 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0174.certificate 134 accepted0174
theorem accepted0175 : minorantGammaCheck GammaPanel0175.certificate 135=true := by decide +kernel
noncomputable def cell0175 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0175.certificate 135 accepted0175
noncomputable def cells : List CertifiedMinorantCell := [cell0168, cell0169, cell0170, cell0171, cell0172, cell0173, cell0174, cell0175]
theorem chainAccepted : minorantChainCheck (901/10000) (917/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (901/10000) (917/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0021
