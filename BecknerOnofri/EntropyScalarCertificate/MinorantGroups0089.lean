module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0089

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0089
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0712 : minorantGammaCheck GammaPanel0712.certificate 616=true := by decide +kernel
noncomputable def cell0712 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0712.certificate 616 accepted0712
theorem accepted0713 : minorantGammaCheck GammaPanel0713.certificate 616=true := by decide +kernel
noncomputable def cell0713 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0713.certificate 616 accepted0713
theorem accepted0714 : minorantGammaCheck GammaPanel0714.certificate 616=true := by decide +kernel
noncomputable def cell0714 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0714.certificate 616 accepted0714
theorem accepted0715 : minorantGammaCheck GammaPanel0715.certificate 616=true := by decide +kernel
noncomputable def cell0715 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0715.certificate 616 accepted0715
theorem accepted0716 : minorantGammaCheck GammaPanel0716.certificate 616=true := by decide +kernel
noncomputable def cell0716 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0716.certificate 616 accepted0716
theorem accepted0717 : minorantGammaCheck GammaPanel0717.certificate 616=true := by decide +kernel
noncomputable def cell0717 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0717.certificate 616 accepted0717
theorem accepted0718 : minorantGammaCheck GammaPanel0718.certificate 616=true := by decide +kernel
noncomputable def cell0718 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0718.certificate 616 accepted0718
theorem accepted0719 : minorantGammaCheck GammaPanel0719.certificate 617=true := by decide +kernel
noncomputable def cell0719 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0719.certificate 617 accepted0719
noncomputable def cells : List CertifiedMinorantCell := [cell0712, cell0713, cell0714, cell0715, cell0716, cell0717, cell0718, cell0719]
theorem chainAccepted : minorantChainCheck (1989/10000) (101/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1989/10000) (101/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0089
