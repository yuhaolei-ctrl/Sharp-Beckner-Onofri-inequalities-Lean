module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0082

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0082
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0656 : minorantGammaCheck GammaPanel0656.certificate 616=true := by decide +kernel
noncomputable def cell0656 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0656.certificate 616 accepted0656
theorem accepted0657 : minorantGammaCheck GammaPanel0657.certificate 616=true := by decide +kernel
noncomputable def cell0657 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0657.certificate 616 accepted0657
theorem accepted0658 : minorantGammaCheck GammaPanel0658.certificate 616=true := by decide +kernel
noncomputable def cell0658 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0658.certificate 616 accepted0658
theorem accepted0659 : minorantGammaCheck GammaPanel0659.certificate 616=true := by decide +kernel
noncomputable def cell0659 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0659.certificate 616 accepted0659
theorem accepted0660 : minorantGammaCheck GammaPanel0660.certificate 616=true := by decide +kernel
noncomputable def cell0660 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0660.certificate 616 accepted0660
theorem accepted0661 : minorantGammaCheck GammaPanel0661.certificate 616=true := by decide +kernel
noncomputable def cell0661 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0661.certificate 616 accepted0661
theorem accepted0662 : minorantGammaCheck GammaPanel0662.certificate 616=true := by decide +kernel
noncomputable def cell0662 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0662.certificate 616 accepted0662
theorem accepted0663 : minorantGammaCheck GammaPanel0663.certificate 616=true := by decide +kernel
noncomputable def cell0663 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0663.certificate 616 accepted0663
noncomputable def cells : List CertifiedMinorantCell := [cell0656, cell0657, cell0658, cell0659, cell0660, cell0661, cell0662, cell0663]
theorem chainAccepted : minorantChainCheck (1877/10000) (1893/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1877/10000) (1893/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0082
