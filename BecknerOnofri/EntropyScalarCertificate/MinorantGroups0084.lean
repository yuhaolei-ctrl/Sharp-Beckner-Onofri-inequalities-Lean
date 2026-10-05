module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0084

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0084
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0672 : minorantGammaCheck GammaPanel0672.certificate 616=true := by decide +kernel
noncomputable def cell0672 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0672.certificate 616 accepted0672
theorem accepted0673 : minorantGammaCheck GammaPanel0673.certificate 616=true := by decide +kernel
noncomputable def cell0673 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0673.certificate 616 accepted0673
theorem accepted0674 : minorantGammaCheck GammaPanel0674.certificate 616=true := by decide +kernel
noncomputable def cell0674 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0674.certificate 616 accepted0674
theorem accepted0675 : minorantGammaCheck GammaPanel0675.certificate 616=true := by decide +kernel
noncomputable def cell0675 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0675.certificate 616 accepted0675
theorem accepted0676 : minorantGammaCheck GammaPanel0676.certificate 616=true := by decide +kernel
noncomputable def cell0676 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0676.certificate 616 accepted0676
theorem accepted0677 : minorantGammaCheck GammaPanel0677.certificate 616=true := by decide +kernel
noncomputable def cell0677 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0677.certificate 616 accepted0677
theorem accepted0678 : minorantGammaCheck GammaPanel0678.certificate 616=true := by decide +kernel
noncomputable def cell0678 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0678.certificate 616 accepted0678
theorem accepted0679 : minorantGammaCheck GammaPanel0679.certificate 616=true := by decide +kernel
noncomputable def cell0679 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0679.certificate 616 accepted0679
noncomputable def cells : List CertifiedMinorantCell := [cell0672, cell0673, cell0674, cell0675, cell0676, cell0677, cell0678, cell0679]
theorem chainAccepted : minorantChainCheck (1909/10000) (77/400) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1909/10000) (77/400) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0084
