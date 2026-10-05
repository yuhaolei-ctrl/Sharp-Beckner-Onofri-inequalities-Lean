module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0107

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0107
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0856 : minorantGammaCheck GammaPanel0856.certificate 754=true := by decide +kernel
noncomputable def cell0856 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0856.certificate 754 accepted0856
theorem accepted0857 : minorantGammaCheck GammaPanel0857.certificate 755=true := by decide +kernel
noncomputable def cell0857 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0857.certificate 755 accepted0857
theorem accepted0858 : minorantGammaCheck GammaPanel0858.certificate 756=true := by decide +kernel
noncomputable def cell0858 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0858.certificate 756 accepted0858
theorem accepted0859 : minorantGammaCheck GammaPanel0859.certificate 757=true := by decide +kernel
noncomputable def cell0859 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0859.certificate 757 accepted0859
theorem accepted0860 : minorantGammaCheck GammaPanel0860.certificate 758=true := by decide +kernel
noncomputable def cell0860 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0860.certificate 758 accepted0860
theorem accepted0861 : minorantGammaCheck GammaPanel0861.certificate 759=true := by decide +kernel
noncomputable def cell0861 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0861.certificate 759 accepted0861
theorem accepted0862 : minorantGammaCheck GammaPanel0862.certificate 760=true := by decide +kernel
noncomputable def cell0862 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0862.certificate 760 accepted0862
theorem accepted0863 : minorantGammaCheck GammaPanel0863.certificate 761=true := by decide +kernel
noncomputable def cell0863 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0863.certificate 761 accepted0863
noncomputable def cells : List CertifiedMinorantCell := [cell0856, cell0857, cell0858, cell0859, cell0860, cell0861, cell0862, cell0863]
theorem chainAccepted : minorantChainCheck (169/500) (173/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (169/500) (173/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0107
