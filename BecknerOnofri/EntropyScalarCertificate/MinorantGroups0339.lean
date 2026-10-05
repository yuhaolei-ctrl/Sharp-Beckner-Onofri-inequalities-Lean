module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0339

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0339
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2712 : minorantGammaCheck GammaPanel2712.certificate 1621=true := by decide +kernel
noncomputable def cell2712 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2712.certificate 1621 accepted2712
theorem accepted2713 : minorantGammaCheck GammaPanel2713.certificate 1621=true := by decide +kernel
noncomputable def cell2713 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2713.certificate 1621 accepted2713
theorem accepted2714 : minorantGammaCheck GammaPanel2714.certificate 1621=true := by decide +kernel
noncomputable def cell2714 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2714.certificate 1621 accepted2714
theorem accepted2715 : minorantGammaCheck GammaPanel2715.certificate 1621=true := by decide +kernel
noncomputable def cell2715 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2715.certificate 1621 accepted2715
theorem accepted2716 : minorantGammaCheck GammaPanel2716.certificate 1621=true := by decide +kernel
noncomputable def cell2716 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2716.certificate 1621 accepted2716
theorem accepted2717 : minorantGammaCheck GammaPanel2717.certificate 1621=true := by decide +kernel
noncomputable def cell2717 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2717.certificate 1621 accepted2717
theorem accepted2718 : minorantGammaCheck GammaPanel2718.certificate 1621=true := by decide +kernel
noncomputable def cell2718 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2718.certificate 1621 accepted2718
theorem accepted2719 : minorantGammaCheck GammaPanel2719.certificate 1621=true := by decide +kernel
noncomputable def cell2719 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2719.certificate 1621 accepted2719
noncomputable def cells : List CertifiedMinorantCell := [cell2712, cell2713, cell2714, cell2715, cell2716, cell2717, cell2718, cell2719]
theorem chainAccepted : minorantChainCheck (24917/25000) (24921/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24917/25000) (24921/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0339
