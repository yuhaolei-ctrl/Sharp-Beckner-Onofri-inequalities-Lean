module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0351

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0351
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2808 : minorantGammaCheck GammaPanel2808.certificate 1621=true := by decide +kernel
noncomputable def cell2808 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2808.certificate 1621 accepted2808
theorem accepted2809 : minorantGammaCheck GammaPanel2809.certificate 1621=true := by decide +kernel
noncomputable def cell2809 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2809.certificate 1621 accepted2809
theorem accepted2810 : minorantGammaCheck GammaPanel2810.certificate 1621=true := by decide +kernel
noncomputable def cell2810 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2810.certificate 1621 accepted2810
theorem accepted2811 : minorantGammaCheck GammaPanel2811.certificate 1621=true := by decide +kernel
noncomputable def cell2811 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2811.certificate 1621 accepted2811
theorem accepted2812 : minorantGammaCheck GammaPanel2812.certificate 1621=true := by decide +kernel
noncomputable def cell2812 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2812.certificate 1621 accepted2812
theorem accepted2813 : minorantGammaCheck GammaPanel2813.certificate 1621=true := by decide +kernel
noncomputable def cell2813 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2813.certificate 1621 accepted2813
theorem accepted2814 : minorantGammaCheck GammaPanel2814.certificate 1621=true := by decide +kernel
noncomputable def cell2814 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2814.certificate 1621 accepted2814
theorem accepted2815 : minorantGammaCheck GammaPanel2815.certificate 1621=true := by decide +kernel
noncomputable def cell2815 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2815.certificate 1621 accepted2815
noncomputable def cells : List CertifiedMinorantCell := [cell2808, cell2809, cell2810, cell2811, cell2812, cell2813, cell2814, cell2815]
theorem chainAccepted : minorantChainCheck (4987/5000) (3117/3125) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4987/5000) (3117/3125) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0351
