module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0352

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0352
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2816 : minorantGammaCheck GammaPanel2816.certificate 1621=true := by decide +kernel
noncomputable def cell2816 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2816.certificate 1621 accepted2816
theorem accepted2817 : minorantGammaCheck GammaPanel2817.certificate 1621=true := by decide +kernel
noncomputable def cell2817 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2817.certificate 1621 accepted2817
theorem accepted2818 : minorantGammaCheck GammaPanel2818.certificate 1621=true := by decide +kernel
noncomputable def cell2818 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2818.certificate 1621 accepted2818
theorem accepted2819 : minorantGammaCheck GammaPanel2819.certificate 1621=true := by decide +kernel
noncomputable def cell2819 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2819.certificate 1621 accepted2819
theorem accepted2820 : minorantGammaCheck GammaPanel2820.certificate 1621=true := by decide +kernel
noncomputable def cell2820 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2820.certificate 1621 accepted2820
theorem accepted2821 : minorantGammaCheck GammaPanel2821.certificate 1621=true := by decide +kernel
noncomputable def cell2821 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2821.certificate 1621 accepted2821
theorem accepted2822 : minorantGammaCheck GammaPanel2822.certificate 1621=true := by decide +kernel
noncomputable def cell2822 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2822.certificate 1621 accepted2822
theorem accepted2823 : minorantGammaCheck GammaPanel2823.certificate 1621=true := by decide +kernel
noncomputable def cell2823 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2823.certificate 1621 accepted2823
noncomputable def cells : List CertifiedMinorantCell := [cell2816, cell2817, cell2818, cell2819, cell2820, cell2821, cell2822, cell2823]
theorem chainAccepted : minorantChainCheck (3117/3125) (24937/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (3117/3125) (24937/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0352
