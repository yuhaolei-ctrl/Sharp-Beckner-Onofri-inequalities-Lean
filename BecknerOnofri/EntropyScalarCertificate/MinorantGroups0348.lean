module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0348

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0348
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2784 : minorantGammaCheck GammaPanel2784.certificate 1621=true := by decide +kernel
noncomputable def cell2784 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2784.certificate 1621 accepted2784
theorem accepted2785 : minorantGammaCheck GammaPanel2785.certificate 1621=true := by decide +kernel
noncomputable def cell2785 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2785.certificate 1621 accepted2785
theorem accepted2786 : minorantGammaCheck GammaPanel2786.certificate 1621=true := by decide +kernel
noncomputable def cell2786 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2786.certificate 1621 accepted2786
theorem accepted2787 : minorantGammaCheck GammaPanel2787.certificate 1621=true := by decide +kernel
noncomputable def cell2787 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2787.certificate 1621 accepted2787
theorem accepted2788 : minorantGammaCheck GammaPanel2788.certificate 1621=true := by decide +kernel
noncomputable def cell2788 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2788.certificate 1621 accepted2788
theorem accepted2789 : minorantGammaCheck GammaPanel2789.certificate 1621=true := by decide +kernel
noncomputable def cell2789 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2789.certificate 1621 accepted2789
theorem accepted2790 : minorantGammaCheck GammaPanel2790.certificate 1621=true := by decide +kernel
noncomputable def cell2790 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2790.certificate 1621 accepted2790
theorem accepted2791 : minorantGammaCheck GammaPanel2791.certificate 1621=true := by decide +kernel
noncomputable def cell2791 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2791.certificate 1621 accepted2791
noncomputable def cells : List CertifiedMinorantCell := [cell2784, cell2785, cell2786, cell2787, cell2788, cell2789, cell2790, cell2791]
theorem chainAccepted : minorantChainCheck (6233/6250) (24933/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (6233/6250) (24933/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0348
