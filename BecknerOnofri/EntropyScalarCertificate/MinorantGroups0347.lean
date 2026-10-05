import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0347
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0347
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2776 : minorantGammaCheck GammaPanel2776.certificate 1621=true := by decide +kernel
noncomputable def cell2776 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2776.certificate 1621 accepted2776
theorem accepted2777 : minorantGammaCheck GammaPanel2777.certificate 1621=true := by decide +kernel
noncomputable def cell2777 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2777.certificate 1621 accepted2777
theorem accepted2778 : minorantGammaCheck GammaPanel2778.certificate 1621=true := by decide +kernel
noncomputable def cell2778 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2778.certificate 1621 accepted2778
theorem accepted2779 : minorantGammaCheck GammaPanel2779.certificate 1621=true := by decide +kernel
noncomputable def cell2779 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2779.certificate 1621 accepted2779
theorem accepted2780 : minorantGammaCheck GammaPanel2780.certificate 1621=true := by decide +kernel
noncomputable def cell2780 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2780.certificate 1621 accepted2780
theorem accepted2781 : minorantGammaCheck GammaPanel2781.certificate 1621=true := by decide +kernel
noncomputable def cell2781 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2781.certificate 1621 accepted2781
theorem accepted2782 : minorantGammaCheck GammaPanel2782.certificate 1621=true := by decide +kernel
noncomputable def cell2782 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2782.certificate 1621 accepted2782
theorem accepted2783 : minorantGammaCheck GammaPanel2783.certificate 1621=true := by decide +kernel
noncomputable def cell2783 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2783.certificate 1621 accepted2783
noncomputable def cells : List CertifiedMinorantCell := [cell2776, cell2777, cell2778, cell2779, cell2780, cell2781, cell2782, cell2783]
theorem chainAccepted : minorantChainCheck (24931/25000) (6233/6250) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24931/25000) (6233/6250) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0347
