import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0363
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0363
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2904 : minorantGammaCheck GammaPanel2904.certificate 1621=true := by decide +kernel
noncomputable def cell2904 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2904.certificate 1621 accepted2904
theorem accepted2905 : minorantGammaCheck GammaPanel2905.certificate 1621=true := by decide +kernel
noncomputable def cell2905 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2905.certificate 1621 accepted2905
theorem accepted2906 : minorantGammaCheck GammaPanel2906.certificate 1621=true := by decide +kernel
noncomputable def cell2906 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2906.certificate 1621 accepted2906
theorem accepted2907 : minorantGammaCheck GammaPanel2907.certificate 1621=true := by decide +kernel
noncomputable def cell2907 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2907.certificate 1621 accepted2907
theorem accepted2908 : minorantGammaCheck GammaPanel2908.certificate 1621=true := by decide +kernel
noncomputable def cell2908 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2908.certificate 1621 accepted2908
theorem accepted2909 : minorantGammaCheck GammaPanel2909.certificate 1621=true := by decide +kernel
noncomputable def cell2909 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2909.certificate 1621 accepted2909
theorem accepted2910 : minorantGammaCheck GammaPanel2910.certificate 1621=true := by decide +kernel
noncomputable def cell2910 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2910.certificate 1621 accepted2910
theorem accepted2911 : minorantGammaCheck GammaPanel2911.certificate 1621=true := by decide +kernel
noncomputable def cell2911 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2911.certificate 1621 accepted2911
noncomputable def cells : List CertifiedMinorantCell := [cell2904, cell2905, cell2906, cell2907, cell2908, cell2909, cell2910, cell2911]
theorem chainAccepted : minorantChainCheck (24947/25000) (6237/6250) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24947/25000) (6237/6250) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0363
