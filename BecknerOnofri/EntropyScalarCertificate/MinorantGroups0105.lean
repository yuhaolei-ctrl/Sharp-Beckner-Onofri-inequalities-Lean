import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0105
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0105
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0840 : minorantGammaCheck GammaPanel0840.certificate 738=true := by decide +kernel
noncomputable def cell0840 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0840.certificate 738 accepted0840
theorem accepted0841 : minorantGammaCheck GammaPanel0841.certificate 739=true := by decide +kernel
noncomputable def cell0841 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0841.certificate 739 accepted0841
theorem accepted0842 : minorantGammaCheck GammaPanel0842.certificate 740=true := by decide +kernel
noncomputable def cell0842 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0842.certificate 740 accepted0842
theorem accepted0843 : minorantGammaCheck GammaPanel0843.certificate 741=true := by decide +kernel
noncomputable def cell0843 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0843.certificate 741 accepted0843
theorem accepted0844 : minorantGammaCheck GammaPanel0844.certificate 742=true := by decide +kernel
noncomputable def cell0844 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0844.certificate 742 accepted0844
theorem accepted0845 : minorantGammaCheck GammaPanel0845.certificate 743=true := by decide +kernel
noncomputable def cell0845 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0845.certificate 743 accepted0845
theorem accepted0846 : minorantGammaCheck GammaPanel0846.certificate 744=true := by decide +kernel
noncomputable def cell0846 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0846.certificate 744 accepted0846
theorem accepted0847 : minorantGammaCheck GammaPanel0847.certificate 745=true := by decide +kernel
noncomputable def cell0847 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0847.certificate 745 accepted0847
noncomputable def cells : List CertifiedMinorantCell := [cell0840, cell0841, cell0842, cell0843, cell0844, cell0845, cell0846, cell0847]
theorem chainAccepted : minorantChainCheck (161/500) (33/100) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (161/500) (33/100) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0105
