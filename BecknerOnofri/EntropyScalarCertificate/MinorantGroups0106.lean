module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0106

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0106
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0848 : minorantGammaCheck GammaPanel0848.certificate 746=true := by decide +kernel
noncomputable def cell0848 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0848.certificate 746 accepted0848
theorem accepted0849 : minorantGammaCheck GammaPanel0849.certificate 747=true := by decide +kernel
noncomputable def cell0849 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0849.certificate 747 accepted0849
theorem accepted0850 : minorantGammaCheck GammaPanel0850.certificate 748=true := by decide +kernel
noncomputable def cell0850 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0850.certificate 748 accepted0850
theorem accepted0851 : minorantGammaCheck GammaPanel0851.certificate 749=true := by decide +kernel
noncomputable def cell0851 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0851.certificate 749 accepted0851
theorem accepted0852 : minorantGammaCheck GammaPanel0852.certificate 750=true := by decide +kernel
noncomputable def cell0852 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0852.certificate 750 accepted0852
theorem accepted0853 : minorantGammaCheck GammaPanel0853.certificate 751=true := by decide +kernel
noncomputable def cell0853 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0853.certificate 751 accepted0853
theorem accepted0854 : minorantGammaCheck GammaPanel0854.certificate 752=true := by decide +kernel
noncomputable def cell0854 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0854.certificate 752 accepted0854
theorem accepted0855 : minorantGammaCheck GammaPanel0855.certificate 753=true := by decide +kernel
noncomputable def cell0855 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0855.certificate 753 accepted0855
noncomputable def cells : List CertifiedMinorantCell := [cell0848, cell0849, cell0850, cell0851, cell0852, cell0853, cell0854, cell0855]
theorem chainAccepted : minorantChainCheck (33/100) (169/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (33/100) (169/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0106
