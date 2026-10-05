module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0102

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0102
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0816 : minorantGammaCheck GammaPanel0816.certificate 714=true := by decide +kernel
noncomputable def cell0816 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0816.certificate 714 accepted0816
theorem accepted0817 : minorantGammaCheck GammaPanel0817.certificate 715=true := by decide +kernel
noncomputable def cell0817 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0817.certificate 715 accepted0817
theorem accepted0818 : minorantGammaCheck GammaPanel0818.certificate 716=true := by decide +kernel
noncomputable def cell0818 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0818.certificate 716 accepted0818
theorem accepted0819 : minorantGammaCheck GammaPanel0819.certificate 717=true := by decide +kernel
noncomputable def cell0819 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0819.certificate 717 accepted0819
theorem accepted0820 : minorantGammaCheck GammaPanel0820.certificate 718=true := by decide +kernel
noncomputable def cell0820 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0820.certificate 718 accepted0820
theorem accepted0821 : minorantGammaCheck GammaPanel0821.certificate 719=true := by decide +kernel
noncomputable def cell0821 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0821.certificate 719 accepted0821
theorem accepted0822 : minorantGammaCheck GammaPanel0822.certificate 720=true := by decide +kernel
noncomputable def cell0822 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0822.certificate 720 accepted0822
theorem accepted0823 : minorantGammaCheck GammaPanel0823.certificate 721=true := by decide +kernel
noncomputable def cell0823 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0823.certificate 721 accepted0823
noncomputable def cells : List CertifiedMinorantCell := [cell0816, cell0817, cell0818, cell0819, cell0820, cell0821, cell0822, cell0823]
theorem chainAccepted : minorantChainCheck (149/500) (153/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (149/500) (153/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0102
