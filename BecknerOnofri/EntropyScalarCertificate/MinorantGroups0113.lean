module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0113

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0113
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0904 : minorantGammaCheck GammaPanel0904.certificate 802=true := by decide +kernel
noncomputable def cell0904 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0904.certificate 802 accepted0904
theorem accepted0905 : minorantGammaCheck GammaPanel0905.certificate 803=true := by decide +kernel
noncomputable def cell0905 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0905.certificate 803 accepted0905
theorem accepted0906 : minorantGammaCheck GammaPanel0906.certificate 804=true := by decide +kernel
noncomputable def cell0906 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0906.certificate 804 accepted0906
theorem accepted0907 : minorantGammaCheck GammaPanel0907.certificate 805=true := by decide +kernel
noncomputable def cell0907 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0907.certificate 805 accepted0907
theorem accepted0908 : minorantGammaCheck GammaPanel0908.certificate 806=true := by decide +kernel
noncomputable def cell0908 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0908.certificate 806 accepted0908
theorem accepted0909 : minorantGammaCheck GammaPanel0909.certificate 807=true := by decide +kernel
noncomputable def cell0909 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0909.certificate 807 accepted0909
theorem accepted0910 : minorantGammaCheck GammaPanel0910.certificate 808=true := by decide +kernel
noncomputable def cell0910 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0910.certificate 808 accepted0910
theorem accepted0911 : minorantGammaCheck GammaPanel0911.certificate 809=true := by decide +kernel
noncomputable def cell0911 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0911.certificate 809 accepted0911
noncomputable def cells : List CertifiedMinorantCell := [cell0904, cell0905, cell0906, cell0907, cell0908, cell0909, cell0910, cell0911]
theorem chainAccepted : minorantChainCheck (193/500) (197/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (193/500) (197/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0113
