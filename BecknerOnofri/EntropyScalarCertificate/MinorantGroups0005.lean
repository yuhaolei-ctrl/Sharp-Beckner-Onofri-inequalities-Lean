module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0005

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0005
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0040 : minorantGammaCheck GammaPanel0040.certificate 0=true := by decide +kernel
noncomputable def cell0040 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0040.certificate 0 accepted0040
theorem accepted0041 : minorantGammaCheck GammaPanel0041.certificate 1=true := by decide +kernel
noncomputable def cell0041 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0041.certificate 1 accepted0041
theorem accepted0042 : minorantGammaCheck GammaPanel0042.certificate 2=true := by decide +kernel
noncomputable def cell0042 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0042.certificate 2 accepted0042
theorem accepted0043 : minorantGammaCheck GammaPanel0043.certificate 3=true := by decide +kernel
noncomputable def cell0043 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0043.certificate 3 accepted0043
theorem accepted0044 : minorantGammaCheck GammaPanel0044.certificate 4=true := by decide +kernel
noncomputable def cell0044 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0044.certificate 4 accepted0044
theorem accepted0045 : minorantGammaCheck GammaPanel0045.certificate 5=true := by decide +kernel
noncomputable def cell0045 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0045.certificate 5 accepted0045
theorem accepted0046 : minorantGammaCheck GammaPanel0046.certificate 6=true := by decide +kernel
noncomputable def cell0046 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0046.certificate 6 accepted0046
theorem accepted0047 : minorantGammaCheck GammaPanel0047.certificate 7=true := by decide +kernel
noncomputable def cell0047 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0047.certificate 7 accepted0047
noncomputable def cells : List CertifiedMinorantCell := [cell0040, cell0041, cell0042, cell0043, cell0044, cell0045, cell0046, cell0047]
theorem chainAccepted : minorantChainCheck (129/2000) (661/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (129/2000) (661/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0005
