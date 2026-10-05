module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0088

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0088
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0704 : minorantGammaCheck GammaPanel0704.certificate 616=true := by decide +kernel
noncomputable def cell0704 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0704.certificate 616 accepted0704
theorem accepted0705 : minorantGammaCheck GammaPanel0705.certificate 616=true := by decide +kernel
noncomputable def cell0705 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0705.certificate 616 accepted0705
theorem accepted0706 : minorantGammaCheck GammaPanel0706.certificate 616=true := by decide +kernel
noncomputable def cell0706 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0706.certificate 616 accepted0706
theorem accepted0707 : minorantGammaCheck GammaPanel0707.certificate 616=true := by decide +kernel
noncomputable def cell0707 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0707.certificate 616 accepted0707
theorem accepted0708 : minorantGammaCheck GammaPanel0708.certificate 616=true := by decide +kernel
noncomputable def cell0708 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0708.certificate 616 accepted0708
theorem accepted0709 : minorantGammaCheck GammaPanel0709.certificate 616=true := by decide +kernel
noncomputable def cell0709 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0709.certificate 616 accepted0709
theorem accepted0710 : minorantGammaCheck GammaPanel0710.certificate 616=true := by decide +kernel
noncomputable def cell0710 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0710.certificate 616 accepted0710
theorem accepted0711 : minorantGammaCheck GammaPanel0711.certificate 616=true := by decide +kernel
noncomputable def cell0711 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0711.certificate 616 accepted0711
noncomputable def cells : List CertifiedMinorantCell := [cell0704, cell0705, cell0706, cell0707, cell0708, cell0709, cell0710, cell0711]
theorem chainAccepted : minorantChainCheck (1973/10000) (1989/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1973/10000) (1989/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0088
