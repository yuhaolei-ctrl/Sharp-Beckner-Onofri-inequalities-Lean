module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0386

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0386
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted3088 : minorantGammaCheck GammaPanel3088.certificate 1621=true := by decide +kernel
noncomputable def cell3088 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3088.certificate 1621 accepted3088
theorem accepted3089 : minorantGammaCheck GammaPanel3089.certificate 1621=true := by decide +kernel
noncomputable def cell3089 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3089.certificate 1621 accepted3089
theorem accepted3090 : minorantGammaCheck GammaPanel3090.certificate 1621=true := by decide +kernel
noncomputable def cell3090 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3090.certificate 1621 accepted3090
theorem accepted3091 : minorantGammaCheck GammaPanel3091.certificate 1621=true := by decide +kernel
noncomputable def cell3091 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3091.certificate 1621 accepted3091
theorem accepted3092 : minorantGammaCheck GammaPanel3092.certificate 1621=true := by decide +kernel
noncomputable def cell3092 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3092.certificate 1621 accepted3092
theorem accepted3093 : minorantGammaCheck GammaPanel3093.certificate 1621=true := by decide +kernel
noncomputable def cell3093 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3093.certificate 1621 accepted3093
theorem accepted3094 : minorantGammaCheck GammaPanel3094.certificate 1621=true := by decide +kernel
noncomputable def cell3094 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3094.certificate 1621 accepted3094
theorem accepted3095 : minorantGammaCheck GammaPanel3095.certificate 1621=true := by decide +kernel
noncomputable def cell3095 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3095.certificate 1621 accepted3095
noncomputable def cells : List CertifiedMinorantCell := [cell3088, cell3089, cell3090, cell3091, cell3092, cell3093, cell3094, cell3095]
theorem chainAccepted : minorantChainCheck (2497/2500) (24971/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (2497/2500) (24971/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0386
