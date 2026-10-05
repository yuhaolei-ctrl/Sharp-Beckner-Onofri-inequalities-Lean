module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0383

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0383
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted3064 : minorantGammaCheck GammaPanel3064.certificate 1621=true := by decide +kernel
noncomputable def cell3064 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3064.certificate 1621 accepted3064
theorem accepted3065 : minorantGammaCheck GammaPanel3065.certificate 1621=true := by decide +kernel
noncomputable def cell3065 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3065.certificate 1621 accepted3065
theorem accepted3066 : minorantGammaCheck GammaPanel3066.certificate 1621=true := by decide +kernel
noncomputable def cell3066 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3066.certificate 1621 accepted3066
theorem accepted3067 : minorantGammaCheck GammaPanel3067.certificate 1621=true := by decide +kernel
noncomputable def cell3067 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3067.certificate 1621 accepted3067
theorem accepted3068 : minorantGammaCheck GammaPanel3068.certificate 1621=true := by decide +kernel
noncomputable def cell3068 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3068.certificate 1621 accepted3068
theorem accepted3069 : minorantGammaCheck GammaPanel3069.certificate 1621=true := by decide +kernel
noncomputable def cell3069 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3069.certificate 1621 accepted3069
theorem accepted3070 : minorantGammaCheck GammaPanel3070.certificate 1621=true := by decide +kernel
noncomputable def cell3070 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3070.certificate 1621 accepted3070
theorem accepted3071 : minorantGammaCheck GammaPanel3071.certificate 1621=true := by decide +kernel
noncomputable def cell3071 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3071.certificate 1621 accepted3071
noncomputable def cells : List CertifiedMinorantCell := [cell3064, cell3065, cell3066, cell3067, cell3068, cell3069, cell3070, cell3071]
theorem chainAccepted : minorantChainCheck (24967/25000) (3121/3125) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24967/25000) (3121/3125) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0383
