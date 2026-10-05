module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0377

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0377
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted3016 : minorantGammaCheck GammaPanel3016.certificate 1621=true := by decide +kernel
noncomputable def cell3016 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3016.certificate 1621 accepted3016
theorem accepted3017 : minorantGammaCheck GammaPanel3017.certificate 1621=true := by decide +kernel
noncomputable def cell3017 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3017.certificate 1621 accepted3017
theorem accepted3018 : minorantGammaCheck GammaPanel3018.certificate 1621=true := by decide +kernel
noncomputable def cell3018 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3018.certificate 1621 accepted3018
theorem accepted3019 : minorantGammaCheck GammaPanel3019.certificate 1621=true := by decide +kernel
noncomputable def cell3019 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3019.certificate 1621 accepted3019
theorem accepted3020 : minorantGammaCheck GammaPanel3020.certificate 1621=true := by decide +kernel
noncomputable def cell3020 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3020.certificate 1621 accepted3020
theorem accepted3021 : minorantGammaCheck GammaPanel3021.certificate 1621=true := by decide +kernel
noncomputable def cell3021 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3021.certificate 1621 accepted3021
theorem accepted3022 : minorantGammaCheck GammaPanel3022.certificate 1621=true := by decide +kernel
noncomputable def cell3022 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3022.certificate 1621 accepted3022
theorem accepted3023 : minorantGammaCheck GammaPanel3023.certificate 1621=true := by decide +kernel
noncomputable def cell3023 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3023.certificate 1621 accepted3023
noncomputable def cells : List CertifiedMinorantCell := [cell3016, cell3017, cell3018, cell3019, cell3020, cell3021, cell3022, cell3023]
theorem chainAccepted : minorantChainCheck (24961/25000) (12481/12500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24961/25000) (12481/12500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0377
