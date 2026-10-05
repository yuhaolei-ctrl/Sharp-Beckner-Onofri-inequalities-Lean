module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0338

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0338
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2704 : minorantGammaCheck GammaPanel2704.certificate 1621=true := by decide +kernel
noncomputable def cell2704 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2704.certificate 1621 accepted2704
theorem accepted2705 : minorantGammaCheck GammaPanel2705.certificate 1621=true := by decide +kernel
noncomputable def cell2705 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2705.certificate 1621 accepted2705
theorem accepted2706 : minorantGammaCheck GammaPanel2706.certificate 1621=true := by decide +kernel
noncomputable def cell2706 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2706.certificate 1621 accepted2706
theorem accepted2707 : minorantGammaCheck GammaPanel2707.certificate 1621=true := by decide +kernel
noncomputable def cell2707 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2707.certificate 1621 accepted2707
theorem accepted2708 : minorantGammaCheck GammaPanel2708.certificate 1621=true := by decide +kernel
noncomputable def cell2708 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2708.certificate 1621 accepted2708
theorem accepted2709 : minorantGammaCheck GammaPanel2709.certificate 1621=true := by decide +kernel
noncomputable def cell2709 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2709.certificate 1621 accepted2709
theorem accepted2710 : minorantGammaCheck GammaPanel2710.certificate 1621=true := by decide +kernel
noncomputable def cell2710 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2710.certificate 1621 accepted2710
theorem accepted2711 : minorantGammaCheck GammaPanel2711.certificate 1621=true := by decide +kernel
noncomputable def cell2711 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2711.certificate 1621 accepted2711
noncomputable def cells : List CertifiedMinorantCell := [cell2704, cell2705, cell2706, cell2707, cell2708, cell2709, cell2710, cell2711]
theorem chainAccepted : minorantChainCheck (24913/25000) (24917/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24913/25000) (24917/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0338
