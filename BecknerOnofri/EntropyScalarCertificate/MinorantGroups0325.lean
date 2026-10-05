module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0325

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0325
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2600 : minorantGammaCheck GammaPanel2600.certificate 1621=true := by decide +kernel
noncomputable def cell2600 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2600.certificate 1621 accepted2600
theorem accepted2601 : minorantGammaCheck GammaPanel2601.certificate 1621=true := by decide +kernel
noncomputable def cell2601 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2601.certificate 1621 accepted2601
theorem accepted2602 : minorantGammaCheck GammaPanel2602.certificate 1621=true := by decide +kernel
noncomputable def cell2602 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2602.certificate 1621 accepted2602
theorem accepted2603 : minorantGammaCheck GammaPanel2603.certificate 1621=true := by decide +kernel
noncomputable def cell2603 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2603.certificate 1621 accepted2603
theorem accepted2604 : minorantGammaCheck GammaPanel2604.certificate 1621=true := by decide +kernel
noncomputable def cell2604 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2604.certificate 1621 accepted2604
theorem accepted2605 : minorantGammaCheck GammaPanel2605.certificate 1621=true := by decide +kernel
noncomputable def cell2605 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2605.certificate 1621 accepted2605
theorem accepted2606 : minorantGammaCheck GammaPanel2606.certificate 1621=true := by decide +kernel
noncomputable def cell2606 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2606.certificate 1621 accepted2606
theorem accepted2607 : minorantGammaCheck GammaPanel2607.certificate 1621=true := by decide +kernel
noncomputable def cell2607 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2607.certificate 1621 accepted2607
noncomputable def cells : List CertifiedMinorantCell := [cell2600, cell2601, cell2602, cell2603, cell2604, cell2605, cell2606, cell2607]
theorem chainAccepted : minorantChainCheck (24861/25000) (4973/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24861/25000) (4973/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0325
