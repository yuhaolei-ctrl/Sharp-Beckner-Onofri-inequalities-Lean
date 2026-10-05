module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0320

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0320
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2560 : minorantGammaCheck GammaPanel2560.certificate 1621=true := by decide +kernel
noncomputable def cell2560 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2560.certificate 1621 accepted2560
theorem accepted2561 : minorantGammaCheck GammaPanel2561.certificate 1621=true := by decide +kernel
noncomputable def cell2561 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2561.certificate 1621 accepted2561
theorem accepted2562 : minorantGammaCheck GammaPanel2562.certificate 1621=true := by decide +kernel
noncomputable def cell2562 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2562.certificate 1621 accepted2562
theorem accepted2563 : minorantGammaCheck GammaPanel2563.certificate 1621=true := by decide +kernel
noncomputable def cell2563 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2563.certificate 1621 accepted2563
theorem accepted2564 : minorantGammaCheck GammaPanel2564.certificate 1621=true := by decide +kernel
noncomputable def cell2564 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2564.certificate 1621 accepted2564
theorem accepted2565 : minorantGammaCheck GammaPanel2565.certificate 1621=true := by decide +kernel
noncomputable def cell2565 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2565.certificate 1621 accepted2565
theorem accepted2566 : minorantGammaCheck GammaPanel2566.certificate 1621=true := by decide +kernel
noncomputable def cell2566 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2566.certificate 1621 accepted2566
theorem accepted2567 : minorantGammaCheck GammaPanel2567.certificate 1621=true := by decide +kernel
noncomputable def cell2567 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2567.certificate 1621 accepted2567
noncomputable def cells : List CertifiedMinorantCell := [cell2560, cell2561, cell2562, cell2563, cell2564, cell2565, cell2566, cell2567]
theorem chainAccepted : minorantChainCheck (24841/25000) (4969/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24841/25000) (4969/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0320
