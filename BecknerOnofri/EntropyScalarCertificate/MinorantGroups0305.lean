module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0305

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0305
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2440 : minorantGammaCheck GammaPanel2440.certificate 1621=true := by decide +kernel
noncomputable def cell2440 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2440.certificate 1621 accepted2440
theorem accepted2441 : minorantGammaCheck GammaPanel2441.certificate 1621=true := by decide +kernel
noncomputable def cell2441 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2441.certificate 1621 accepted2441
theorem accepted2442 : minorantGammaCheck GammaPanel2442.certificate 1621=true := by decide +kernel
noncomputable def cell2442 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2442.certificate 1621 accepted2442
theorem accepted2443 : minorantGammaCheck GammaPanel2443.certificate 1621=true := by decide +kernel
noncomputable def cell2443 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2443.certificate 1621 accepted2443
theorem accepted2444 : minorantGammaCheck GammaPanel2444.certificate 1621=true := by decide +kernel
noncomputable def cell2444 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2444.certificate 1621 accepted2444
theorem accepted2445 : minorantGammaCheck GammaPanel2445.certificate 1621=true := by decide +kernel
noncomputable def cell2445 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2445.certificate 1621 accepted2445
theorem accepted2446 : minorantGammaCheck GammaPanel2446.certificate 1621=true := by decide +kernel
noncomputable def cell2446 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2446.certificate 1621 accepted2446
theorem accepted2447 : minorantGammaCheck GammaPanel2447.certificate 1621=true := by decide +kernel
noncomputable def cell2447 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2447.certificate 1621 accepted2447
noncomputable def cells : List CertifiedMinorantCell := [cell2440, cell2441, cell2442, cell2443, cell2444, cell2445, cell2446, cell2447]
theorem chainAccepted : minorantChainCheck (24781/25000) (4957/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24781/25000) (4957/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0305
