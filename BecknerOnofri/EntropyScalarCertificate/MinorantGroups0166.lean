module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0166

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0166
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1328 : minorantGammaCheck GammaPanel1328.certificate 1216=true := by decide +kernel
noncomputable def cell1328 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1328.certificate 1216 accepted1328
theorem accepted1329 : minorantGammaCheck GammaPanel1329.certificate 1216=true := by decide +kernel
noncomputable def cell1329 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1329.certificate 1216 accepted1329
theorem accepted1330 : minorantGammaCheck GammaPanel1330.certificate 1216=true := by decide +kernel
noncomputable def cell1330 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1330.certificate 1216 accepted1330
theorem accepted1331 : minorantGammaCheck GammaPanel1331.certificate 1216=true := by decide +kernel
noncomputable def cell1331 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1331.certificate 1216 accepted1331
theorem accepted1332 : minorantGammaCheck GammaPanel1332.certificate 1216=true := by decide +kernel
noncomputable def cell1332 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1332.certificate 1216 accepted1332
theorem accepted1333 : minorantGammaCheck GammaPanel1333.certificate 1216=true := by decide +kernel
noncomputable def cell1333 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1333.certificate 1216 accepted1333
theorem accepted1334 : minorantGammaCheck GammaPanel1334.certificate 1216=true := by decide +kernel
noncomputable def cell1334 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1334.certificate 1216 accepted1334
theorem accepted1335 : minorantGammaCheck GammaPanel1335.certificate 1216=true := by decide +kernel
noncomputable def cell1335 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1335.certificate 1216 accepted1335
noncomputable def cells : List CertifiedMinorantCell := [cell1328, cell1329, cell1330, cell1331, cell1332, cell1333, cell1334, cell1335]
theorem chainAccepted : minorantChainCheck (161/200) (809/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (161/200) (809/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0166
