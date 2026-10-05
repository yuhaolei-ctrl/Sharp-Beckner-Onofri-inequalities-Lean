module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0173

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0173
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1384 : minorantGammaCheck GammaPanel1384.certificate 1249=true := by decide +kernel
noncomputable def cell1384 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1384.certificate 1249 accepted1384
theorem accepted1385 : minorantGammaCheck GammaPanel1385.certificate 1249=true := by decide +kernel
noncomputable def cell1385 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1385.certificate 1249 accepted1385
theorem accepted1386 : minorantGammaCheck GammaPanel1386.certificate 1249=true := by decide +kernel
noncomputable def cell1386 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1386.certificate 1249 accepted1386
theorem accepted1387 : minorantGammaCheck GammaPanel1387.certificate 1249=true := by decide +kernel
noncomputable def cell1387 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1387.certificate 1249 accepted1387
theorem accepted1388 : minorantGammaCheck GammaPanel1388.certificate 1249=true := by decide +kernel
noncomputable def cell1388 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1388.certificate 1249 accepted1388
theorem accepted1389 : minorantGammaCheck GammaPanel1389.certificate 1249=true := by decide +kernel
noncomputable def cell1389 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1389.certificate 1249 accepted1389
theorem accepted1390 : minorantGammaCheck GammaPanel1390.certificate 1249=true := by decide +kernel
noncomputable def cell1390 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1390.certificate 1249 accepted1390
theorem accepted1391 : minorantGammaCheck GammaPanel1391.certificate 1249=true := by decide +kernel
noncomputable def cell1391 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1391.certificate 1249 accepted1391
noncomputable def cells : List CertifiedMinorantCell := [cell1384, cell1385, cell1386, cell1387, cell1388, cell1389, cell1390, cell1391]
theorem chainAccepted : minorantChainCheck (4153/5000) (4157/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4153/5000) (4157/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0173
