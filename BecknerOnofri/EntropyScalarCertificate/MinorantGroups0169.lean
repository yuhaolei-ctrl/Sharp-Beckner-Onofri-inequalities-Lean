module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0169

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0169
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1352 : minorantGammaCheck GammaPanel1352.certificate 1223=true := by decide +kernel
noncomputable def cell1352 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1352.certificate 1223 accepted1352
theorem accepted1353 : minorantGammaCheck GammaPanel1353.certificate 1224=true := by decide +kernel
noncomputable def cell1353 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1353.certificate 1224 accepted1353
theorem accepted1354 : minorantGammaCheck GammaPanel1354.certificate 1225=true := by decide +kernel
noncomputable def cell1354 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1354.certificate 1225 accepted1354
theorem accepted1355 : minorantGammaCheck GammaPanel1355.certificate 1226=true := by decide +kernel
noncomputable def cell1355 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1355.certificate 1226 accepted1355
theorem accepted1356 : minorantGammaCheck GammaPanel1356.certificate 1227=true := by decide +kernel
noncomputable def cell1356 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1356.certificate 1227 accepted1356
theorem accepted1357 : minorantGammaCheck GammaPanel1357.certificate 1228=true := by decide +kernel
noncomputable def cell1357 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1357.certificate 1228 accepted1357
theorem accepted1358 : minorantGammaCheck GammaPanel1358.certificate 1229=true := by decide +kernel
noncomputable def cell1358 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1358.certificate 1229 accepted1358
theorem accepted1359 : minorantGammaCheck GammaPanel1359.certificate 1230=true := by decide +kernel
noncomputable def cell1359 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1359.certificate 1230 accepted1359
noncomputable def cells : List CertifiedMinorantCell := [cell1352, cell1353, cell1354, cell1355, cell1356, cell1357, cell1358, cell1359]
theorem chainAccepted : minorantChainCheck (817/1000) (821/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (817/1000) (821/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0169
