import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0048
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0048
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0384 : minorantGammaCheck GammaPanel0384.certificate 344=true := by decide +kernel
noncomputable def cell0384 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0384.certificate 344 accepted0384
theorem accepted0385 : minorantGammaCheck GammaPanel0385.certificate 345=true := by decide +kernel
noncomputable def cell0385 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0385.certificate 345 accepted0385
theorem accepted0386 : minorantGammaCheck GammaPanel0386.certificate 346=true := by decide +kernel
noncomputable def cell0386 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0386.certificate 346 accepted0386
theorem accepted0387 : minorantGammaCheck GammaPanel0387.certificate 347=true := by decide +kernel
noncomputable def cell0387 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0387.certificate 347 accepted0387
theorem accepted0388 : minorantGammaCheck GammaPanel0388.certificate 348=true := by decide +kernel
noncomputable def cell0388 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0388.certificate 348 accepted0388
theorem accepted0389 : minorantGammaCheck GammaPanel0389.certificate 349=true := by decide +kernel
noncomputable def cell0389 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0389.certificate 349 accepted0389
theorem accepted0390 : minorantGammaCheck GammaPanel0390.certificate 350=true := by decide +kernel
noncomputable def cell0390 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0390.certificate 350 accepted0390
theorem accepted0391 : minorantGammaCheck GammaPanel0391.certificate 351=true := by decide +kernel
noncomputable def cell0391 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0391.certificate 351 accepted0391
noncomputable def cells : List CertifiedMinorantCell := [cell0384, cell0385, cell0386, cell0387, cell0388, cell0389, cell0390, cell0391]
theorem chainAccepted : minorantChainCheck (1333/10000) (1349/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1333/10000) (1349/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0048
