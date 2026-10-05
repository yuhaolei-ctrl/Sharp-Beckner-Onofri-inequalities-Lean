module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0057

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0057
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0456 : minorantGammaCheck GammaPanel0456.certificate 416=true := by decide +kernel
noncomputable def cell0456 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0456.certificate 416 accepted0456
theorem accepted0457 : minorantGammaCheck GammaPanel0457.certificate 417=true := by decide +kernel
noncomputable def cell0457 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0457.certificate 417 accepted0457
theorem accepted0458 : minorantGammaCheck GammaPanel0458.certificate 418=true := by decide +kernel
noncomputable def cell0458 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0458.certificate 418 accepted0458
theorem accepted0459 : minorantGammaCheck GammaPanel0459.certificate 419=true := by decide +kernel
noncomputable def cell0459 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0459.certificate 419 accepted0459
theorem accepted0460 : minorantGammaCheck GammaPanel0460.certificate 420=true := by decide +kernel
noncomputable def cell0460 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0460.certificate 420 accepted0460
theorem accepted0461 : minorantGammaCheck GammaPanel0461.certificate 421=true := by decide +kernel
noncomputable def cell0461 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0461.certificate 421 accepted0461
theorem accepted0462 : minorantGammaCheck GammaPanel0462.certificate 422=true := by decide +kernel
noncomputable def cell0462 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0462.certificate 422 accepted0462
theorem accepted0463 : minorantGammaCheck GammaPanel0463.certificate 423=true := by decide +kernel
noncomputable def cell0463 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0463.certificate 423 accepted0463
noncomputable def cells : List CertifiedMinorantCell := [cell0456, cell0457, cell0458, cell0459, cell0460, cell0461, cell0462, cell0463]
theorem chainAccepted : minorantChainCheck (1477/10000) (1493/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1477/10000) (1493/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0057
