module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0002

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0002
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0016 : minorantGammaCheck GammaPanel0016.certificate 0=true := by decide +kernel
noncomputable def cell0016 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0016.certificate 0 accepted0016
theorem accepted0017 : minorantGammaCheck GammaPanel0017.certificate 0=true := by decide +kernel
noncomputable def cell0017 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0017.certificate 0 accepted0017
theorem accepted0018 : minorantGammaCheck GammaPanel0018.certificate 0=true := by decide +kernel
noncomputable def cell0018 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0018.certificate 0 accepted0018
theorem accepted0019 : minorantGammaCheck GammaPanel0019.certificate 0=true := by decide +kernel
noncomputable def cell0019 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0019.certificate 0 accepted0019
theorem accepted0020 : minorantGammaCheck GammaPanel0020.certificate 0=true := by decide +kernel
noncomputable def cell0020 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0020.certificate 0 accepted0020
theorem accepted0021 : minorantGammaCheck GammaPanel0021.certificate 0=true := by decide +kernel
noncomputable def cell0021 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0021.certificate 0 accepted0021
theorem accepted0022 : minorantGammaCheck GammaPanel0022.certificate 0=true := by decide +kernel
noncomputable def cell0022 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0022.certificate 0 accepted0022
theorem accepted0023 : minorantGammaCheck GammaPanel0023.certificate 0=true := by decide +kernel
noncomputable def cell0023 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0023.certificate 0 accepted0023
noncomputable def cells : List CertifiedMinorantCell := [cell0016, cell0017, cell0018, cell0019, cell0020, cell0021, cell0022, cell0023]
theorem chainAccepted : minorantChainCheck (633/10000) (637/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (633/10000) (637/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0002
