module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0244

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0244
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1952 : minorantGammaCheck GammaPanel1952.certificate 1596=true := by decide +kernel
noncomputable def cell1952 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1952.certificate 1596 accepted1952
theorem accepted1953 : minorantGammaCheck GammaPanel1953.certificate 1597=true := by decide +kernel
noncomputable def cell1953 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1953.certificate 1597 accepted1953
theorem accepted1954 : minorantGammaCheck GammaPanel1954.certificate 1598=true := by decide +kernel
noncomputable def cell1954 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1954.certificate 1598 accepted1954
theorem accepted1955 : minorantGammaCheck GammaPanel1955.certificate 1599=true := by decide +kernel
noncomputable def cell1955 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1955.certificate 1599 accepted1955
theorem accepted1956 : minorantGammaCheck GammaPanel1956.certificate 1600=true := by decide +kernel
noncomputable def cell1956 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1956.certificate 1600 accepted1956
theorem accepted1957 : minorantGammaCheck GammaPanel1957.certificate 1601=true := by decide +kernel
noncomputable def cell1957 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1957.certificate 1601 accepted1957
theorem accepted1958 : minorantGammaCheck GammaPanel1958.certificate 1602=true := by decide +kernel
noncomputable def cell1958 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1958.certificate 1602 accepted1958
theorem accepted1959 : minorantGammaCheck GammaPanel1959.certificate 1603=true := by decide +kernel
noncomputable def cell1959 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1959.certificate 1603 accepted1959
noncomputable def cells : List CertifiedMinorantCell := [cell1952, cell1953, cell1954, cell1955, cell1956, cell1957, cell1958, cell1959]
theorem chainAccepted : minorantChainCheck (937/1000) (941/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (937/1000) (941/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0244
