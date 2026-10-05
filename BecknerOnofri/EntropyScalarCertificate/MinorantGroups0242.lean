import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0242
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0242
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1936 : minorantGammaCheck GammaPanel1936.certificate 1580=true := by decide +kernel
noncomputable def cell1936 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1936.certificate 1580 accepted1936
theorem accepted1937 : minorantGammaCheck GammaPanel1937.certificate 1581=true := by decide +kernel
noncomputable def cell1937 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1937.certificate 1581 accepted1937
theorem accepted1938 : minorantGammaCheck GammaPanel1938.certificate 1582=true := by decide +kernel
noncomputable def cell1938 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1938.certificate 1582 accepted1938
theorem accepted1939 : minorantGammaCheck GammaPanel1939.certificate 1583=true := by decide +kernel
noncomputable def cell1939 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1939.certificate 1583 accepted1939
theorem accepted1940 : minorantGammaCheck GammaPanel1940.certificate 1584=true := by decide +kernel
noncomputable def cell1940 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1940.certificate 1584 accepted1940
theorem accepted1941 : minorantGammaCheck GammaPanel1941.certificate 1585=true := by decide +kernel
noncomputable def cell1941 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1941.certificate 1585 accepted1941
theorem accepted1942 : minorantGammaCheck GammaPanel1942.certificate 1586=true := by decide +kernel
noncomputable def cell1942 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1942.certificate 1586 accepted1942
theorem accepted1943 : minorantGammaCheck GammaPanel1943.certificate 1587=true := by decide +kernel
noncomputable def cell1943 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1943.certificate 1587 accepted1943
noncomputable def cells : List CertifiedMinorantCell := [cell1936, cell1937, cell1938, cell1939, cell1940, cell1941, cell1942, cell1943]
theorem chainAccepted : minorantChainCheck (929/1000) (933/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (929/1000) (933/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0242
