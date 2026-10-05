import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0123
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0123
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0984 : minorantGammaCheck GammaPanel0984.certificate 882=true := by decide +kernel
noncomputable def cell0984 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0984.certificate 882 accepted0984
theorem accepted0985 : minorantGammaCheck GammaPanel0985.certificate 883=true := by decide +kernel
noncomputable def cell0985 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0985.certificate 883 accepted0985
theorem accepted0986 : minorantGammaCheck GammaPanel0986.certificate 884=true := by decide +kernel
noncomputable def cell0986 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0986.certificate 884 accepted0986
theorem accepted0987 : minorantGammaCheck GammaPanel0987.certificate 885=true := by decide +kernel
noncomputable def cell0987 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0987.certificate 885 accepted0987
theorem accepted0988 : minorantGammaCheck GammaPanel0988.certificate 886=true := by decide +kernel
noncomputable def cell0988 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0988.certificate 886 accepted0988
theorem accepted0989 : minorantGammaCheck GammaPanel0989.certificate 887=true := by decide +kernel
noncomputable def cell0989 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0989.certificate 887 accepted0989
theorem accepted0990 : minorantGammaCheck GammaPanel0990.certificate 888=true := by decide +kernel
noncomputable def cell0990 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0990.certificate 888 accepted0990
theorem accepted0991 : minorantGammaCheck GammaPanel0991.certificate 889=true := by decide +kernel
noncomputable def cell0991 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0991.certificate 889 accepted0991
noncomputable def cells : List CertifiedMinorantCell := [cell0984, cell0985, cell0986, cell0987, cell0988, cell0989, cell0990, cell0991]
theorem chainAccepted : minorantChainCheck (233/500) (237/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (233/500) (237/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0123
