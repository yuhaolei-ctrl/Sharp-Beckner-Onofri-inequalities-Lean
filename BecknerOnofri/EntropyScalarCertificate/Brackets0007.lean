module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0017
public import BecknerOnofri.EntropyScalarCertificate.Bessel0018
public import BecknerOnofri.EntropyScalarCertificate.Bessel0019

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0007
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0112b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨32,by decide⟩
def lo0112b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨33,by decide⟩
def lo0112 : CheckedMoment :=
  CheckedMoment.ofBessel lo0112b1 lo0112b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0112b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨37,by decide⟩
def hi0112b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨38,by decide⟩
def hi0112 : CheckedMoment :=
  CheckedMoment.ofBessel hi0112b1 hi0112b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0112 : meanBracketCheck (789/10000) lo0112 hi0112=true := by decide +kernel
def bracket0112 : MeanBracket := meanBracketOfMoments (789/10000) lo0112 hi0112 accepted0112
def lo0113b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨42,by decide⟩
def lo0113b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨43,by decide⟩
def lo0113 : CheckedMoment :=
  CheckedMoment.ofBessel lo0113b1 lo0113b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0113b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨47,by decide⟩
def hi0113b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨48,by decide⟩
def hi0113 : CheckedMoment :=
  CheckedMoment.ofBessel hi0113b1 hi0113b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0113 : meanBracketCheck (791/10000) lo0113 hi0113=true := by decide +kernel
def bracket0113 : MeanBracket := meanBracketOfMoments (791/10000) lo0113 hi0113 accepted0113
def lo0114b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨52,by decide⟩
def lo0114b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨53,by decide⟩
def lo0114 : CheckedMoment :=
  CheckedMoment.ofBessel lo0114b1 lo0114b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0114b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨57,by decide⟩
def hi0114b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨58,by decide⟩
def hi0114 : CheckedMoment :=
  CheckedMoment.ofBessel hi0114b1 hi0114b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0114 : meanBracketCheck (793/10000) lo0114 hi0114=true := by decide +kernel
def bracket0114 : MeanBracket := meanBracketOfMoments (793/10000) lo0114 hi0114 accepted0114
def lo0115b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨62,by decide⟩
def lo0115b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨63,by decide⟩
def lo0115 : CheckedMoment :=
  CheckedMoment.ofBessel lo0115b1 lo0115b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0115b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨3,by decide⟩
def hi0115b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨4,by decide⟩
def hi0115 : CheckedMoment :=
  CheckedMoment.ofBessel hi0115b1 hi0115b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0115 : meanBracketCheck (159/2000) lo0115 hi0115=true := by decide +kernel
def bracket0115 : MeanBracket := meanBracketOfMoments (159/2000) lo0115 hi0115 accepted0115
def lo0116b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨8,by decide⟩
def lo0116b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨9,by decide⟩
def lo0116 : CheckedMoment :=
  CheckedMoment.ofBessel lo0116b1 lo0116b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0116b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨13,by decide⟩
def hi0116b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨14,by decide⟩
def hi0116 : CheckedMoment :=
  CheckedMoment.ofBessel hi0116b1 hi0116b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0116 : meanBracketCheck (797/10000) lo0116 hi0116=true := by decide +kernel
def bracket0116 : MeanBracket := meanBracketOfMoments (797/10000) lo0116 hi0116 accepted0116
def lo0117b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨18,by decide⟩
def lo0117b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨19,by decide⟩
def lo0117 : CheckedMoment :=
  CheckedMoment.ofBessel lo0117b1 lo0117b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0117b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨23,by decide⟩
def hi0117b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨24,by decide⟩
def hi0117 : CheckedMoment :=
  CheckedMoment.ofBessel hi0117b1 hi0117b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0117 : meanBracketCheck (799/10000) lo0117 hi0117=true := by decide +kernel
def bracket0117 : MeanBracket := meanBracketOfMoments (799/10000) lo0117 hi0117 accepted0117
def lo0118b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨28,by decide⟩
def lo0118b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨29,by decide⟩
def lo0118 : CheckedMoment :=
  CheckedMoment.ofBessel lo0118b1 lo0118b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0118b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨33,by decide⟩
def hi0118b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨34,by decide⟩
def hi0118 : CheckedMoment :=
  CheckedMoment.ofBessel hi0118b1 hi0118b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0118 : meanBracketCheck (801/10000) lo0118 hi0118=true := by decide +kernel
def bracket0118 : MeanBracket := meanBracketOfMoments (801/10000) lo0118 hi0118 accepted0118
def lo0119b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨38,by decide⟩
def lo0119b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨39,by decide⟩
def lo0119 : CheckedMoment :=
  CheckedMoment.ofBessel lo0119b1 lo0119b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0119b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨43,by decide⟩
def hi0119b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨44,by decide⟩
def hi0119 : CheckedMoment :=
  CheckedMoment.ofBessel hi0119b1 hi0119b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0119 : meanBracketCheck (803/10000) lo0119 hi0119=true := by decide +kernel
def bracket0119 : MeanBracket := meanBracketOfMoments (803/10000) lo0119 hi0119 accepted0119
def lo0120b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨48,by decide⟩
def lo0120b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨49,by decide⟩
def lo0120 : CheckedMoment :=
  CheckedMoment.ofBessel lo0120b1 lo0120b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0120b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨53,by decide⟩
def hi0120b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨54,by decide⟩
def hi0120 : CheckedMoment :=
  CheckedMoment.ofBessel hi0120b1 hi0120b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0120 : meanBracketCheck (161/2000) lo0120 hi0120=true := by decide +kernel
def bracket0120 : MeanBracket := meanBracketOfMoments (161/2000) lo0120 hi0120 accepted0120
def lo0121b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨58,by decide⟩
def lo0121b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨59,by decide⟩
def lo0121 : CheckedMoment :=
  CheckedMoment.ofBessel lo0121b1 lo0121b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0121b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0018.rows BesselBatch0018.accepted ⟨63,by decide⟩
def hi0121b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨0,by decide⟩
def hi0121 : CheckedMoment :=
  CheckedMoment.ofBessel hi0121b1 hi0121b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0121 : meanBracketCheck (807/10000) lo0121 hi0121=true := by decide +kernel
def bracket0121 : MeanBracket := meanBracketOfMoments (807/10000) lo0121 hi0121 accepted0121
def lo0122b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨4,by decide⟩
def lo0122b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨5,by decide⟩
def lo0122 : CheckedMoment :=
  CheckedMoment.ofBessel lo0122b1 lo0122b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0122b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨9,by decide⟩
def hi0122b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨10,by decide⟩
def hi0122 : CheckedMoment :=
  CheckedMoment.ofBessel hi0122b1 hi0122b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0122 : meanBracketCheck (809/10000) lo0122 hi0122=true := by decide +kernel
def bracket0122 : MeanBracket := meanBracketOfMoments (809/10000) lo0122 hi0122 accepted0122
def lo0123b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨14,by decide⟩
def lo0123b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨15,by decide⟩
def lo0123 : CheckedMoment :=
  CheckedMoment.ofBessel lo0123b1 lo0123b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0123b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨19,by decide⟩
def hi0123b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨20,by decide⟩
def hi0123 : CheckedMoment :=
  CheckedMoment.ofBessel hi0123b1 hi0123b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0123 : meanBracketCheck (811/10000) lo0123 hi0123=true := by decide +kernel
def bracket0123 : MeanBracket := meanBracketOfMoments (811/10000) lo0123 hi0123 accepted0123
def lo0124b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨24,by decide⟩
def lo0124b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨25,by decide⟩
def lo0124 : CheckedMoment :=
  CheckedMoment.ofBessel lo0124b1 lo0124b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0124b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨29,by decide⟩
def hi0124b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨30,by decide⟩
def hi0124 : CheckedMoment :=
  CheckedMoment.ofBessel hi0124b1 hi0124b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0124 : meanBracketCheck (813/10000) lo0124 hi0124=true := by decide +kernel
def bracket0124 : MeanBracket := meanBracketOfMoments (813/10000) lo0124 hi0124 accepted0124
def lo0125b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨34,by decide⟩
def lo0125b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨35,by decide⟩
def lo0125 : CheckedMoment :=
  CheckedMoment.ofBessel lo0125b1 lo0125b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0125b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨39,by decide⟩
def hi0125b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨40,by decide⟩
def hi0125 : CheckedMoment :=
  CheckedMoment.ofBessel hi0125b1 hi0125b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0125 : meanBracketCheck (163/2000) lo0125 hi0125=true := by decide +kernel
def bracket0125 : MeanBracket := meanBracketOfMoments (163/2000) lo0125 hi0125 accepted0125
def lo0126b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨44,by decide⟩
def lo0126b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨45,by decide⟩
def lo0126 : CheckedMoment :=
  CheckedMoment.ofBessel lo0126b1 lo0126b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0126b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨49,by decide⟩
def hi0126b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨50,by decide⟩
def hi0126 : CheckedMoment :=
  CheckedMoment.ofBessel hi0126b1 hi0126b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0126 : meanBracketCheck (817/10000) lo0126 hi0126=true := by decide +kernel
def bracket0126 : MeanBracket := meanBracketOfMoments (817/10000) lo0126 hi0126 accepted0126
def lo0127b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨54,by decide⟩
def lo0127b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨55,by decide⟩
def lo0127 : CheckedMoment :=
  CheckedMoment.ofBessel lo0127b1 lo0127b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0127b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨59,by decide⟩
def hi0127b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0019.rows BesselBatch0019.accepted ⟨60,by decide⟩
def hi0127 : CheckedMoment :=
  CheckedMoment.ofBessel hi0127b1 hi0127b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0127 : meanBracketCheck (819/10000) lo0127 hi0127=true := by decide +kernel
def bracket0127 : MeanBracket := meanBracketOfMoments (819/10000) lo0127 hi0127 accepted0127
#print axioms bracket0112
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0007
