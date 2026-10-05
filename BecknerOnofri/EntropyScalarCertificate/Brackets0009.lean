module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0022
public import BecknerOnofri.EntropyScalarCertificate.Bessel0023
public import BecknerOnofri.EntropyScalarCertificate.Bessel0024

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0009
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0144b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨32,by decide⟩
def lo0144b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨33,by decide⟩
def lo0144 : CheckedMoment :=
  CheckedMoment.ofBessel lo0144b1 lo0144b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0144b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨37,by decide⟩
def hi0144b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨38,by decide⟩
def hi0144 : CheckedMoment :=
  CheckedMoment.ofBessel hi0144b1 hi0144b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0144 : meanBracketCheck (853/10000) lo0144 hi0144=true := by decide +kernel
def bracket0144 : MeanBracket := meanBracketOfMoments (853/10000) lo0144 hi0144 accepted0144
def lo0145b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨42,by decide⟩
def lo0145b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨43,by decide⟩
def lo0145 : CheckedMoment :=
  CheckedMoment.ofBessel lo0145b1 lo0145b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0145b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨47,by decide⟩
def hi0145b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨48,by decide⟩
def hi0145 : CheckedMoment :=
  CheckedMoment.ofBessel hi0145b1 hi0145b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0145 : meanBracketCheck (171/2000) lo0145 hi0145=true := by decide +kernel
def bracket0145 : MeanBracket := meanBracketOfMoments (171/2000) lo0145 hi0145 accepted0145
def lo0146b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨52,by decide⟩
def lo0146b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨53,by decide⟩
def lo0146 : CheckedMoment :=
  CheckedMoment.ofBessel lo0146b1 lo0146b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0146b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨57,by decide⟩
def hi0146b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨58,by decide⟩
def hi0146 : CheckedMoment :=
  CheckedMoment.ofBessel hi0146b1 hi0146b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0146 : meanBracketCheck (857/10000) lo0146 hi0146=true := by decide +kernel
def bracket0146 : MeanBracket := meanBracketOfMoments (857/10000) lo0146 hi0146 accepted0146
def lo0147b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨62,by decide⟩
def lo0147b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨63,by decide⟩
def lo0147 : CheckedMoment :=
  CheckedMoment.ofBessel lo0147b1 lo0147b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0147b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨3,by decide⟩
def hi0147b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨4,by decide⟩
def hi0147 : CheckedMoment :=
  CheckedMoment.ofBessel hi0147b1 hi0147b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0147 : meanBracketCheck (859/10000) lo0147 hi0147=true := by decide +kernel
def bracket0147 : MeanBracket := meanBracketOfMoments (859/10000) lo0147 hi0147 accepted0147
def lo0148b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨8,by decide⟩
def lo0148b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨9,by decide⟩
def lo0148 : CheckedMoment :=
  CheckedMoment.ofBessel lo0148b1 lo0148b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0148b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨13,by decide⟩
def hi0148b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨14,by decide⟩
def hi0148 : CheckedMoment :=
  CheckedMoment.ofBessel hi0148b1 hi0148b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0148 : meanBracketCheck (861/10000) lo0148 hi0148=true := by decide +kernel
def bracket0148 : MeanBracket := meanBracketOfMoments (861/10000) lo0148 hi0148 accepted0148
def lo0149b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨18,by decide⟩
def lo0149b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨19,by decide⟩
def lo0149 : CheckedMoment :=
  CheckedMoment.ofBessel lo0149b1 lo0149b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0149b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨23,by decide⟩
def hi0149b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨24,by decide⟩
def hi0149 : CheckedMoment :=
  CheckedMoment.ofBessel hi0149b1 hi0149b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0149 : meanBracketCheck (863/10000) lo0149 hi0149=true := by decide +kernel
def bracket0149 : MeanBracket := meanBracketOfMoments (863/10000) lo0149 hi0149 accepted0149
def lo0150b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨28,by decide⟩
def lo0150b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨29,by decide⟩
def lo0150 : CheckedMoment :=
  CheckedMoment.ofBessel lo0150b1 lo0150b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0150b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨33,by decide⟩
def hi0150b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨34,by decide⟩
def hi0150 : CheckedMoment :=
  CheckedMoment.ofBessel hi0150b1 hi0150b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0150 : meanBracketCheck (173/2000) lo0150 hi0150=true := by decide +kernel
def bracket0150 : MeanBracket := meanBracketOfMoments (173/2000) lo0150 hi0150 accepted0150
def lo0151b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨38,by decide⟩
def lo0151b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨39,by decide⟩
def lo0151 : CheckedMoment :=
  CheckedMoment.ofBessel lo0151b1 lo0151b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0151b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨43,by decide⟩
def hi0151b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨44,by decide⟩
def hi0151 : CheckedMoment :=
  CheckedMoment.ofBessel hi0151b1 hi0151b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0151 : meanBracketCheck (867/10000) lo0151 hi0151=true := by decide +kernel
def bracket0151 : MeanBracket := meanBracketOfMoments (867/10000) lo0151 hi0151 accepted0151
def lo0152b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨48,by decide⟩
def lo0152b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨49,by decide⟩
def lo0152 : CheckedMoment :=
  CheckedMoment.ofBessel lo0152b1 lo0152b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0152b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨53,by decide⟩
def hi0152b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨54,by decide⟩
def hi0152 : CheckedMoment :=
  CheckedMoment.ofBessel hi0152b1 hi0152b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0152 : meanBracketCheck (869/10000) lo0152 hi0152=true := by decide +kernel
def bracket0152 : MeanBracket := meanBracketOfMoments (869/10000) lo0152 hi0152 accepted0152
def lo0153b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨58,by decide⟩
def lo0153b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨59,by decide⟩
def lo0153 : CheckedMoment :=
  CheckedMoment.ofBessel lo0153b1 lo0153b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0153b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨63,by decide⟩
def hi0153b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨0,by decide⟩
def hi0153 : CheckedMoment :=
  CheckedMoment.ofBessel hi0153b1 hi0153b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0153 : meanBracketCheck (871/10000) lo0153 hi0153=true := by decide +kernel
def bracket0153 : MeanBracket := meanBracketOfMoments (871/10000) lo0153 hi0153 accepted0153
def lo0154b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨4,by decide⟩
def lo0154b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨5,by decide⟩
def lo0154 : CheckedMoment :=
  CheckedMoment.ofBessel lo0154b1 lo0154b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0154b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨9,by decide⟩
def hi0154b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨10,by decide⟩
def hi0154 : CheckedMoment :=
  CheckedMoment.ofBessel hi0154b1 hi0154b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0154 : meanBracketCheck (873/10000) lo0154 hi0154=true := by decide +kernel
def bracket0154 : MeanBracket := meanBracketOfMoments (873/10000) lo0154 hi0154 accepted0154
def lo0155b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨14,by decide⟩
def lo0155b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨15,by decide⟩
def lo0155 : CheckedMoment :=
  CheckedMoment.ofBessel lo0155b1 lo0155b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0155b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨19,by decide⟩
def hi0155b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨20,by decide⟩
def hi0155 : CheckedMoment :=
  CheckedMoment.ofBessel hi0155b1 hi0155b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0155 : meanBracketCheck (7/80) lo0155 hi0155=true := by decide +kernel
def bracket0155 : MeanBracket := meanBracketOfMoments (7/80) lo0155 hi0155 accepted0155
def lo0156b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨24,by decide⟩
def lo0156b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨25,by decide⟩
def lo0156 : CheckedMoment :=
  CheckedMoment.ofBessel lo0156b1 lo0156b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0156b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨29,by decide⟩
def hi0156b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨30,by decide⟩
def hi0156 : CheckedMoment :=
  CheckedMoment.ofBessel hi0156b1 hi0156b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0156 : meanBracketCheck (877/10000) lo0156 hi0156=true := by decide +kernel
def bracket0156 : MeanBracket := meanBracketOfMoments (877/10000) lo0156 hi0156 accepted0156
def lo0157b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨34,by decide⟩
def lo0157b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨35,by decide⟩
def lo0157 : CheckedMoment :=
  CheckedMoment.ofBessel lo0157b1 lo0157b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0157b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨39,by decide⟩
def hi0157b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨40,by decide⟩
def hi0157 : CheckedMoment :=
  CheckedMoment.ofBessel hi0157b1 hi0157b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0157 : meanBracketCheck (879/10000) lo0157 hi0157=true := by decide +kernel
def bracket0157 : MeanBracket := meanBracketOfMoments (879/10000) lo0157 hi0157 accepted0157
def lo0158b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨44,by decide⟩
def lo0158b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨45,by decide⟩
def lo0158 : CheckedMoment :=
  CheckedMoment.ofBessel lo0158b1 lo0158b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0158b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨49,by decide⟩
def hi0158b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨50,by decide⟩
def hi0158 : CheckedMoment :=
  CheckedMoment.ofBessel hi0158b1 hi0158b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0158 : meanBracketCheck (881/10000) lo0158 hi0158=true := by decide +kernel
def bracket0158 : MeanBracket := meanBracketOfMoments (881/10000) lo0158 hi0158 accepted0158
def lo0159b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨54,by decide⟩
def lo0159b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨55,by decide⟩
def lo0159 : CheckedMoment :=
  CheckedMoment.ofBessel lo0159b1 lo0159b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0159b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨59,by decide⟩
def hi0159b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨60,by decide⟩
def hi0159 : CheckedMoment :=
  CheckedMoment.ofBessel hi0159b1 hi0159b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0159 : meanBracketCheck (883/10000) lo0159 hi0159=true := by decide +kernel
def bracket0159 : MeanBracket := meanBracketOfMoments (883/10000) lo0159 hi0159 accepted0159
#print axioms bracket0144
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0009
