module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0487
public import BecknerOnofri.EntropyScalarCertificate.Bessel0488

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0195
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo3120b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨32,by decide⟩
def lo3120b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨33,by decide⟩
def lo3120 : CheckedMoment :=
  CheckedMoment.ofBessel lo3120b1 lo3120b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3120b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨37,by decide⟩
def hi3120b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨38,by decide⟩
def hi3120 : CheckedMoment :=
  CheckedMoment.ofBessel hi3120b1 hi3120b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3120 : meanBracketCheck (12487/12500) lo3120 hi3120=true := by decide +kernel
def bracket3120 : MeanBracket := meanBracketOfMoments (12487/12500) lo3120 hi3120 accepted3120
def lo3121b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨42,by decide⟩
def lo3121b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨43,by decide⟩
def lo3121 : CheckedMoment :=
  CheckedMoment.ofBessel lo3121b1 lo3121b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3121b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨47,by decide⟩
def hi3121b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨48,by decide⟩
def hi3121 : CheckedMoment :=
  CheckedMoment.ofBessel hi3121b1 hi3121b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3121 : meanBracketCheck (199793/200000) lo3121 hi3121=true := by decide +kernel
def bracket3121 : MeanBracket := meanBracketOfMoments (199793/200000) lo3121 hi3121 accepted3121
def lo3122b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨52,by decide⟩
def lo3122b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨53,by decide⟩
def lo3122 : CheckedMoment :=
  CheckedMoment.ofBessel lo3122b1 lo3122b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3122b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨57,by decide⟩
def hi3122b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨58,by decide⟩
def hi3122 : CheckedMoment :=
  CheckedMoment.ofBessel hi3122b1 hi3122b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3122 : meanBracketCheck (99897/100000) lo3122 hi3122=true := by decide +kernel
def bracket3122 : MeanBracket := meanBracketOfMoments (99897/100000) lo3122 hi3122 accepted3122
def lo3123b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨62,by decide⟩
def lo3123b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0487.rows BesselBatch0487.accepted ⟨63,by decide⟩
def lo3123 : CheckedMoment :=
  CheckedMoment.ofBessel lo3123b1 lo3123b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3123b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨3,by decide⟩
def hi3123b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨4,by decide⟩
def hi3123 : CheckedMoment :=
  CheckedMoment.ofBessel hi3123b1 hi3123b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3123 : meanBracketCheck (39959/40000) lo3123 hi3123=true := by decide +kernel
def bracket3123 : MeanBracket := meanBracketOfMoments (39959/40000) lo3123 hi3123 accepted3123
def lo3124b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨8,by decide⟩
def lo3124b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨9,by decide⟩
def lo3124 : CheckedMoment :=
  CheckedMoment.ofBessel lo3124b1 lo3124b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3124b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨13,by decide⟩
def hi3124b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨14,by decide⟩
def hi3124 : CheckedMoment :=
  CheckedMoment.ofBessel hi3124b1 hi3124b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3124 : meanBracketCheck (49949/50000) lo3124 hi3124=true := by decide +kernel
def bracket3124 : MeanBracket := meanBracketOfMoments (49949/50000) lo3124 hi3124 accepted3124
def lo3125b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨18,by decide⟩
def lo3125b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨19,by decide⟩
def lo3125 : CheckedMoment :=
  CheckedMoment.ofBessel lo3125b1 lo3125b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3125b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨23,by decide⟩
def hi3125b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨24,by decide⟩
def hi3125 : CheckedMoment :=
  CheckedMoment.ofBessel hi3125b1 hi3125b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3125 : meanBracketCheck (199797/200000) lo3125 hi3125=true := by decide +kernel
def bracket3125 : MeanBracket := meanBracketOfMoments (199797/200000) lo3125 hi3125 accepted3125
def lo3126b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨28,by decide⟩
def lo3126b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨29,by decide⟩
def lo3126 : CheckedMoment :=
  CheckedMoment.ofBessel lo3126b1 lo3126b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3126b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨33,by decide⟩
def hi3126b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨34,by decide⟩
def hi3126 : CheckedMoment :=
  CheckedMoment.ofBessel hi3126b1 hi3126b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3126 : meanBracketCheck (99899/100000) lo3126 hi3126=true := by decide +kernel
def bracket3126 : MeanBracket := meanBracketOfMoments (99899/100000) lo3126 hi3126 accepted3126
def lo3127b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨38,by decide⟩
def lo3127b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨39,by decide⟩
def lo3127 : CheckedMoment :=
  CheckedMoment.ofBessel lo3127b1 lo3127b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3127b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨43,by decide⟩
def hi3127b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨44,by decide⟩
def hi3127 : CheckedMoment :=
  CheckedMoment.ofBessel hi3127b1 hi3127b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3127 : meanBracketCheck (199799/200000) lo3127 hi3127=true := by decide +kernel
def bracket3127 : MeanBracket := meanBracketOfMoments (199799/200000) lo3127 hi3127 accepted3127
def lo3128b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨48,by decide⟩
def lo3128b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨49,by decide⟩
def lo3128 : CheckedMoment :=
  CheckedMoment.ofBessel lo3128b1 lo3128b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3128b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨53,by decide⟩
def hi3128b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨54,by decide⟩
def hi3128 : CheckedMoment :=
  CheckedMoment.ofBessel hi3128b1 hi3128b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3128 : meanBracketCheck (999/1000) lo3128 hi3128=true := by decide +kernel
def bracket3128 : MeanBracket := meanBracketOfMoments (999/1000) lo3128 hi3128 accepted3128
#print axioms bracket3120
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0195
