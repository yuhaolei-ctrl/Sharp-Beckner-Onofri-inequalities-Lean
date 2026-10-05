module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0007
public import BecknerOnofri.EntropyScalarCertificate.Bessel0008
public import BecknerOnofri.EntropyScalarCertificate.Bessel0009

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0003
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0048b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨32,by decide⟩
def lo0048b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨33,by decide⟩
def lo0048 : CheckedMoment :=
  CheckedMoment.ofBessel lo0048b1 lo0048b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0048b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨37,by decide⟩
def hi0048b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨38,by decide⟩
def hi0048 : CheckedMoment :=
  CheckedMoment.ofBessel hi0048b1 hi0048b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0048 : meanBracketCheck (661/10000) lo0048 hi0048=true := by decide +kernel
def bracket0048 : MeanBracket := meanBracketOfMoments (661/10000) lo0048 hi0048 accepted0048
def lo0049b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨42,by decide⟩
def lo0049b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨43,by decide⟩
def lo0049 : CheckedMoment :=
  CheckedMoment.ofBessel lo0049b1 lo0049b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0049b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨47,by decide⟩
def hi0049b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨48,by decide⟩
def hi0049 : CheckedMoment :=
  CheckedMoment.ofBessel hi0049b1 hi0049b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0049 : meanBracketCheck (663/10000) lo0049 hi0049=true := by decide +kernel
def bracket0049 : MeanBracket := meanBracketOfMoments (663/10000) lo0049 hi0049 accepted0049
def lo0050b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨52,by decide⟩
def lo0050b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨53,by decide⟩
def lo0050 : CheckedMoment :=
  CheckedMoment.ofBessel lo0050b1 lo0050b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0050b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨57,by decide⟩
def hi0050b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨58,by decide⟩
def hi0050 : CheckedMoment :=
  CheckedMoment.ofBessel hi0050b1 hi0050b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0050 : meanBracketCheck (133/2000) lo0050 hi0050=true := by decide +kernel
def bracket0050 : MeanBracket := meanBracketOfMoments (133/2000) lo0050 hi0050 accepted0050
def lo0051b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨62,by decide⟩
def lo0051b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨63,by decide⟩
def lo0051 : CheckedMoment :=
  CheckedMoment.ofBessel lo0051b1 lo0051b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0051b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨3,by decide⟩
def hi0051b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨4,by decide⟩
def hi0051 : CheckedMoment :=
  CheckedMoment.ofBessel hi0051b1 hi0051b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0051 : meanBracketCheck (667/10000) lo0051 hi0051=true := by decide +kernel
def bracket0051 : MeanBracket := meanBracketOfMoments (667/10000) lo0051 hi0051 accepted0051
def lo0052b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨8,by decide⟩
def lo0052b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨9,by decide⟩
def lo0052 : CheckedMoment :=
  CheckedMoment.ofBessel lo0052b1 lo0052b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0052b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨13,by decide⟩
def hi0052b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨14,by decide⟩
def hi0052 : CheckedMoment :=
  CheckedMoment.ofBessel hi0052b1 hi0052b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0052 : meanBracketCheck (669/10000) lo0052 hi0052=true := by decide +kernel
def bracket0052 : MeanBracket := meanBracketOfMoments (669/10000) lo0052 hi0052 accepted0052
def lo0053b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨18,by decide⟩
def lo0053b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨19,by decide⟩
def lo0053 : CheckedMoment :=
  CheckedMoment.ofBessel lo0053b1 lo0053b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0053b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨23,by decide⟩
def hi0053b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨24,by decide⟩
def hi0053 : CheckedMoment :=
  CheckedMoment.ofBessel hi0053b1 hi0053b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0053 : meanBracketCheck (671/10000) lo0053 hi0053=true := by decide +kernel
def bracket0053 : MeanBracket := meanBracketOfMoments (671/10000) lo0053 hi0053 accepted0053
def lo0054b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨28,by decide⟩
def lo0054b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨29,by decide⟩
def lo0054 : CheckedMoment :=
  CheckedMoment.ofBessel lo0054b1 lo0054b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0054b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨33,by decide⟩
def hi0054b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨34,by decide⟩
def hi0054 : CheckedMoment :=
  CheckedMoment.ofBessel hi0054b1 hi0054b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0054 : meanBracketCheck (673/10000) lo0054 hi0054=true := by decide +kernel
def bracket0054 : MeanBracket := meanBracketOfMoments (673/10000) lo0054 hi0054 accepted0054
def lo0055b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨38,by decide⟩
def lo0055b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨39,by decide⟩
def lo0055 : CheckedMoment :=
  CheckedMoment.ofBessel lo0055b1 lo0055b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0055b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨43,by decide⟩
def hi0055b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨44,by decide⟩
def hi0055 : CheckedMoment :=
  CheckedMoment.ofBessel hi0055b1 hi0055b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0055 : meanBracketCheck (27/400) lo0055 hi0055=true := by decide +kernel
def bracket0055 : MeanBracket := meanBracketOfMoments (27/400) lo0055 hi0055 accepted0055
def lo0056b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨48,by decide⟩
def lo0056b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨49,by decide⟩
def lo0056 : CheckedMoment :=
  CheckedMoment.ofBessel lo0056b1 lo0056b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0056b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨53,by decide⟩
def hi0056b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨54,by decide⟩
def hi0056 : CheckedMoment :=
  CheckedMoment.ofBessel hi0056b1 hi0056b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0056 : meanBracketCheck (677/10000) lo0056 hi0056=true := by decide +kernel
def bracket0056 : MeanBracket := meanBracketOfMoments (677/10000) lo0056 hi0056 accepted0056
def lo0057b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨58,by decide⟩
def lo0057b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨59,by decide⟩
def lo0057 : CheckedMoment :=
  CheckedMoment.ofBessel lo0057b1 lo0057b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0057b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨63,by decide⟩
def hi0057b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨0,by decide⟩
def hi0057 : CheckedMoment :=
  CheckedMoment.ofBessel hi0057b1 hi0057b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0057 : meanBracketCheck (679/10000) lo0057 hi0057=true := by decide +kernel
def bracket0057 : MeanBracket := meanBracketOfMoments (679/10000) lo0057 hi0057 accepted0057
def lo0058b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨4,by decide⟩
def lo0058b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨5,by decide⟩
def lo0058 : CheckedMoment :=
  CheckedMoment.ofBessel lo0058b1 lo0058b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0058b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨9,by decide⟩
def hi0058b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨10,by decide⟩
def hi0058 : CheckedMoment :=
  CheckedMoment.ofBessel hi0058b1 hi0058b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0058 : meanBracketCheck (681/10000) lo0058 hi0058=true := by decide +kernel
def bracket0058 : MeanBracket := meanBracketOfMoments (681/10000) lo0058 hi0058 accepted0058
def lo0059b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨14,by decide⟩
def lo0059b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨15,by decide⟩
def lo0059 : CheckedMoment :=
  CheckedMoment.ofBessel lo0059b1 lo0059b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0059b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨19,by decide⟩
def hi0059b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨20,by decide⟩
def hi0059 : CheckedMoment :=
  CheckedMoment.ofBessel hi0059b1 hi0059b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0059 : meanBracketCheck (683/10000) lo0059 hi0059=true := by decide +kernel
def bracket0059 : MeanBracket := meanBracketOfMoments (683/10000) lo0059 hi0059 accepted0059
def lo0060b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨24,by decide⟩
def lo0060b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨25,by decide⟩
def lo0060 : CheckedMoment :=
  CheckedMoment.ofBessel lo0060b1 lo0060b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0060b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨29,by decide⟩
def hi0060b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨30,by decide⟩
def hi0060 : CheckedMoment :=
  CheckedMoment.ofBessel hi0060b1 hi0060b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0060 : meanBracketCheck (137/2000) lo0060 hi0060=true := by decide +kernel
def bracket0060 : MeanBracket := meanBracketOfMoments (137/2000) lo0060 hi0060 accepted0060
def lo0061b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨34,by decide⟩
def lo0061b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨35,by decide⟩
def lo0061 : CheckedMoment :=
  CheckedMoment.ofBessel lo0061b1 lo0061b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0061b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨39,by decide⟩
def hi0061b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨40,by decide⟩
def hi0061 : CheckedMoment :=
  CheckedMoment.ofBessel hi0061b1 hi0061b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0061 : meanBracketCheck (687/10000) lo0061 hi0061=true := by decide +kernel
def bracket0061 : MeanBracket := meanBracketOfMoments (687/10000) lo0061 hi0061 accepted0061
def lo0062b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨44,by decide⟩
def lo0062b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨45,by decide⟩
def lo0062 : CheckedMoment :=
  CheckedMoment.ofBessel lo0062b1 lo0062b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0062b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨49,by decide⟩
def hi0062b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨50,by decide⟩
def hi0062 : CheckedMoment :=
  CheckedMoment.ofBessel hi0062b1 hi0062b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0062 : meanBracketCheck (689/10000) lo0062 hi0062=true := by decide +kernel
def bracket0062 : MeanBracket := meanBracketOfMoments (689/10000) lo0062 hi0062 accepted0062
def lo0063b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨54,by decide⟩
def lo0063b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨55,by decide⟩
def lo0063 : CheckedMoment :=
  CheckedMoment.ofBessel lo0063b1 lo0063b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0063b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨59,by decide⟩
def hi0063b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨60,by decide⟩
def hi0063 : CheckedMoment :=
  CheckedMoment.ofBessel hi0063b1 hi0063b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0063 : meanBracketCheck (691/10000) lo0063 hi0063=true := by decide +kernel
def bracket0063 : MeanBracket := meanBracketOfMoments (691/10000) lo0063 hi0063 accepted0063
#print axioms bracket0048
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0003
