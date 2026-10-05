module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0157
public import BecknerOnofri.EntropyScalarCertificate.Bessel0158
public import BecknerOnofri.EntropyScalarCertificate.Bessel0159

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0063
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1008b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨32,by decide⟩
def lo1008b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨33,by decide⟩
def lo1008 : CheckedMoment :=
  CheckedMoment.ofBessel lo1008b1 lo1008b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1008b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨37,by decide⟩
def hi1008b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨38,by decide⟩
def hi1008 : CheckedMoment :=
  CheckedMoment.ofBessel hi1008b1 hi1008b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1008 : meanBracketCheck (49/100) lo1008 hi1008=true := by decide +kernel
def bracket1008 : MeanBracket := meanBracketOfMoments (49/100) lo1008 hi1008 accepted1008
def lo1009b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨42,by decide⟩
def lo1009b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨43,by decide⟩
def lo1009 : CheckedMoment :=
  CheckedMoment.ofBessel lo1009b1 lo1009b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1009b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨47,by decide⟩
def hi1009b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨48,by decide⟩
def hi1009 : CheckedMoment :=
  CheckedMoment.ofBessel hi1009b1 hi1009b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1009 : meanBracketCheck (491/1000) lo1009 hi1009=true := by decide +kernel
def bracket1009 : MeanBracket := meanBracketOfMoments (491/1000) lo1009 hi1009 accepted1009
def lo1010b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨52,by decide⟩
def lo1010b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨53,by decide⟩
def lo1010 : CheckedMoment :=
  CheckedMoment.ofBessel lo1010b1 lo1010b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1010b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨57,by decide⟩
def hi1010b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨58,by decide⟩
def hi1010 : CheckedMoment :=
  CheckedMoment.ofBessel hi1010b1 hi1010b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1010 : meanBracketCheck (123/250) lo1010 hi1010=true := by decide +kernel
def bracket1010 : MeanBracket := meanBracketOfMoments (123/250) lo1010 hi1010 accepted1010
def lo1011b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨62,by decide⟩
def lo1011b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨63,by decide⟩
def lo1011 : CheckedMoment :=
  CheckedMoment.ofBessel lo1011b1 lo1011b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1011b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨3,by decide⟩
def hi1011b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨4,by decide⟩
def hi1011 : CheckedMoment :=
  CheckedMoment.ofBessel hi1011b1 hi1011b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1011 : meanBracketCheck (493/1000) lo1011 hi1011=true := by decide +kernel
def bracket1011 : MeanBracket := meanBracketOfMoments (493/1000) lo1011 hi1011 accepted1011
def lo1012b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨8,by decide⟩
def lo1012b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨9,by decide⟩
def lo1012 : CheckedMoment :=
  CheckedMoment.ofBessel lo1012b1 lo1012b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1012b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨13,by decide⟩
def hi1012b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨14,by decide⟩
def hi1012 : CheckedMoment :=
  CheckedMoment.ofBessel hi1012b1 hi1012b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1012 : meanBracketCheck (247/500) lo1012 hi1012=true := by decide +kernel
def bracket1012 : MeanBracket := meanBracketOfMoments (247/500) lo1012 hi1012 accepted1012
def lo1013b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨18,by decide⟩
def lo1013b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨19,by decide⟩
def lo1013 : CheckedMoment :=
  CheckedMoment.ofBessel lo1013b1 lo1013b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1013b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨23,by decide⟩
def hi1013b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨24,by decide⟩
def hi1013 : CheckedMoment :=
  CheckedMoment.ofBessel hi1013b1 hi1013b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1013 : meanBracketCheck (99/200) lo1013 hi1013=true := by decide +kernel
def bracket1013 : MeanBracket := meanBracketOfMoments (99/200) lo1013 hi1013 accepted1013
def lo1014b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨28,by decide⟩
def lo1014b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨29,by decide⟩
def lo1014 : CheckedMoment :=
  CheckedMoment.ofBessel lo1014b1 lo1014b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1014b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨33,by decide⟩
def hi1014b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨34,by decide⟩
def hi1014 : CheckedMoment :=
  CheckedMoment.ofBessel hi1014b1 hi1014b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1014 : meanBracketCheck (62/125) lo1014 hi1014=true := by decide +kernel
def bracket1014 : MeanBracket := meanBracketOfMoments (62/125) lo1014 hi1014 accepted1014
def lo1015b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨38,by decide⟩
def lo1015b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨39,by decide⟩
def lo1015 : CheckedMoment :=
  CheckedMoment.ofBessel lo1015b1 lo1015b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1015b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨43,by decide⟩
def hi1015b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨44,by decide⟩
def hi1015 : CheckedMoment :=
  CheckedMoment.ofBessel hi1015b1 hi1015b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1015 : meanBracketCheck (497/1000) lo1015 hi1015=true := by decide +kernel
def bracket1015 : MeanBracket := meanBracketOfMoments (497/1000) lo1015 hi1015 accepted1015
def lo1016b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨48,by decide⟩
def lo1016b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨49,by decide⟩
def lo1016 : CheckedMoment :=
  CheckedMoment.ofBessel lo1016b1 lo1016b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1016b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨53,by decide⟩
def hi1016b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨54,by decide⟩
def hi1016 : CheckedMoment :=
  CheckedMoment.ofBessel hi1016b1 hi1016b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1016 : meanBracketCheck (249/500) lo1016 hi1016=true := by decide +kernel
def bracket1016 : MeanBracket := meanBracketOfMoments (249/500) lo1016 hi1016 accepted1016
def lo1017b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨58,by decide⟩
def lo1017b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨59,by decide⟩
def lo1017 : CheckedMoment :=
  CheckedMoment.ofBessel lo1017b1 lo1017b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1017b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0158.rows BesselBatch0158.accepted ⟨63,by decide⟩
def hi1017b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨0,by decide⟩
def hi1017 : CheckedMoment :=
  CheckedMoment.ofBessel hi1017b1 hi1017b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1017 : meanBracketCheck (499/1000) lo1017 hi1017=true := by decide +kernel
def bracket1017 : MeanBracket := meanBracketOfMoments (499/1000) lo1017 hi1017 accepted1017
def lo1018b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨4,by decide⟩
def lo1018b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨5,by decide⟩
def lo1018 : CheckedMoment :=
  CheckedMoment.ofBessel lo1018b1 lo1018b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1018b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨9,by decide⟩
def hi1018b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨10,by decide⟩
def hi1018 : CheckedMoment :=
  CheckedMoment.ofBessel hi1018b1 hi1018b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1018 : meanBracketCheck (1/2) lo1018 hi1018=true := by decide +kernel
def bracket1018 : MeanBracket := meanBracketOfMoments (1/2) lo1018 hi1018 accepted1018
def lo1019b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨14,by decide⟩
def lo1019b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨15,by decide⟩
def lo1019 : CheckedMoment :=
  CheckedMoment.ofBessel lo1019b1 lo1019b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1019b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨19,by decide⟩
def hi1019b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨20,by decide⟩
def hi1019 : CheckedMoment :=
  CheckedMoment.ofBessel hi1019b1 hi1019b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1019 : meanBracketCheck (501/1000) lo1019 hi1019=true := by decide +kernel
def bracket1019 : MeanBracket := meanBracketOfMoments (501/1000) lo1019 hi1019 accepted1019
def lo1020b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨24,by decide⟩
def lo1020b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨25,by decide⟩
def lo1020 : CheckedMoment :=
  CheckedMoment.ofBessel lo1020b1 lo1020b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1020b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨29,by decide⟩
def hi1020b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨30,by decide⟩
def hi1020 : CheckedMoment :=
  CheckedMoment.ofBessel hi1020b1 hi1020b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1020 : meanBracketCheck (251/500) lo1020 hi1020=true := by decide +kernel
def bracket1020 : MeanBracket := meanBracketOfMoments (251/500) lo1020 hi1020 accepted1020
def lo1021b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨34,by decide⟩
def lo1021b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨35,by decide⟩
def lo1021 : CheckedMoment :=
  CheckedMoment.ofBessel lo1021b1 lo1021b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1021b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨39,by decide⟩
def hi1021b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨40,by decide⟩
def hi1021 : CheckedMoment :=
  CheckedMoment.ofBessel hi1021b1 hi1021b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1021 : meanBracketCheck (503/1000) lo1021 hi1021=true := by decide +kernel
def bracket1021 : MeanBracket := meanBracketOfMoments (503/1000) lo1021 hi1021 accepted1021
def lo1022b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨44,by decide⟩
def lo1022b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨45,by decide⟩
def lo1022 : CheckedMoment :=
  CheckedMoment.ofBessel lo1022b1 lo1022b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1022b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨49,by decide⟩
def hi1022b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨50,by decide⟩
def hi1022 : CheckedMoment :=
  CheckedMoment.ofBessel hi1022b1 hi1022b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1022 : meanBracketCheck (63/125) lo1022 hi1022=true := by decide +kernel
def bracket1022 : MeanBracket := meanBracketOfMoments (63/125) lo1022 hi1022 accepted1022
def lo1023b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨54,by decide⟩
def lo1023b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨55,by decide⟩
def lo1023 : CheckedMoment :=
  CheckedMoment.ofBessel lo1023b1 lo1023b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1023b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨59,by decide⟩
def hi1023b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0159.rows BesselBatch0159.accepted ⟨60,by decide⟩
def hi1023 : CheckedMoment :=
  CheckedMoment.ofBessel hi1023b1 hi1023b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1023 : meanBracketCheck (101/200) lo1023 hi1023=true := by decide +kernel
def bracket1023 : MeanBracket := meanBracketOfMoments (101/200) lo1023 hi1023 accepted1023
#print axioms bracket1008
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0063
