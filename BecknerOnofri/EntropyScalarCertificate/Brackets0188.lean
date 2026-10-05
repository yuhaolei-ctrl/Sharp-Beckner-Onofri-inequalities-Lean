module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0470
public import BecknerOnofri.EntropyScalarCertificate.Bessel0471
public import BecknerOnofri.EntropyScalarCertificate.Bessel0472

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0188
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo3008b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨0,by decide⟩
def lo3008b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨1,by decide⟩
def lo3008 : CheckedMoment :=
  CheckedMoment.ofBessel lo3008b1 lo3008b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3008b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨5,by decide⟩
def hi3008b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨6,by decide⟩
def hi3008 : CheckedMoment :=
  CheckedMoment.ofBessel hi3008b1 hi3008b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3008 : meanBracketCheck (624/625) lo3008 hi3008=true := by decide +kernel
def bracket3008 : MeanBracket := meanBracketOfMoments (624/625) lo3008 hi3008 accepted3008
def lo3009b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨10,by decide⟩
def lo3009b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨11,by decide⟩
def lo3009 : CheckedMoment :=
  CheckedMoment.ofBessel lo3009b1 lo3009b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3009b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨15,by decide⟩
def hi3009b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨16,by decide⟩
def hi3009 : CheckedMoment :=
  CheckedMoment.ofBessel hi3009b1 hi3009b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3009 : meanBracketCheck (199681/200000) lo3009 hi3009=true := by decide +kernel
def bracket3009 : MeanBracket := meanBracketOfMoments (199681/200000) lo3009 hi3009 accepted3009
def lo3010b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨20,by decide⟩
def lo3010b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨21,by decide⟩
def lo3010 : CheckedMoment :=
  CheckedMoment.ofBessel lo3010b1 lo3010b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3010b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨25,by decide⟩
def hi3010b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨26,by decide⟩
def hi3010 : CheckedMoment :=
  CheckedMoment.ofBessel hi3010b1 hi3010b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3010 : meanBracketCheck (99841/100000) lo3010 hi3010=true := by decide +kernel
def bracket3010 : MeanBracket := meanBracketOfMoments (99841/100000) lo3010 hi3010 accepted3010
def lo3011b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨30,by decide⟩
def lo3011b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨31,by decide⟩
def lo3011 : CheckedMoment :=
  CheckedMoment.ofBessel lo3011b1 lo3011b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3011b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨35,by decide⟩
def hi3011b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨36,by decide⟩
def hi3011 : CheckedMoment :=
  CheckedMoment.ofBessel hi3011b1 hi3011b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3011 : meanBracketCheck (199683/200000) lo3011 hi3011=true := by decide +kernel
def bracket3011 : MeanBracket := meanBracketOfMoments (199683/200000) lo3011 hi3011 accepted3011
def lo3012b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨40,by decide⟩
def lo3012b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨41,by decide⟩
def lo3012 : CheckedMoment :=
  CheckedMoment.ofBessel lo3012b1 lo3012b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3012b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨45,by decide⟩
def hi3012b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨46,by decide⟩
def hi3012 : CheckedMoment :=
  CheckedMoment.ofBessel hi3012b1 hi3012b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3012 : meanBracketCheck (49921/50000) lo3012 hi3012=true := by decide +kernel
def bracket3012 : MeanBracket := meanBracketOfMoments (49921/50000) lo3012 hi3012 accepted3012
def lo3013b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨50,by decide⟩
def lo3013b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨51,by decide⟩
def lo3013 : CheckedMoment :=
  CheckedMoment.ofBessel lo3013b1 lo3013b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3013b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨55,by decide⟩
def hi3013b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨56,by decide⟩
def hi3013 : CheckedMoment :=
  CheckedMoment.ofBessel hi3013b1 hi3013b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3013 : meanBracketCheck (39937/40000) lo3013 hi3013=true := by decide +kernel
def bracket3013 : MeanBracket := meanBracketOfMoments (39937/40000) lo3013 hi3013 accepted3013
def lo3014b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨60,by decide⟩
def lo3014b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨61,by decide⟩
def lo3014 : CheckedMoment :=
  CheckedMoment.ofBessel lo3014b1 lo3014b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3014b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨1,by decide⟩
def hi3014b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨2,by decide⟩
def hi3014 : CheckedMoment :=
  CheckedMoment.ofBessel hi3014b1 hi3014b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3014 : meanBracketCheck (99843/100000) lo3014 hi3014=true := by decide +kernel
def bracket3014 : MeanBracket := meanBracketOfMoments (99843/100000) lo3014 hi3014 accepted3014
def lo3015b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨6,by decide⟩
def lo3015b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨7,by decide⟩
def lo3015 : CheckedMoment :=
  CheckedMoment.ofBessel lo3015b1 lo3015b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3015b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨11,by decide⟩
def hi3015b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨12,by decide⟩
def hi3015 : CheckedMoment :=
  CheckedMoment.ofBessel hi3015b1 hi3015b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3015 : meanBracketCheck (199687/200000) lo3015 hi3015=true := by decide +kernel
def bracket3015 : MeanBracket := meanBracketOfMoments (199687/200000) lo3015 hi3015 accepted3015
def lo3016b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨16,by decide⟩
def lo3016b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨17,by decide⟩
def lo3016 : CheckedMoment :=
  CheckedMoment.ofBessel lo3016b1 lo3016b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3016b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨21,by decide⟩
def hi3016b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨22,by decide⟩
def hi3016 : CheckedMoment :=
  CheckedMoment.ofBessel hi3016b1 hi3016b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3016 : meanBracketCheck (24961/25000) lo3016 hi3016=true := by decide +kernel
def bracket3016 : MeanBracket := meanBracketOfMoments (24961/25000) lo3016 hi3016 accepted3016
def lo3017b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨26,by decide⟩
def lo3017b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨27,by decide⟩
def lo3017 : CheckedMoment :=
  CheckedMoment.ofBessel lo3017b1 lo3017b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3017b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨31,by decide⟩
def hi3017b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨32,by decide⟩
def hi3017 : CheckedMoment :=
  CheckedMoment.ofBessel hi3017b1 hi3017b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3017 : meanBracketCheck (199689/200000) lo3017 hi3017=true := by decide +kernel
def bracket3017 : MeanBracket := meanBracketOfMoments (199689/200000) lo3017 hi3017 accepted3017
def lo3018b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨36,by decide⟩
def lo3018b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨37,by decide⟩
def lo3018 : CheckedMoment :=
  CheckedMoment.ofBessel lo3018b1 lo3018b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3018b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨41,by decide⟩
def hi3018b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨42,by decide⟩
def hi3018 : CheckedMoment :=
  CheckedMoment.ofBessel hi3018b1 hi3018b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3018 : meanBracketCheck (19969/20000) lo3018 hi3018=true := by decide +kernel
def bracket3018 : MeanBracket := meanBracketOfMoments (19969/20000) lo3018 hi3018 accepted3018
def lo3019b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨46,by decide⟩
def lo3019b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨47,by decide⟩
def lo3019 : CheckedMoment :=
  CheckedMoment.ofBessel lo3019b1 lo3019b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3019b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨51,by decide⟩
def hi3019b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨52,by decide⟩
def hi3019 : CheckedMoment :=
  CheckedMoment.ofBessel hi3019b1 hi3019b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3019 : meanBracketCheck (199691/200000) lo3019 hi3019=true := by decide +kernel
def bracket3019 : MeanBracket := meanBracketOfMoments (199691/200000) lo3019 hi3019 accepted3019
def lo3020b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨56,by decide⟩
def lo3020b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨57,by decide⟩
def lo3020 : CheckedMoment :=
  CheckedMoment.ofBessel lo3020b1 lo3020b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3020b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨61,by decide⟩
def hi3020b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨62,by decide⟩
def hi3020 : CheckedMoment :=
  CheckedMoment.ofBessel hi3020b1 hi3020b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3020 : meanBracketCheck (49923/50000) lo3020 hi3020=true := by decide +kernel
def bracket3020 : MeanBracket := meanBracketOfMoments (49923/50000) lo3020 hi3020 accepted3020
def lo3021b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨2,by decide⟩
def lo3021b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨3,by decide⟩
def lo3021 : CheckedMoment :=
  CheckedMoment.ofBessel lo3021b1 lo3021b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3021b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨7,by decide⟩
def hi3021b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨8,by decide⟩
def hi3021 : CheckedMoment :=
  CheckedMoment.ofBessel hi3021b1 hi3021b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3021 : meanBracketCheck (199693/200000) lo3021 hi3021=true := by decide +kernel
def bracket3021 : MeanBracket := meanBracketOfMoments (199693/200000) lo3021 hi3021 accepted3021
def lo3022b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨12,by decide⟩
def lo3022b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨13,by decide⟩
def lo3022 : CheckedMoment :=
  CheckedMoment.ofBessel lo3022b1 lo3022b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3022b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨17,by decide⟩
def hi3022b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨18,by decide⟩
def hi3022 : CheckedMoment :=
  CheckedMoment.ofBessel hi3022b1 hi3022b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3022 : meanBracketCheck (99847/100000) lo3022 hi3022=true := by decide +kernel
def bracket3022 : MeanBracket := meanBracketOfMoments (99847/100000) lo3022 hi3022 accepted3022
def lo3023b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨22,by decide⟩
def lo3023b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨23,by decide⟩
def lo3023 : CheckedMoment :=
  CheckedMoment.ofBessel lo3023b1 lo3023b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi3023b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨27,by decide⟩
def hi3023b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0472.rows BesselBatch0472.accepted ⟨28,by decide⟩
def hi3023 : CheckedMoment :=
  CheckedMoment.ofBessel hi3023b1 hi3023b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted3023 : meanBracketCheck (39939/40000) lo3023 hi3023=true := by decide +kernel
def bracket3023 : MeanBracket := meanBracketOfMoments (39939/40000) lo3023 hi3023 accepted3023
#print axioms bracket3008
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0188
