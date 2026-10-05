module

public import BecknerOnofri.ScalarCheckedBessel
public import BecknerOnofri.EntropyScalarCertificate.Bessel0002
public import BecknerOnofri.EntropyScalarCertificate.Bessel0003
public import BecknerOnofri.EntropyScalarCertificate.Bessel0004

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0001
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0016b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨32,by decide⟩
def lo0016b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨33,by decide⟩
def lo0016 : CheckedMoment :=
  CheckedMoment.ofBessel lo0016b1 lo0016b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0016b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨37,by decide⟩
def hi0016b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨38,by decide⟩
def hi0016 : CheckedMoment :=
  CheckedMoment.ofBessel hi0016b1 hi0016b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0016 : meanBracketCheck (633/10000) lo0016 hi0016=true := by decide +kernel
def bracket0016 : MeanBracket := meanBracketOfMoments (633/10000) lo0016 hi0016 accepted0016
def lo0017b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨42,by decide⟩
def lo0017b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨43,by decide⟩
def lo0017 : CheckedMoment :=
  CheckedMoment.ofBessel lo0017b1 lo0017b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0017b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨47,by decide⟩
def hi0017b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨48,by decide⟩
def hi0017 : CheckedMoment :=
  CheckedMoment.ofBessel hi0017b1 hi0017b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0017 : meanBracketCheck (1267/20000) lo0017 hi0017=true := by decide +kernel
def bracket0017 : MeanBracket := meanBracketOfMoments (1267/20000) lo0017 hi0017 accepted0017
def lo0018b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨52,by decide⟩
def lo0018b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨53,by decide⟩
def lo0018 : CheckedMoment :=
  CheckedMoment.ofBessel lo0018b1 lo0018b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0018b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨57,by decide⟩
def hi0018b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨58,by decide⟩
def hi0018 : CheckedMoment :=
  CheckedMoment.ofBessel hi0018b1 hi0018b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0018 : meanBracketCheck (317/5000) lo0018 hi0018=true := by decide +kernel
def bracket0018 : MeanBracket := meanBracketOfMoments (317/5000) lo0018 hi0018 accepted0018
def lo0019b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨62,by decide⟩
def lo0019b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨63,by decide⟩
def lo0019 : CheckedMoment :=
  CheckedMoment.ofBessel lo0019b1 lo0019b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0019b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨3,by decide⟩
def hi0019b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨4,by decide⟩
def hi0019 : CheckedMoment :=
  CheckedMoment.ofBessel hi0019b1 hi0019b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0019 : meanBracketCheck (1269/20000) lo0019 hi0019=true := by decide +kernel
def bracket0019 : MeanBracket := meanBracketOfMoments (1269/20000) lo0019 hi0019 accepted0019
def lo0020b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨8,by decide⟩
def lo0020b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨9,by decide⟩
def lo0020 : CheckedMoment :=
  CheckedMoment.ofBessel lo0020b1 lo0020b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0020b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨13,by decide⟩
def hi0020b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨14,by decide⟩
def hi0020 : CheckedMoment :=
  CheckedMoment.ofBessel hi0020b1 hi0020b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0020 : meanBracketCheck (127/2000) lo0020 hi0020=true := by decide +kernel
def bracket0020 : MeanBracket := meanBracketOfMoments (127/2000) lo0020 hi0020 accepted0020
def lo0021b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨18,by decide⟩
def lo0021b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨19,by decide⟩
def lo0021 : CheckedMoment :=
  CheckedMoment.ofBessel lo0021b1 lo0021b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0021b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨23,by decide⟩
def hi0021b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨24,by decide⟩
def hi0021 : CheckedMoment :=
  CheckedMoment.ofBessel hi0021b1 hi0021b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0021 : meanBracketCheck (1271/20000) lo0021 hi0021=true := by decide +kernel
def bracket0021 : MeanBracket := meanBracketOfMoments (1271/20000) lo0021 hi0021 accepted0021
def lo0022b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨28,by decide⟩
def lo0022b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨29,by decide⟩
def lo0022 : CheckedMoment :=
  CheckedMoment.ofBessel lo0022b1 lo0022b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0022b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨33,by decide⟩
def hi0022b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨34,by decide⟩
def hi0022 : CheckedMoment :=
  CheckedMoment.ofBessel hi0022b1 hi0022b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0022 : meanBracketCheck (159/2500) lo0022 hi0022=true := by decide +kernel
def bracket0022 : MeanBracket := meanBracketOfMoments (159/2500) lo0022 hi0022 accepted0022
def lo0023b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨38,by decide⟩
def lo0023b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨39,by decide⟩
def lo0023 : CheckedMoment :=
  CheckedMoment.ofBessel lo0023b1 lo0023b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0023b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨43,by decide⟩
def hi0023b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨44,by decide⟩
def hi0023 : CheckedMoment :=
  CheckedMoment.ofBessel hi0023b1 hi0023b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0023 : meanBracketCheck (1273/20000) lo0023 hi0023=true := by decide +kernel
def bracket0023 : MeanBracket := meanBracketOfMoments (1273/20000) lo0023 hi0023 accepted0023
def lo0024b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨48,by decide⟩
def lo0024b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨49,by decide⟩
def lo0024 : CheckedMoment :=
  CheckedMoment.ofBessel lo0024b1 lo0024b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0024b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨53,by decide⟩
def hi0024b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨54,by decide⟩
def hi0024 : CheckedMoment :=
  CheckedMoment.ofBessel hi0024b1 hi0024b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0024 : meanBracketCheck (637/10000) lo0024 hi0024=true := by decide +kernel
def bracket0024 : MeanBracket := meanBracketOfMoments (637/10000) lo0024 hi0024 accepted0024
def lo0025b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨58,by decide⟩
def lo0025b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨59,by decide⟩
def lo0025 : CheckedMoment :=
  CheckedMoment.ofBessel lo0025b1 lo0025b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0025b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨63,by decide⟩
def hi0025b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨0,by decide⟩
def hi0025 : CheckedMoment :=
  CheckedMoment.ofBessel hi0025b1 hi0025b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0025 : meanBracketCheck (51/800) lo0025 hi0025=true := by decide +kernel
def bracket0025 : MeanBracket := meanBracketOfMoments (51/800) lo0025 hi0025 accepted0025
def lo0026b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨4,by decide⟩
def lo0026b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨5,by decide⟩
def lo0026 : CheckedMoment :=
  CheckedMoment.ofBessel lo0026b1 lo0026b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0026b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨9,by decide⟩
def hi0026b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨10,by decide⟩
def hi0026 : CheckedMoment :=
  CheckedMoment.ofBessel hi0026b1 hi0026b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0026 : meanBracketCheck (319/5000) lo0026 hi0026=true := by decide +kernel
def bracket0026 : MeanBracket := meanBracketOfMoments (319/5000) lo0026 hi0026 accepted0026
def lo0027b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨14,by decide⟩
def lo0027b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨15,by decide⟩
def lo0027 : CheckedMoment :=
  CheckedMoment.ofBessel lo0027b1 lo0027b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0027b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨19,by decide⟩
def hi0027b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨20,by decide⟩
def hi0027 : CheckedMoment :=
  CheckedMoment.ofBessel hi0027b1 hi0027b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0027 : meanBracketCheck (1277/20000) lo0027 hi0027=true := by decide +kernel
def bracket0027 : MeanBracket := meanBracketOfMoments (1277/20000) lo0027 hi0027 accepted0027
def lo0028b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨24,by decide⟩
def lo0028b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨25,by decide⟩
def lo0028 : CheckedMoment :=
  CheckedMoment.ofBessel lo0028b1 lo0028b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0028b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨29,by decide⟩
def hi0028b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨30,by decide⟩
def hi0028 : CheckedMoment :=
  CheckedMoment.ofBessel hi0028b1 hi0028b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0028 : meanBracketCheck (639/10000) lo0028 hi0028=true := by decide +kernel
def bracket0028 : MeanBracket := meanBracketOfMoments (639/10000) lo0028 hi0028 accepted0028
def lo0029b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨34,by decide⟩
def lo0029b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨35,by decide⟩
def lo0029 : CheckedMoment :=
  CheckedMoment.ofBessel lo0029b1 lo0029b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0029b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨39,by decide⟩
def hi0029b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨40,by decide⟩
def hi0029 : CheckedMoment :=
  CheckedMoment.ofBessel hi0029b1 hi0029b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0029 : meanBracketCheck (1279/20000) lo0029 hi0029=true := by decide +kernel
def bracket0029 : MeanBracket := meanBracketOfMoments (1279/20000) lo0029 hi0029 accepted0029
def lo0030b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨44,by decide⟩
def lo0030b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨45,by decide⟩
def lo0030 : CheckedMoment :=
  CheckedMoment.ofBessel lo0030b1 lo0030b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0030b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨49,by decide⟩
def hi0030b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨50,by decide⟩
def hi0030 : CheckedMoment :=
  CheckedMoment.ofBessel hi0030b1 hi0030b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0030 : meanBracketCheck (8/125) lo0030 hi0030=true := by decide +kernel
def bracket0030 : MeanBracket := meanBracketOfMoments (8/125) lo0030 hi0030 accepted0030
def lo0031b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨54,by decide⟩
def lo0031b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨55,by decide⟩
def lo0031 : CheckedMoment :=
  CheckedMoment.ofBessel lo0031b1 lo0031b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0031b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨59,by decide⟩
def hi0031b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨60,by decide⟩
def hi0031 : CheckedMoment :=
  CheckedMoment.ofBessel hi0031b1 hi0031b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0031 : meanBracketCheck (1281/20000) lo0031 hi0031=true := by decide +kernel
def bracket0031 : MeanBracket := meanBracketOfMoments (1281/20000) lo0031 hi0031 accepted0031
#print axioms bracket0016
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0001
