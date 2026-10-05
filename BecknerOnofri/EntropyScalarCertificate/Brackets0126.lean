import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0315
import BecknerOnofri.EntropyScalarCertificate.Bessel0316
import BecknerOnofri.EntropyScalarCertificate.Bessel0317
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0126
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2016b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨0,by decide⟩
def lo2016b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨1,by decide⟩
def lo2016 : CheckedMoment :=
  CheckedMoment.ofBessel lo2016b1 lo2016b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2016b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨5,by decide⟩
def hi2016b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨6,by decide⟩
def hi2016 : CheckedMoment :=
  CheckedMoment.ofBessel hi2016b1 hi2016b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2016 : meanBracketCheck (4769/5000) lo2016 hi2016=true := by decide +kernel
def bracket2016 : MeanBracket := meanBracketOfMoments (4769/5000) lo2016 hi2016 accepted2016
def lo2017b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨10,by decide⟩
def lo2017b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨11,by decide⟩
def lo2017 : CheckedMoment :=
  CheckedMoment.ofBessel lo2017b1 lo2017b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2017b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨15,by decide⟩
def hi2017b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨16,by decide⟩
def hi2017 : CheckedMoment :=
  CheckedMoment.ofBessel hi2017b1 hi2017b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2017 : meanBracketCheck (9539/10000) lo2017 hi2017=true := by decide +kernel
def bracket2017 : MeanBracket := meanBracketOfMoments (9539/10000) lo2017 hi2017 accepted2017
def lo2018b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨20,by decide⟩
def lo2018b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨21,by decide⟩
def lo2018 : CheckedMoment :=
  CheckedMoment.ofBessel lo2018b1 lo2018b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2018b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨25,by decide⟩
def hi2018b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨26,by decide⟩
def hi2018 : CheckedMoment :=
  CheckedMoment.ofBessel hi2018b1 hi2018b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2018 : meanBracketCheck (477/500) lo2018 hi2018=true := by decide +kernel
def bracket2018 : MeanBracket := meanBracketOfMoments (477/500) lo2018 hi2018 accepted2018
def lo2019b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨30,by decide⟩
def lo2019b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨31,by decide⟩
def lo2019 : CheckedMoment :=
  CheckedMoment.ofBessel lo2019b1 lo2019b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2019b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨35,by decide⟩
def hi2019b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨36,by decide⟩
def hi2019 : CheckedMoment :=
  CheckedMoment.ofBessel hi2019b1 hi2019b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2019 : meanBracketCheck (9541/10000) lo2019 hi2019=true := by decide +kernel
def bracket2019 : MeanBracket := meanBracketOfMoments (9541/10000) lo2019 hi2019 accepted2019
def lo2020b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨40,by decide⟩
def lo2020b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨41,by decide⟩
def lo2020 : CheckedMoment :=
  CheckedMoment.ofBessel lo2020b1 lo2020b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2020b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨45,by decide⟩
def hi2020b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨46,by decide⟩
def hi2020 : CheckedMoment :=
  CheckedMoment.ofBessel hi2020b1 hi2020b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2020 : meanBracketCheck (4771/5000) lo2020 hi2020=true := by decide +kernel
def bracket2020 : MeanBracket := meanBracketOfMoments (4771/5000) lo2020 hi2020 accepted2020
def lo2021b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨50,by decide⟩
def lo2021b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨51,by decide⟩
def lo2021 : CheckedMoment :=
  CheckedMoment.ofBessel lo2021b1 lo2021b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2021b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨55,by decide⟩
def hi2021b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨56,by decide⟩
def hi2021 : CheckedMoment :=
  CheckedMoment.ofBessel hi2021b1 hi2021b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2021 : meanBracketCheck (9543/10000) lo2021 hi2021=true := by decide +kernel
def bracket2021 : MeanBracket := meanBracketOfMoments (9543/10000) lo2021 hi2021 accepted2021
def lo2022b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨60,by decide⟩
def lo2022b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨61,by decide⟩
def lo2022 : CheckedMoment :=
  CheckedMoment.ofBessel lo2022b1 lo2022b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2022b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨1,by decide⟩
def hi2022b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨2,by decide⟩
def hi2022 : CheckedMoment :=
  CheckedMoment.ofBessel hi2022b1 hi2022b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2022 : meanBracketCheck (1193/1250) lo2022 hi2022=true := by decide +kernel
def bracket2022 : MeanBracket := meanBracketOfMoments (1193/1250) lo2022 hi2022 accepted2022
def lo2023b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨6,by decide⟩
def lo2023b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨7,by decide⟩
def lo2023 : CheckedMoment :=
  CheckedMoment.ofBessel lo2023b1 lo2023b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2023b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨11,by decide⟩
def hi2023b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨12,by decide⟩
def hi2023 : CheckedMoment :=
  CheckedMoment.ofBessel hi2023b1 hi2023b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2023 : meanBracketCheck (1909/2000) lo2023 hi2023=true := by decide +kernel
def bracket2023 : MeanBracket := meanBracketOfMoments (1909/2000) lo2023 hi2023 accepted2023
def lo2024b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨16,by decide⟩
def lo2024b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨17,by decide⟩
def lo2024 : CheckedMoment :=
  CheckedMoment.ofBessel lo2024b1 lo2024b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2024b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨21,by decide⟩
def hi2024b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨22,by decide⟩
def hi2024 : CheckedMoment :=
  CheckedMoment.ofBessel hi2024b1 hi2024b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2024 : meanBracketCheck (4773/5000) lo2024 hi2024=true := by decide +kernel
def bracket2024 : MeanBracket := meanBracketOfMoments (4773/5000) lo2024 hi2024 accepted2024
def lo2025b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨26,by decide⟩
def lo2025b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨27,by decide⟩
def lo2025 : CheckedMoment :=
  CheckedMoment.ofBessel lo2025b1 lo2025b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2025b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨31,by decide⟩
def hi2025b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨32,by decide⟩
def hi2025 : CheckedMoment :=
  CheckedMoment.ofBessel hi2025b1 hi2025b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2025 : meanBracketCheck (9547/10000) lo2025 hi2025=true := by decide +kernel
def bracket2025 : MeanBracket := meanBracketOfMoments (9547/10000) lo2025 hi2025 accepted2025
def lo2026b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨36,by decide⟩
def lo2026b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨37,by decide⟩
def lo2026 : CheckedMoment :=
  CheckedMoment.ofBessel lo2026b1 lo2026b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2026b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨41,by decide⟩
def hi2026b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨42,by decide⟩
def hi2026 : CheckedMoment :=
  CheckedMoment.ofBessel hi2026b1 hi2026b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2026 : meanBracketCheck (2387/2500) lo2026 hi2026=true := by decide +kernel
def bracket2026 : MeanBracket := meanBracketOfMoments (2387/2500) lo2026 hi2026 accepted2026
def lo2027b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨46,by decide⟩
def lo2027b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨47,by decide⟩
def lo2027 : CheckedMoment :=
  CheckedMoment.ofBessel lo2027b1 lo2027b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2027b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨51,by decide⟩
def hi2027b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨52,by decide⟩
def hi2027 : CheckedMoment :=
  CheckedMoment.ofBessel hi2027b1 hi2027b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2027 : meanBracketCheck (9549/10000) lo2027 hi2027=true := by decide +kernel
def bracket2027 : MeanBracket := meanBracketOfMoments (9549/10000) lo2027 hi2027 accepted2027
def lo2028b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨56,by decide⟩
def lo2028b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨57,by decide⟩
def lo2028 : CheckedMoment :=
  CheckedMoment.ofBessel lo2028b1 lo2028b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2028b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨61,by decide⟩
def hi2028b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0316.rows BesselBatch0316.accepted ⟨62,by decide⟩
def hi2028 : CheckedMoment :=
  CheckedMoment.ofBessel hi2028b1 hi2028b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2028 : meanBracketCheck (191/200) lo2028 hi2028=true := by decide +kernel
def bracket2028 : MeanBracket := meanBracketOfMoments (191/200) lo2028 hi2028 accepted2028
def lo2029b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨2,by decide⟩
def lo2029b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨3,by decide⟩
def lo2029 : CheckedMoment :=
  CheckedMoment.ofBessel lo2029b1 lo2029b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2029b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨7,by decide⟩
def hi2029b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨8,by decide⟩
def hi2029 : CheckedMoment :=
  CheckedMoment.ofBessel hi2029b1 hi2029b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2029 : meanBracketCheck (9551/10000) lo2029 hi2029=true := by decide +kernel
def bracket2029 : MeanBracket := meanBracketOfMoments (9551/10000) lo2029 hi2029 accepted2029
def lo2030b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨12,by decide⟩
def lo2030b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨13,by decide⟩
def lo2030 : CheckedMoment :=
  CheckedMoment.ofBessel lo2030b1 lo2030b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2030b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨17,by decide⟩
def hi2030b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨18,by decide⟩
def hi2030 : CheckedMoment :=
  CheckedMoment.ofBessel hi2030b1 hi2030b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2030 : meanBracketCheck (597/625) lo2030 hi2030=true := by decide +kernel
def bracket2030 : MeanBracket := meanBracketOfMoments (597/625) lo2030 hi2030 accepted2030
def lo2031b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨22,by decide⟩
def lo2031b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨23,by decide⟩
def lo2031 : CheckedMoment :=
  CheckedMoment.ofBessel lo2031b1 lo2031b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2031b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨27,by decide⟩
def hi2031b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨28,by decide⟩
def hi2031 : CheckedMoment :=
  CheckedMoment.ofBessel hi2031b1 hi2031b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2031 : meanBracketCheck (9553/10000) lo2031 hi2031=true := by decide +kernel
def bracket2031 : MeanBracket := meanBracketOfMoments (9553/10000) lo2031 hi2031 accepted2031
#print axioms bracket2016
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0126
