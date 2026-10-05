module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0465
public import BecknerOnofri.EntropyScalarCertificate.Bessel0466
public import BecknerOnofri.EntropyScalarCertificate.Bessel0721
public import BecknerOnofri.EntropyScalarCertificate.Bessel0722
public import BecknerOnofri.EntropyScalarCertificate.Brackets0186
public import BecknerOnofri.EntropyScalarCertificate.Logs0372
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2976
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (1421707860069929453283133202675821119201019/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1421707860069929453283133202675821119201019/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (285150945931722540101049335378154354979699/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (285150945931722540101049335378154354979699/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (1423731294864271076894189939783296447049757/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1423731294864271076894189939783296447049757/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨7,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨15,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0186.bracket2976 BracketBatch0186.bracket2977 (1423731294864271076894189939783296447049757/10000000000000000000000000000000000000000) (6654943411557538732599509451668670497489/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0186.bracket2976 BracketBatch0186.bracket2977
  (1423731294864271076894189939783296447049757/10000000000000000000000000000000000000000) (6654943411557538732599509451668670497489/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2976
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2977
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (356438682414653175126311669222692943724623/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (356438682414653175126311669222692943724623/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (1429824724270659992078284423600065377614799/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1429824724270659992078284423600065377614799/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (2855579453929272692583531100490837152513291/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2855579453929272692583531100490837152513291/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨23,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨31,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0186.bracket2977 BracketBatch0186.bracket2978 (2855579453929272692583531100490837152513291/20000000000000000000000000000000000000000) (6659304667054407578864235730245739468063/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0186.bracket2977 BracketBatch0186.bracket2978
  (2855579453929272692583531100490837152513291/20000000000000000000000000000000000000000) (6659304667054407578864235730245739468063/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2977
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2978
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (357456181067664998019571105900016344403699/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (357456181067664998019571105900016344403699/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (358479510672126263496534191595048231924331/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (358479510672126263496534191595048231924331/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (71593569173979126151610529749506457632803/500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (71593569173979126151610529749506457632803/500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨39,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨47,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0186.bracket2978 BracketBatch0186.bracket2979 (71593569173979126151610529749506457632803/500000000000000000000000000000000000000) (33318389668842275629482224766316699419/50000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0186.bracket2978 BracketBatch0186.bracket2979
  (71593569173979126151610529749506457632803/500000000000000000000000000000000000000) (33318389668842275629482224766316699419/50000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2978
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2979
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (1433918042688505053986136766380192927697321/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1433918042688505053986136766380192927697321/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (1438034885979437172437655259606129576699519/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1438034885979437172437655259606129576699519/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (71798823216698555660594800649658062609921/500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (71798823216698555660594800649658062609921/500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨55,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨63,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0186.bracket2979 BracketBatch0186.bracket2980 (71798823216698555660594800649658062609921/500000000000000000000000000000000000000) (6668063272154949159152623814243104017883/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0186.bracket2979 BracketBatch0186.bracket2980
  (71798823216698555660594800649658062609921/500000000000000000000000000000000000000) (6668063272154949159152623814243104017883/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2979
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2980
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (359508721494859293109413814901532394174879/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (359508721494859293109413814901532394174879/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (72108772876426209232398623039243884758341/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (72108772876426209232398623039243884758341/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (90006573234623792408925866262218977245823/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (90006573234623792408925866262218977245823/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨71,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨79,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0186.bracket2980 BracketBatch0186.bracket2981 (90006573234623792408925866262218977245823/625000000000000000000000000000000000000) (6672460743070671773897513193684831663057/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0186.bracket2980 BracketBatch0186.bracket2981
  (90006573234623792408925866262218977245823/625000000000000000000000000000000000000) (6672460743070671773897513193684831663057/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2980
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2981
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (1442175457528524184647972460784877695166817/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1442175457528524184647972460784877695166817/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (180792495384013298566888088553889753110551/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (180792495384013298566888088553889753110551/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (115540616824025222927323086768639828802049/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (115540616824025222927323086768639828802049/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨87,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨95,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0186.bracket2981 BracketBatch0186.bracket2982 (115540616824025222927323086768639828802049/800000000000000000000000000000000000000) (1335374081555302363898057600519078357657/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0186.bracket2981 BracketBatch0186.bracket2982
  (115540616824025222927323086768639828802049/800000000000000000000000000000000000000) (1335374081555302363898057600519078357657/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2981
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2982
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0465.rows BesselBatch0465.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (289267992614421277707020941686223604976881/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (289267992614421277707020941686223604976881/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (725264305365936477596943562943154701082041/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (725264305365936477596943562943154701082041/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (2896868573803979343728991834317427427048487/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2896868573803979343728991834317427427048487/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨103,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨111,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0186.bracket2982 BracketBatch0186.bracket2983 (2896868573803979343728991834317427427048487/20000000000000000000000000000000000000000) (6681292327940054173447712029594363391519/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0186.bracket2982 BracketBatch0186.bracket2983
  (2896868573803979343728991834317427427048487/20000000000000000000000000000000000000000) (6681292327940054173447712029594363391519/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2982
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2983
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (1450528610731872955193887125886309402164079/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1450528610731872955193887125886309402164079/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0466.rows BesselBatch0466.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (727370805524766348700715375513397543833381/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (727370805524766348700715375513397543833381/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0721.rows BesselBatch0721.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0722.rows BesselBatch0722.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (2905270221781405652595317876913104489830841/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2905270221781405652595317876913104489830841/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨119,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0372.rows ScalarLogs0372.accepted ⟨127,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0186.bracket2983 BracketBatch0186.bracket2984 (2905270221781405652595317876913104489830841/20000000000000000000000000000000000000000) (3342863282819082428892100707116322476629/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0186.bracket2983 BracketBatch0186.bracket2984
  (2905270221781405652595317876913104489830841/20000000000000000000000000000000000000000) (3342863282819082428892100707116322476629/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2983
