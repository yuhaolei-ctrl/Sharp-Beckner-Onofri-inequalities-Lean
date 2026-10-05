import BecknerOnofri.EntropyScalarCertificate.Bessel0048
import BecknerOnofri.EntropyScalarCertificate.Bessel0049
import BecknerOnofri.EntropyScalarCertificate.Bessel0050
import BecknerOnofri.EntropyScalarCertificate.Bessel0513
import BecknerOnofri.EntropyScalarCertificate.Brackets0019
import BecknerOnofri.EntropyScalarCertificate.Brackets0020
import BecknerOnofri.EntropyScalarCertificate.Logs0039
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0312
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (59875246730584779675361152668527141867/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (59875246730584779675361152668527141867/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (1199548269210696018361848718347258009551/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1199548269210696018361848718347258009551/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (2397053203822391611869071771717800846891/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2397053203822391611869071771717800846891/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0019.bracket0312 BracketBatch0019.bracket0313 (2397053203822391611869071771717800846891/20000000000000000000000000000000000000000) (31235244570261509477511248753025019/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0019.bracket0312 BracketBatch0019.bracket0313
  (2397053203822391611869071771717800846891/20000000000000000000000000000000000000000) (31235244570261509477511248753025019/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0312
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0313
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0048.rows BesselBatch0048.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (299887067302674004590462179586814502387/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (299887067302674004590462179586814502387/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (1201591752524412633051883474405765245003/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1201591752524412633051883474405765245003/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (2401140021735108651413732192753023254551/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2401140021735108651413732192753023254551/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0019.bracket0313 BracketBatch0019.bracket0314 (2401140021735108651413732192753023254551/20000000000000000000000000000000000000000) (9827218462199263001910340815138043/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0019.bracket0313 BracketBatch0019.bracket0314
  (2401140021735108651413732192753023254551/20000000000000000000000000000000000000000) (9827218462199263001910340815138043/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0313
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0314
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (240318350504882526610376694881153049/2000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (240318350504882526610376694881153049/2000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (601817692411326290440300097964021348963/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (601817692411326290440300097964021348963/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (1202613568673532606966241835166903971463/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1202613568673532606966241835166903971463/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0019.bracket0314 BracketBatch0019.bracket0315 (1202613568673532606966241835166903971463/10000000000000000000000000000000000000000) (158300148947226824614979305118454781/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0019.bracket0314 BracketBatch0019.bracket0315
  (1202613568673532606966241835166903971463/10000000000000000000000000000000000000000) (158300148947226824614979305118454781/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0314
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0315
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (1203635384822652580880600195928042697923/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1203635384822652580880600195928042697923/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (602839583187663980544541473241695294903/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (602839583187663980544541473241695294903/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (2409314551197980541969683142411433287729/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2409314551197980541969683142411433287729/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0019.bracket0315 BracketBatch0019.bracket0316 (2409314551197980541969683142411433287729/20000000000000000000000000000000000000000) (159370201857338490994671702741071709/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0019.bracket0315 BracketBatch0019.bracket0316
  (2409314551197980541969683142411433287729/20000000000000000000000000000000000000000) (159370201857338490994671702741071709/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0315
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0316
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (1205679166375327961089082946483390589803/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1205679166375327961089082946483390589803/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (1207723097452456038488344846287859789423/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1207723097452456038488344846287859789423/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (1206701131913891999788713896385625189613/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1206701131913891999788713896385625189613/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0019.bracket0316 BracketBatch0019.bracket0317 (1206701131913891999788713896385625189613/10000000000000000000000000000000000000000) (20055709063501652175854493450914343/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0019.bracket0316 BracketBatch0019.bracket0317
  (1206701131913891999788713896385625189613/10000000000000000000000000000000000000000) (20055709063501652175854493450914343/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0316
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0317
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (60386154872622801924417242314392989471/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (60386154872622801924417242314392989471/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (604883589162079726636254561794039410097/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (604883589162079726636254561794039410097/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (1208745137888307745880426984937969304807/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1208745137888307745880426984937969304807/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0019.bracket0317 BracketBatch0019.bracket0318 (1208745137888307745880426984937969304807/10000000000000000000000000000000000000000) (40381644828581298329422790065966993/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0019.bracket0317 BracketBatch0019.bracket0318
  (1208745137888307745880426984937969304807/10000000000000000000000000000000000000000) (40381644828581298329422790065966993/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0317
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0318
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (1209767178324159453272509123588078820191/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1209767178324159453272509123588078820191/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (4733638317424478246146328027880399313/39062500000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4733638317424478246146328027880399313/39062500000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (2421578587584825884285969098725461044319/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2421578587584825884285969098725461044319/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0019.bracket0318 BracketBatch0019.bracket0319 (2421578587584825884285969098725461044319/20000000000000000000000000000000000000000) (81306470361971034109677250783341671/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0019.bracket0318 BracketBatch0019.bracket0319
  (2421578587584825884285969098725461044319/20000000000000000000000000000000000000000) (81306470361971034109677250783341671/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0318
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0319
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0049.rows BesselBatch0049.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (9694491274085331448107679801099057793/80000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9694491274085331448107679801099057793/80000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (1213855790532310992837370437335674943547/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1213855790532310992837370437335674943547/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (303208399974122177981353801559132145959/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (303208399974122177981353801559132145959/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0039.rows ScalarLogs0039.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0019.bracket0319 BracketBatch0020.bracket0320 (303208399974122177981353801559132145959/2500000000000000000000000000000000000000) (163704775217134250390965624992599221/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0019.bracket0319 BracketBatch0020.bracket0320
  (303208399974122177981353801559132145959/2500000000000000000000000000000000000000) (163704775217134250390965624992599221/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0319
