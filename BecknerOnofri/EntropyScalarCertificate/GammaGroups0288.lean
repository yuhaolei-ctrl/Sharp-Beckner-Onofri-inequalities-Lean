import BecknerOnofri.EntropyScalarCertificate.Bessel0360
import BecknerOnofri.EntropyScalarCertificate.Bessel0361
import BecknerOnofri.EntropyScalarCertificate.Bessel0668
import BecknerOnofri.EntropyScalarCertificate.Bessel0669
import BecknerOnofri.EntropyScalarCertificate.Brackets0144
import BecknerOnofri.EntropyScalarCertificate.Logs0288
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2304
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (144962305270257916066631358259054944084367/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (144962305270257916066631358259054944084367/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (145792609332432221243880602522122721539913/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (145792609332432221243880602522122721539913/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (7268872865067253432762799019529441640607/500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7268872865067253432762799019529441640607/500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0144.bracket2304 BracketBatch0144.bracket2305 (7268872865067253432762799019529441640607/500000000000000000000000000000000000000) (814849735551212086378427381344715549483/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0144.bracket2304 BracketBatch0144.bracket2305
  (7268872865067253432762799019529441640607/500000000000000000000000000000000000000) (814849735551212086378427381344715549483/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2304
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2305
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (14579260933243222124388060252212272153991/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (14579260933243222124388060252212272153991/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (73316285299239461193275164296000543797207/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (73316285299239461193275164296000543797207/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (73106294982727785907607732778530952283581/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (73106294982727785907607732778530952283581/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0144.bracket2305 BracketBatch0144.bracket2306 (73106294982727785907607732778530952283581/5000000000000000000000000000000000000000) (1633531061420878771364865120144004485297/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0144.bracket2305 BracketBatch0144.bracket2306
  (73106294982727785907607732778530952283581/5000000000000000000000000000000000000000) (1633531061420878771364865120144004485297/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2305
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2306
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (146632570598478922386550328592001087594411/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (146632570598478922386550328592001087594411/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (147482358490849294477863155829118142811963/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (147482358490849294477863155829118142811963/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (147057464544664108432206742210559615203187/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (147057464544664108432206742210559615203187/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0144.bracket2306 BracketBatch0144.bracket2307 (147057464544664108432206742210559615203187/10000000000000000000000000000000000000000) (3274770399299606517317254566105462072721/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0144.bracket2306 BracketBatch0144.bracket2307
  (147057464544664108432206742210559615203187/10000000000000000000000000000000000000000) (3274770399299606517317254566105462072721/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2306
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2307
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (3687058962271232361946578895727953570299/250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3687058962271232361946578895727953570299/250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (74171073209204588465831283657184125759147/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (74171073209204588465831283657184125759147/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (147912252454629235704762861571743197165127/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (147912252454629235704762861571743197165127/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0144.bracket2307 BracketBatch0144.bracket2308 (147912252454629235704762861571743197165127/10000000000000000000000000000000000000000) (820631058531870526431985531174672908163/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0144.bracket2307 BracketBatch0144.bracket2308
  (147912252454629235704762861571743197165127/10000000000000000000000000000000000000000) (820631058531870526431985531174672908163/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2307
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2308
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (148342146418409176931662567314368251518291/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (148342146418409176931662567314368251518291/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (149212111894380220397823126189538785566491/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (149212111894380220397823126189538785566491/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (148777129156394698664742846751953518542391/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (148777129156394698664742846751953518542391/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0144.bracket2308 BracketBatch0144.bracket2309 (148777129156394698664742846751953518542391/10000000000000000000000000000000000000000) (658064819130632020150638106356180383579/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0144.bracket2308 BracketBatch0144.bracket2309
  (148777129156394698664742846751953518542391/10000000000000000000000000000000000000000) (658064819130632020150638106356180383579/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2308
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2309
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (18651513986797527549727890773692348195811/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18651513986797527549727890773692348195811/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (18761554582311665126888319832300289024697/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18761554582311665126888319832300289024697/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (9353267142277298169154052651498159305127/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9353267142277298169154052651498159305127/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0144.bracket2309 BracketBatch0144.bracket2310 (9353267142277298169154052651498159305127/625000000000000000000000000000000000000) (659634091605708902847976285879065613161/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0144.bracket2309 BracketBatch0144.bracket2310
  (9353267142277298169154052651498159305127/625000000000000000000000000000000000000) (659634091605708902847976285879065613161/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2309
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2310
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (150092436658493321015106558658402312197573/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (150092436658493321015106558658402312197573/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (7549165340176540043315370788986699353303/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7549165340176540043315370788986699353303/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (301075743462024121881413974438136299263633/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (301075743462024121881413974438136299263633/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0144.bracket2310 BracketBatch0144.bracket2311 (301075743462024121881413974438136299263633/20000000000000000000000000000000000000000) (3306063801272487078972634770362900826317/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0144.bracket2310 BracketBatch0144.bracket2311
  (301075743462024121881413974438136299263633/20000000000000000000000000000000000000000) (3306063801272487078972634770362900826317/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2310
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2311
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (150983306803530800866307415779733987066057/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (150983306803530800866307415779733987066057/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (151884912906442402246191469916152284754049/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (151884912906442402246191469916152284754049/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (151434109854986601556249442847943135910053/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (151434109854986601556249442847943135910053/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0288.rows ScalarLogs0288.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0144.bracket2311 BracketBatch0144.bracket2312 (151434109854986601556249442847943135910053/10000000000000000000000000000000000000000) (1657002305655347811414915657789028621057/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0144.bracket2311 BracketBatch0144.bracket2312
  (151434109854986601556249442847943135910053/10000000000000000000000000000000000000000) (1657002305655347811414915657789028621057/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2311
