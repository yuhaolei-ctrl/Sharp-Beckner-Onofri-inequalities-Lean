module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0008
public import BecknerOnofri.EntropyScalarCertificate.Bessel0009
public import BecknerOnofri.EntropyScalarCertificate.Bessel0010
public import BecknerOnofri.EntropyScalarCertificate.Bessel0493
public import BecknerOnofri.EntropyScalarCertificate.Brackets0003
public import BecknerOnofri.EntropyScalarCertificate.Brackets0004
public import BecknerOnofri.EntropyScalarCertificate.Logs0007
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0056
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (339278697590943010395863765603974443409/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (339278697590943010395863765603974443409/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (340285637149676965436982222677369119397/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (340285637149676965436982222677369119397/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (339782167370309987916422994140671781403/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (339782167370309987916422994140671781403/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0003.bracket0056 BracketBatch0003.bracket0057 (339782167370309987916422994140671781403/5000000000000000000000000000000000000000) (15989272558817590447506832491591997/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0003.bracket0056 BracketBatch0003.bracket0057
  (339782167370309987916422994140671781403/5000000000000000000000000000000000000000) (15989272558817590447506832491591997/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0056
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0057
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (680571274299353930873964445354738238791/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (680571274299353930873964445354738238791/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (68258523594999042531603073203106799723/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (68258523594999042531603073203106799723/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (1363156510249344356189995177385806236021/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1363156510249344356189995177385806236021/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0003.bracket0057 BracketBatch0003.bracket0058 (1363156510249344356189995177385806236021/20000000000000000000000000000000000000000) (1011501271420498209701712077205351/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0003.bracket0057 BracketBatch0003.bracket0058
  (1363156510249344356189995177385806236021/20000000000000000000000000000000000000000) (1011501271420498209701712077205351/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0057
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0058
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (682585235949990425316030732031067997227/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (682585235949990425316030732031067997227/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (342299640191593655289461908031668023689/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (342299640191593655289461908031668023689/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (273436903266635547178990909618880808921/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (273436903266635547178990909618880808921/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0003.bracket0058 BracketBatch0003.bracket0059 (273436903266635547178990909618880808921/4000000000000000000000000000000000000000) (16380500112000940624097283145809983/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0003.bracket0058 BracketBatch0003.bracket0059
  (273436903266635547178990909618880808921/4000000000000000000000000000000000000000) (16380500112000940624097283145809983/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0058
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0059
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (5476794243065498484631390528506688379/80000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5476794243065498484631390528506688379/80000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (137322681569678516362736326151687548259/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (137322681569678516362736326151687548259/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (137121268823157989239260544682177378867/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (137121268823157989239260544682177378867/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0003.bracket0059 BracketBatch0003.bracket0060 (137121268823157989239260544682177378867/2000000000000000000000000000000000000000) (129521266667474280818964919653173/78125000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0003.bracket0059 BracketBatch0003.bracket0060
  (137121268823157989239260544682177378867/2000000000000000000000000000000000000000) (129521266667474280818964919653173/78125000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0059
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0060
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (171653351962098145453420407689609435323/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (171653351962098145453420407689609435323/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (172156904648777649532850575740162017917/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (172156904648777649532850575740162017917/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (8595256415271894874656774585744286331/125000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8595256415271894874656774585744286331/125000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0003.bracket0060 BracketBatch0003.bracket0061 (8595256415271894874656774585744286331/125000000000000000000000000000000000000) (3355739340919532013148945826273061/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0003.bracket0060 BracketBatch0003.bracket0061
  (8595256415271894874656774585744286331/125000000000000000000000000000000000000) (3355739340919532013148945826273061/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0060
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0061
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (137725523719022119626280460592129614333/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (137725523719022119626280460592129614333/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (10791279888639097780710938604571526237/156250000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10791279888639097780710938604571526237/156250000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (1379269531468012856096902373653225750833/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1379269531468012856096902373653225750833/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0003.bracket0061 BracketBatch0003.bracket0062 (1379269531468012856096902373653225750833/20000000000000000000000000000000000000000) (4245108538453345536754201421341961/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0003.bracket0061 BracketBatch0003.bracket0062
  (1379269531468012856096902373653225750833/20000000000000000000000000000000000000000) (4245108538453345536754201421341961/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0061
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0062
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (138128382574580451593100014138515535833/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (138128382574580451593100014138515535833/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (346328145465692587263248956005240370629/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (346328145465692587263248956005240370629/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (1383298203804287432491997982703058420423/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1383298203804287432491997982703058420423/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0003.bracket0062 BracketBatch0003.bracket0063 (1383298203804287432491997982703058420423/20000000000000000000000000000000000000000) (8591972420092847291468242881781393/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0003.bracket0062 BracketBatch0003.bracket0063
  (1383298203804287432491997982703058420423/20000000000000000000000000000000000000000) (8591972420092847291468242881781393/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0062
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0063
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0009.rows BesselBatch0009.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (138531258186277034905299582402096148251/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (138531258186277034905299582402096148251/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (138934150604046770269931527954147437559/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (138934150604046770269931527954147437559/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (27746540879032380517523111035624358581/400000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (27746540879032380517523111035624358581/400000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0007.rows ScalarLogs0007.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0003.bracket0063 BracketBatch0004.bracket0064 (27746540879032380517523111035624358581/400000000000000000000000000000000000000) (2173654894199213162366269606731429/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0003.bracket0063 BracketBatch0004.bracket0064
  (27746540879032380517523111035624358581/400000000000000000000000000000000000000) (2173654894199213162366269606731429/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0063
