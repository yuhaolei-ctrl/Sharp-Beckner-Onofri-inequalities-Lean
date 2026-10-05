module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0485
public import BecknerOnofri.EntropyScalarCertificate.Bessel0486
public import BecknerOnofri.EntropyScalarCertificate.Bessel0731
public import BecknerOnofri.EntropyScalarCertificate.Bessel0732
public import BecknerOnofri.EntropyScalarCertificate.Brackets0194
public import BecknerOnofri.EntropyScalarCertificate.Logs0388
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3104
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (1116697481523679699827574174996099655924959/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1116697481523679699827574174996099655924959/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (224340456284450515525002571405555480753501/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (224340456284450515525002571405555480753501/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (139899985184120767340786689501492316230779/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (139899985184120767340786689501492316230779/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0194.bracket3104 BracketBatch0194.bracket3105 (139899985184120767340786689501492316230779/625000000000000000000000000000000000000) (366809228365462782013983634927570865937/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0194.bracket3104 BracketBatch0194.bracket3105
  (139899985184120767340786689501492316230779/625000000000000000000000000000000000000) (366809228365462782013983634927570865937/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3104
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3105
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (2243404562844505155250025714055554807535007/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2243404562844505155250025714055554807535007/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (563376084825392901250070890070158276988023/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (563376084825392901250070890070158276988023/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (4496908902146076760250309274336187915487099/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4496908902146076760250309274336187915487099/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0194.bracket3105 BracketBatch0194.bracket3106 (4496908902146076760250309274336187915487099/20000000000000000000000000000000000000000) (3671362025891516640186137126437275451443/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0194.bracket3105 BracketBatch0194.bracket3106
  (4496908902146076760250309274336187915487099/20000000000000000000000000000000000000000) (3671362025891516640186137126437275451443/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3105
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3106
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (2253504339301571605000283560280633107952089/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2253504339301571605000283560280633107952089/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (2263695516536110998767956100993025586636827/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2263695516536110998767956100993025586636827/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (1129299963959420650942059915318414673647229/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1129299963959420650942059915318414673647229/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0194.bracket3106 BracketBatch0194.bracket3107 (1129299963959420650942059915318414673647229/5000000000000000000000000000000000000000) (14354075258610760203530440316155265841/19531250000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0194.bracket3106 BracketBatch0194.bracket3107
  (1129299963959420650942059915318414673647229/5000000000000000000000000000000000000000) (14354075258610760203530440316155265841/19531250000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3106
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3107
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (282961939567013874845994512624128198329603/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (282961939567013874845994512624128198329603/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (2273979340922358354837501297277377371326361/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2273979340922358354837501297277377371326361/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (907534971491693870721091479654080591592637/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (907534971491693870721091479654080591592637/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0194.bracket3107 BracketBatch0194.bracket3108 (907534971491693870721091479654080591592637/4000000000000000000000000000000000000000) (7355872094141771928745964448704132710287/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0194.bracket3107 BracketBatch0194.bracket3108
  (907534971491693870721091479654080591592637/4000000000000000000000000000000000000000) (7355872094141771928745964448704132710287/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3107
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3108
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (1136989670461179177418750648638688685663179/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1136989670461179177418750648638688685663179/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (2284357081599374902117195540363061600041127/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2284357081599374902117195540363061600041127/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (911667284504346651390939367528087794273497/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (911667284504346651390939367528087794273497/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0194.bracket3108 BracketBatch0194.bracket3109 (911667284504346651390939367528087794273497/4000000000000000000000000000000000000000) (1472496164067739661263579435939237994269/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0194.bracket3108 BracketBatch0194.bracket3109
  (911667284504346651390939367528087794273497/4000000000000000000000000000000000000000) (1472496164067739661263579435939237994269/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3108
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3109
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (571089270399843725529298885090765400010281/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (571089270399843725529298885090765400010281/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (2294830030993177121667172229020178606376999/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2294830030993177121667172229020178606376999/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (4579187112592552023784367769383240206418123/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4579187112592552023784367769383240206418123/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0194.bracket3109 BracketBatch0194.bracket3110 (4579187112592552023784367769383240206418123/20000000000000000000000000000000000000000) (3684556396326521224725002300043297796393/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0194.bracket3109 BracketBatch0194.bracket3110
  (4579187112592552023784367769383240206418123/20000000000000000000000000000000000000000) (3684556396326521224725002300043297796393/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3109
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3110
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (573707507748294280416793057255044651594249/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (573707507748294280416793057255044651594249/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (2305399505353302535919479852513133742884521/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2305399505353302535919479852513133742884521/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (4600229536346479657586652081533312349261517/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4600229536346479657586652081533312349261517/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0194.bracket3110 BracketBatch0194.bracket3111 (4600229536346479657586652081533312349261517/20000000000000000000000000000000000000000) (7375768090926759346044332553380519685777/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0194.bracket3110 BracketBatch0194.bracket3111
  (4600229536346479657586652081533312349261517/20000000000000000000000000000000000000000) (7375768090926759346044332553380519685777/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3110
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3111
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (1152699752676651267959739926256566871442259/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1152699752676651267959739926256566871442259/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0486.rows BesselBatch0486.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (2316066845304280103154252803827464850416707/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2316066845304280103154252803827464850416707/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0732.rows BesselBatch0732.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (184858654026303305562949306253623943732049/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (184858654026303305562949306253623943732049/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0388.rows ScalarLogs0388.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0194.bracket3111 BracketBatch0194.bracket3112 (184858654026303305562949306253623943732049/800000000000000000000000000000000000000) (3691223396538272193727748124290636395691/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0194.bracket3111 BracketBatch0194.bracket3112
  (184858654026303305562949306253623943732049/800000000000000000000000000000000000000) (3691223396538272193727748124290636395691/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3111
