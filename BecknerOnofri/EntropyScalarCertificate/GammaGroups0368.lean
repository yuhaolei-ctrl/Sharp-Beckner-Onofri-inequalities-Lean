module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0460
public import BecknerOnofri.EntropyScalarCertificate.Bessel0461
public import BecknerOnofri.EntropyScalarCertificate.Bessel0718
public import BecknerOnofri.EntropyScalarCertificate.Bessel0719
public import BecknerOnofri.EntropyScalarCertificate.Brackets0184
public import BecknerOnofri.EntropyScalarCertificate.Logs0368
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2944
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (260667390147453360656687311671640829160527/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (260667390147453360656687311671640829160527/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (1306736636658708502691883730992387303671487/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1306736636658708502691883730992387303671487/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (1305036793697987652987660144675295724737061/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1305036793697987652987660144675295724737061/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0184.bracket2944 BracketBatch0184.bracket2945 (1305036793697987652987660144675295724737061/10000000000000000000000000000000000000000) (326069172136983243691060991722328166991/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0184.bracket2944 BracketBatch0184.bracket2945
  (1305036793697987652987660144675295724737061/10000000000000000000000000000000000000000) (326069172136983243691060991722328166991/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2944
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2945
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (326684159164677125672970932748096825917871/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (326684159164677125672970932748096825917871/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (327538530508169787197285948341918329111053/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (327538530508169787197285948341918329111053/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (163555672418211728217564220272503788757231/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (163555672418211728217564220272503788757231/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0184.bracket2945 BracketBatch0184.bracket2946 (163555672418211728217564220272503788757231/1250000000000000000000000000000000000000) (6525389992114622766065570197141140996553/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0184.bracket2945 BracketBatch0184.bracket2946
  (163555672418211728217564220272503788757231/1250000000000000000000000000000000000000) (6525389992114622766065570197141140996553/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2945
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2946
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (1310154122032679148789143793367673316444209/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1310154122032679148789143793367673316444209/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (328397386753086590467648769223486763538167/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (328397386753086590467648769223486763538167/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (2623743669045025510659738870261620370596877/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2623743669045025510659738870261620370596877/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0184.bracket2946 BracketBatch0184.bracket2947 (2623743669045025510659738870261620370596877/20000000000000000000000000000000000000000) (6529406814746216980522239421478507877601/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0184.bracket2946 BracketBatch0184.bracket2947
  (2623743669045025510659738870261620370596877/20000000000000000000000000000000000000000) (6529406814746216980522239421478507877601/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2946
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2947
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (262717909402469272374119015378789410830533/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (262717909402469272374119015378789410830533/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (1317043053226174263641490084043267106053089/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1317043053226174263641490084043267106053089/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (1315316300119260312756042580468607080102877/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1315316300119260312756042580468607080102877/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0184.bracket2947 BracketBatch0184.bracket2948 (1315316300119260312756042580468607080102877/10000000000000000000000000000000000000000) (6533433959590715309676063136684703442177/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0184.bracket2947 BracketBatch0184.bracket2948
  (1315316300119260312756042580468607080102877/10000000000000000000000000000000000000000) (6533433959590715309676063136684703442177/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2947
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2948
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (658521526613087131820745042021633553026543/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (658521526613087131820745042021633553026543/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (1320514783797386491747410592441556128138291/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1320514783797386491747410592441556128138291/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (2637557837023560755388900676484823234191377/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2637557837023560755388900676484823234191377/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0184.bracket2948 BracketBatch0184.bracket2949 (2637557837023560755388900676484823234191377/20000000000000000000000000000000000000000) (6537471475925382260955565528043072508021/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0184.bracket2948 BracketBatch0184.bracket2949
  (2637557837023560755388900676484823234191377/20000000000000000000000000000000000000000) (6537471475925382260955565528043072508021/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2948
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2949
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (82532173987336655734213162027597258008643/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (82532173987336655734213162027597258008643/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (1324004883363738151043301414830162731483291/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1324004883363738151043301414830162731483291/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (2644519667161124642790712007271718859621579/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2644519667161124642790712007271718859621579/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0184.bracket2949 BracketBatch0184.bracket2950 (2644519667161124642790712007271718859621579/20000000000000000000000000000000000000000) (3270759706675423114218743553522017026509/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0184.bracket2949 BracketBatch0184.bracket2950
  (2644519667161124642790712007271718859621579/20000000000000000000000000000000000000000) (3270759706675423114218743553522017026509/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2949
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2950
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (165500610420467268880412676853770341435411/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (165500610420467268880412676853770341435411/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (1327513498097602437826998068453669373721719/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1327513498097602437826998068453669373721719/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (2651518381461340588870299483283832105205007/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2651518381461340588870299483283832105205007/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0184.bracket2950 BracketBatch0184.bracket2951 (2651518381461340588870299483283832105205007/20000000000000000000000000000000000000000) (6545577821793479346553666733317246406783/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0184.bracket2950 BracketBatch0184.bracket2951
  (2651518381461340588870299483283832105205007/20000000000000000000000000000000000000000) (6545577821793479346553666733317246406783/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2950
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2951
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (331878374524400609456749517113417343430429/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (331878374524400609456749517113417343430429/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0461.rows BesselBatch0461.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (33276019393159444882763087661053969375109/250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (33276019393159444882763087661053969375109/250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0719.rows BesselBatch0719.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (664638568455995058284380393723957037181519/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (664638568455995058284380393723957037181519/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0368.rows ScalarLogs0368.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0184.bracket2951 BracketBatch0184.bracket2952 (664638568455995058284380393723957037181519/5000000000000000000000000000000000000000) (1637411687876947459211610315163722569993/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0184.bracket2951 BracketBatch0184.bracket2952
  (664638568455995058284380393723957037181519/5000000000000000000000000000000000000000) (1637411687876947459211610315163722569993/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2951
