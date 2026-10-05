module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0000
public import BecknerOnofri.EntropyScalarCertificate.Bessel0001
public import BecknerOnofri.EntropyScalarCertificate.Bessel0488
public import BecknerOnofri.EntropyScalarCertificate.Bessel0489
public import BecknerOnofri.EntropyScalarCertificate.Brackets0000
public import BecknerOnofri.EntropyScalarCertificate.Logs0000
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0000
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (78278086446495369331777475473447150057/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (78278086446495369331777475473447150057/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (313363819803528433424978506226361405671/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (313363819803528433424978506226361405671/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (626476165589509910752088408120150005899/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (626476165589509910752088408120150005899/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0000.bracket0000 BracketBatch0000.bracket0001 (626476165589509910752088408120150005899/10000000000000000000000000000000000000000) (11881575090688911297711312028108613/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0000.bracket0000 BracketBatch0000.bracket0001
  (626476165589509910752088408120150005899/10000000000000000000000000000000000000000) (11881575090688911297711312028108613/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0000
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0001
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (626727639607056866849957012452722811339/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (626727639607056866849957012452722811339/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (313615296192393124006927616765330513089/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (313615296192393124006927616765330513089/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (1253958231991843114863812245983383837517/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1253958231991843114863812245983383837517/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0000.bracket0001 BracketBatch0000.bracket0002 (1253958231991843114863812245983383837517/20000000000000000000000000000000000000000) (2979938188754442258558595596097613/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0000.bracket0001 BracketBatch0000.bracket0002
  (1253958231991843114863812245983383837517/20000000000000000000000000000000000000000) (2979938188754442258558595596097613/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0001
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0002
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (25089223695391449920554209341226441047/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (25089223695391449920554209341226441047/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (313866774954512534937687644241077369851/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (313866774954512534937687644241077369851/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (1254964142293811317889230522012815765877/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1254964142293811317889230522012815765877/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0000.bracket0002 BracketBatch0000.bracket0003 (1254964142293811317889230522012815765877/20000000000000000000000000000000000000000) (5979011114195400970510729957419671/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0000.bracket0002 BracketBatch0000.bracket0003
  (1254964142293811317889230522012815765877/20000000000000000000000000000000000000000) (5979011114195400970510729957419671/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0002
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0003
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (627733549909025069875375288482154739699/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (627733549909025069875375288482154739699/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (31411825609182375247993146651283164429/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (31411825609182375247993146651283164429/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (1255970062092672574835238221507818028279/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1255970062092672574835238221507818028279/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0000.bracket0003 BracketBatch0000.bracket0004 (1255970062092672574835238221507818028279/20000000000000000000000000000000000000000) (5998191829112114311386724423761199/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0000.bracket0003 BracketBatch0000.bracket0004
  (1255970062092672574835238221507818028279/20000000000000000000000000000000000000000) (5998191829112114311386724423761199/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0003
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0004
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (628236512183647504959862933025663288577/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (628236512183647504959862933025663288577/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (628739479212527926757317144631546673977/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (628739479212527926757317144631546673977/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (628487995698087715858590038828604981277/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (628487995698087715858590038828604981277/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0000.bracket0004 BracketBatch0000.bracket0005 (628487995698087715858590038828604981277/10000000000000000000000000000000000000000) (3008709298013479238630576745075029/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0000.bracket0004 BracketBatch0000.bracket0005
  (628487995698087715858590038828604981277/10000000000000000000000000000000000000000) (3008709298013479238630576745075029/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0004
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0005
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (314369739606263963378658572315773336987/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (314369739606263963378658572315773336987/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (629242450999540909891178883112898916331/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (629242450999540909891178883112898916331/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (251596386042413767329699205548889118061/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (251596386042413767329699205548889118061/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0000.bracket0005 BracketBatch0000.bracket0006 (251596386042413767329699205548889118061/4000000000000000000000000000000000000000) (3018345744383847141680981262706069/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0000.bracket0005 BracketBatch0000.bracket0006
  (251596386042413767329699205548889118061/4000000000000000000000000000000000000000) (3018345744383847141680981262706069/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0005
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0006
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0000.rows BesselBatch0000.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (78655306374942613736397360389112364541/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (78655306374942613736397360389112364541/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (125949085509712246057428068438925799773/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (125949085509712246057428068438925799773/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (1258987878548102140178319225307527915193/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1258987878548102140178319225307527915193/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0000.bracket0006 BracketBatch0000.bracket0007 (1258987878548102140178319225307527915193/20000000000000000000000000000000000000000) (12112021162443823334083495799983713/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0000.bracket0006 BracketBatch0000.bracket0007
  (1258987878548102140178319225307527915193/20000000000000000000000000000000000000000) (12112021162443823334083495799983713/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0006
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0007
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (314872713774280615143570171097314499431/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (314872713774280615143570171097314499431/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0001.rows BesselBatch0001.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (157562102215865966335493677486552287533/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (157562102215865966335493677486552287533/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0489.rows BesselBatch0489.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (629996918206012547814557526070419074497/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (629996918206012547814557526070419074497/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0000.rows ScalarLogs0000.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0000.bracket0007 BracketBatch0000.bracket0008 (629996918206012547814557526070419074497/10000000000000000000000000000000000000000) (6075375947337031934056622959202703/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0000.bracket0007 BracketBatch0000.bracket0008
  (629996918206012547814557526070419074497/10000000000000000000000000000000000000000) (6075375947337031934056622959202703/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0007
