module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0165
public import BecknerOnofri.EntropyScalarCertificate.Bessel0166
public import BecknerOnofri.EntropyScalarCertificate.Bessel0571
public import BecknerOnofri.EntropyScalarCertificate.Bessel0572
public import BecknerOnofri.EntropyScalarCertificate.Brackets0066
public import BecknerOnofri.EntropyScalarCertificate.Logs0132
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1056
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (3209734465067800935357858152811762567013/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3209734465067800935357858152811762567013/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (6436642193510610162836535918430683886057/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6436642193510610162836535918430683886057/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (12856111123646212033552252224054209020083/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (12856111123646212033552252224054209020083/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0066.bracket1056 BracketBatch0066.bracket1057 (12856111123646212033552252224054209020083/20000000000000000000000000000000000000000) (37345618817785616528411226978711472679/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0066.bracket1056 BracketBatch0066.bracket1057
  (12856111123646212033552252224054209020083/20000000000000000000000000000000000000000) (37345618817785616528411226978711472679/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1056
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1057
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (3218321096755305081418267959215341943027/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3218321096755305081418267959215341943027/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (403366187271437393177502134981678839221/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (403366187271437393177502134981678839221/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (1289050118985360845367657007813754531359/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1289050118985360845367657007813754531359/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0066.bracket1057 BracketBatch0066.bracket1058 (1289050118985360845367657007813754531359/2000000000000000000000000000000000000000) (15058787624259509586467473684972933157/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0066.bracket1057 BracketBatch0066.bracket1058
  (1289050118985360845367657007813754531359/2000000000000000000000000000000000000000) (15058787624259509586467473684972933157/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1057
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1058
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (6453858996342998290840034159706861427533/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6453858996342998290840034159706861427533/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (808889952383949571590358250948460765259/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (808889952383949571590358250948460765259/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (2584995723082918972712580033458909509921/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2584995723082918972712580033458909509921/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0066.bracket1058 BracketBatch0066.bracket1059 (2584995723082918972712580033458909509921/4000000000000000000000000000000000000000) (75900619972484636846015652901293864791/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0066.bracket1058 BracketBatch0066.bracket1059
  (2584995723082918972712580033458909509921/4000000000000000000000000000000000000000) (75900619972484636846015652901293864791/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1058
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1059
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (6471119619071596572722866007587686122069/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6471119619071596572722866007587686122069/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (811053043067821655900290253513658968169/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (811053043067821655900290253513658968169/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (12959543963614169819925188035696957867421/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (12959543963614169819925188035696957867421/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0066.bracket1059 BracketBatch0066.bracket1060 (12959543963614169819925188035696957867421/20000000000000000000000000000000000000000) (76511305789497661700219444395830232931/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0066.bracket1059 BracketBatch0066.bracket1060
  (12959543963614169819925188035696957867421/20000000000000000000000000000000000000000) (76511305789497661700219444395830232931/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1059
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1060
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (6488424344542573247202322028109271745349/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6488424344542573247202322028109271745349/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (6505773458036690837747712285502062324533/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6505773458036690837747712285502062324533/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (6497098901289632042475017156805667034941/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6497098901289632042475017156805667034941/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0066.bracket1060 BracketBatch0066.bracket1061 (6497098901289632042475017156805667034941/10000000000000000000000000000000000000000) (77126018312115776119537819649670786161/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0066.bracket1060 BracketBatch0066.bracket1061
  (6497098901289632042475017156805667034941/10000000000000000000000000000000000000000) (77126018312115776119537819649670786161/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1060
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1061
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (650577345803669083774771228550206232453/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (650577345803669083774771228550206232453/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (81539590591211717113366607739181085769/125000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (81539590591211717113366607739181085769/125000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (260578814106672564136340818092730983721/400000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (260578814106672564136340818092730983721/400000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0066.bracket1061 BracketBatch0066.bracket1062 (260578814106672564136340818092730983721/400000000000000000000000000000000000000) (15548956084165201341327599302191454897/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0066.bracket1061 BracketBatch0066.bracket1062
  (260578814106672564136340818092730983721/400000000000000000000000000000000000000) (15548956084165201341327599302191454897/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1061
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1062
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0165.rows BesselBatch0165.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (6523167247296937369069328619134486861517/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6523167247296937369069328619134486861517/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (6540606002556538506259498799544114433511/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6540606002556538506259498799544114433511/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (3265943312463368968832206854669650323757/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3265943312463368968832206854669650323757/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0066.bracket1062 BracketBatch0066.bracket1063 (3265943312463368968832206854669650323757/5000000000000000000000000000000000000000) (78367615138134168689484914162379763513/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0066.bracket1062 BracketBatch0066.bracket1063
  (3265943312463368968832206854669650323757/5000000000000000000000000000000000000000) (78367615138134168689484914162379763513/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1062
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1063
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (1635151500639134626564874699886028608377/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1635151500639134626564874699886028608377/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (1311618003313471359877674413068410454257/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1311618003313471359877674413068410454257/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0571.rows BesselBatch0571.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (13098696019123895305647870864886166704793/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (13098696019123895305647870864886166704793/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0132.rows ScalarLogs0132.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0066.bracket1063 BracketBatch0066.bracket1064 (13098696019123895305647870864886166704793/20000000000000000000000000000000000000000) (78994545629893086893324059826901498439/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0066.bracket1063 BracketBatch0066.bracket1064
  (13098696019123895305647870864886166704793/20000000000000000000000000000000000000000) (78994545629893086893324059826901498439/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1063
