module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0420
public import BecknerOnofri.EntropyScalarCertificate.Bessel0421
public import BecknerOnofri.EntropyScalarCertificate.Bessel0698
public import BecknerOnofri.EntropyScalarCertificate.Bessel0699
public import BecknerOnofri.EntropyScalarCertificate.Brackets0168
public import BecknerOnofri.EntropyScalarCertificate.Logs0336
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2688
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (659151930499554350574899290679828151364427/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (659151930499554350574899290679828151364427/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (662632816807154078105621558838164434946883/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (662632816807154078105621558838164434946883/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (132178474730670842868052084951799258631131/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (132178474730670842868052084951799258631131/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0168.bracket2688 BracketBatch0168.bracket2689 (132178474730670842868052084951799258631131/2000000000000000000000000000000000000000) (5450849241150199348431109099575651251957/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0168.bracket2688 BracketBatch0168.bracket2689
  (132178474730670842868052084951799258631131/2000000000000000000000000000000000000000) (5450849241150199348431109099575651251957/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2688
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2689
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (2070727552522356494080067371369263859209/31250000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2070727552522356494080067371369263859209/31250000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (166537683557681589504220523801951677553333/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (166537683557681589504220523801951677553333/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (332195887759470109030625913511492786290053/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (332195887759470109030625913511492786290053/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0168.bracket2689 BracketBatch0168.bracket2690 (332195887759470109030625913511492786290053/5000000000000000000000000000000000000000) (682316157758210001945816029849699821861/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0168.bracket2689 BracketBatch0168.bracket2690
  (332195887759470109030625913511492786290053/5000000000000000000000000000000000000000) (682316157758210001945816029849699821861/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2689
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2690
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (666150734230726358016882095207806710213329/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (666150734230726358016882095207806710213329/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (334853138426140967779584954883810668759509/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (334853138426140967779584954883810668759509/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (1335857011083008293576052004975428047732347/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1335857011083008293576052004975428047732347/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0168.bracket2690 BracketBatch0168.bracket2691 (1335857011083008293576052004975428047732347/20000000000000000000000000000000000000000) (5466246847543145428065371592445809164737/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0168.bracket2690 BracketBatch0168.bracket2691
  (1335857011083008293576052004975428047732347/20000000000000000000000000000000000000000) (5466246847543145428065371592445809164737/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2690
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2691
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (133941255370456387111833981953524267503803/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (133941255370456387111833981953524267503803/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (336650025764894397998125291772335340027311/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (336650025764894397998125291772335340027311/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (1343006328382070731555420493312292017573637/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1343006328382070731555420493312292017573637/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0168.bracket2691 BracketBatch0168.bracket2692 (1343006328382070731555420493312292017573637/20000000000000000000000000000000000000000) (1094800459158758874865265798358569939501/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0168.bracket2691 BracketBatch0168.bracket2692
  (1343006328382070731555420493312292017573637/20000000000000000000000000000000000000000) (1094800459158758874865265798358569939501/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2691
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2692
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (673300051529788795996250583544670680054619/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (673300051529788795996250583544670680054619/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (676932678242468306216924409296107603196237/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (676932678242468306216924409296107603196237/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (168779091221532137776646874105097285406357/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (168779091221532137776646874105097285406357/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0168.bracket2692 BracketBatch0168.bracket2693 (168779091221532137776646874105097285406357/2500000000000000000000000000000000000000) (1096359181420201001307446485490244620931/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0168.bracket2692 BracketBatch0168.bracket2693
  (168779091221532137776646874105097285406357/2500000000000000000000000000000000000000) (1096359181420201001307446485490244620931/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2692
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2693
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (338466339121234153108462204648053801598117/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (338466339121234153108462204648053801598117/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (136120958089470202627696046409279634862523/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (136120958089470202627696046409279634862523/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (1357537468689819319355404641342505777508849/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1357537468689819319355404641342505777508849/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0168.bracket2693 BracketBatch0168.bracket2694 (1357537468689819319355404641342505777508849/20000000000000000000000000000000000000000) (2744813991889077937290544303207503906393/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0168.bracket2693 BracketBatch0168.bracket2694
  (1357537468689819319355404641342505777508849/20000000000000000000000000000000000000000) (2744813991889077937290544303207503906393/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2693
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2694
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0420.rows BesselBatch0420.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (170151197611837753284620058011599543578153/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (170151197611837753284620058011599543578153/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (17107925886188069903904303471570612201219/250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17107925886188069903904303471570612201219/250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (341230456473718452323663092727305665590343/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (341230456473718452323663092727305665590343/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0168.bracket2694 BracketBatch0168.bracket2695 (341230456473718452323663092727305665590343/5000000000000000000000000000000000000000) (5497498830122042360183189942057751580713/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0168.bracket2694 BracketBatch0168.bracket2695
  (341230456473718452323663092727305665590343/5000000000000000000000000000000000000000) (5497498830122042360183189942057751580713/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2694
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2695
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (684317035447522796156172138862824488048757/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (684317035447522796156172138862824488048757/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0421.rows BesselBatch0421.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (86008759346563875330061137360693608665479/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (86008759346563875330061137360693608665479/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0699.rows BesselBatch0699.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (1372387110220033798796661237748373357372589/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1372387110220033798796661237748373357372589/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0336.rows ScalarLogs0336.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0168.bracket2695 BracketBatch0168.bracket2696 (1372387110220033798796661237748373357372589/20000000000000000000000000000000000000000) (1376352188090400795558257393290294772487/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0168.bracket2695 BracketBatch0168.bracket2696
  (1372387110220033798796661237748373357372589/20000000000000000000000000000000000000000) (1376352188090400795558257393290294772487/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2695
