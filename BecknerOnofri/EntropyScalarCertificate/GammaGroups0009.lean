import BecknerOnofri.EntropyScalarCertificate.Bessel0011
import BecknerOnofri.EntropyScalarCertificate.Bessel0012
import BecknerOnofri.EntropyScalarCertificate.Bessel0494
import BecknerOnofri.EntropyScalarCertificate.Bessel0495
import BecknerOnofri.EntropyScalarCertificate.Brackets0004
import BecknerOnofri.EntropyScalarCertificate.Brackets0005
import BecknerOnofri.EntropyScalarCertificate.Logs0009
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0072
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (710789504804044060834100422253264548369/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (710789504804044060834100422253264548369/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (356402367205505579574538521924915615087/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (356402367205505579574538521924915615087/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (1423594239215055219983177466103095778543/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1423594239215055219983177466103095778543/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0004.bracket0072 BracketBatch0004.bracket0073 (1423594239215055219983177466103095778543/20000000000000000000000000000000000000000) (1931888076223117998537433562595247/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0004.bracket0072 BracketBatch0004.bracket0073
  (1423594239215055219983177466103095778543/20000000000000000000000000000000000000000) (1931888076223117998537433562595247/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0072
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0073
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (712804734411011159149077043849831230171/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (712804734411011159149077043849831230171/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (89352506318532088550047755922549879191/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (89352506318532088550047755922549879191/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (1427624784959267867549459091230230263699/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1427624784959267867549459091230230263699/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0004.bracket0073 BracketBatch0004.bracket0074 (1427624784959267867549459091230230263699/20000000000000000000000000000000000000000) (9771294781996886314310463642079531/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0004.bracket0073 BracketBatch0004.bracket0074
  (1427624784959267867549459091230230263699/20000000000000000000000000000000000000000) (9771294781996886314310463642079531/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0073
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0074
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (28592802021930268336015281895215961341/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (28592802021930268336015281895215961341/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (179208863366523154673099504858325249503/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (179208863366523154673099504858325249503/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (1431655504014349327092780066813700031537/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1431655504014349327092780066813700031537/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0004.bracket0074 BracketBatch0004.bracket0075 (1431655504014349327092780066813700031537/20000000000000000000000000000000000000000) (19768198314223695126282428511962679/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0004.bracket0074 BracketBatch0004.bracket0075
  (1431655504014349327092780066813700031537/20000000000000000000000000000000000000000) (19768198314223695126282428511962679/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0074
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0075
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (716835453466092618692398019433300998009/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (716835453466092618692398019433300998009/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (718850943414889804376985551414365365877/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (718850943414889804376985551414365365877/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (717843198440491211534691785423833181943/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (717843198440491211534691785423833181943/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0004.bracket0075 BracketBatch0004.bracket0076 (717843198440491211534691785423833181943/10000000000000000000000000000000000000000) (4998929443131806734902851205831427/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0004.bracket0075 BracketBatch0004.bracket0076
  (717843198440491211534691785423833181943/10000000000000000000000000000000000000000) (4998929443131806734902851205831427/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0075
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0076
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (359425471707444902188492775707182682937/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (359425471707444902188492775707182682937/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (360433260322539180417748204952684556823/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (360433260322539180417748204952684556823/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (8998234150374801032578012258248340497/125000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8998234150374801032578012258248340497/125000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0004.bracket0076 BracketBatch0004.bracket0077 (8998234150374801032578012258248340497/125000000000000000000000000000000000000) (20225158729355026195216446246716399/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0004.bracket0076 BracketBatch0004.bracket0077
  (8998234150374801032578012258248340497/125000000000000000000000000000000000000) (20225158729355026195216446246716399/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0076
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0077
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (720866520645078360835496409905369113643/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (720866520645078360835496409905369113643/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (722882185407147741357864258940054449813/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (722882185407147741357864258940054449813/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (22558573532066032846771260450709743179/312500000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (22558573532066032846771260450709743179/312500000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0004.bracket0077 BracketBatch0004.bracket0078 (22558573532066032846771260450709743179/312500000000000000000000000000000000000) (409130640120147986809127333826223/200000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0004.bracket0077 BracketBatch0004.bracket0078
  (22558573532066032846771260450709743179/312500000000000000000000000000000000000) (409130640120147986809127333826223/200000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0077
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0078
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (72288218540714774135786425894005444981/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (72288218540714774135786425894005444981/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (45306121121977933382442371524351659279/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (45306121121977933382442371524351659279/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (723890061679397337738471101664840499137/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (723890061679397337738471101664840499137/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0004.bracket0078 BracketBatch0004.bracket0079 (723890061679397337738471101664840499137/10000000000000000000000000000000000000000) (20689848454639586376180499622880021/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0004.bracket0078 BracketBatch0004.bracket0079
  (723890061679397337738471101664840499137/10000000000000000000000000000000000000000) (20689848454639586376180499622880021/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0078
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0079
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (724897937951646934119077944389626548461/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (724897937951646934119077944389626548461/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (363456889264592319626671321021573985603/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (363456889264592319626671321021573985603/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (1451811716480831573372420586432774519667/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1451811716480831573372420586432774519667/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0009.rows ScalarLogs0009.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0004.bracket0079 BracketBatch0005.bracket0080 (1451811716480831573372420586432774519667/20000000000000000000000000000000000000000) (10462559479133530836915895977358959/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0004.bracket0079 BracketBatch0005.bracket0080
  (1451811716480831573372420586432774519667/20000000000000000000000000000000000000000) (10462559479133530836915895977358959/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0079
