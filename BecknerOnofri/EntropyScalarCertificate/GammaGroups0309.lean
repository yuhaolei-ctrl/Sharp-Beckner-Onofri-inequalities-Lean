import BecknerOnofri.EntropyScalarCertificate.Bessel0386
import BecknerOnofri.EntropyScalarCertificate.Bessel0387
import BecknerOnofri.EntropyScalarCertificate.Bessel0682
import BecknerOnofri.EntropyScalarCertificate.Brackets0154
import BecknerOnofri.EntropyScalarCertificate.Brackets0155
import BecknerOnofri.EntropyScalarCertificate.Logs0309
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2472
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (61829463428723164098504466145854565070999/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (61829463428723164098504466145854565070999/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (309907479960280446013646536337922232671299/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (309907479960280446013646536337922232671299/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (309527398551948133253084433533597529013147/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (309527398551948133253084433533597529013147/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0154.bracket2472 BracketBatch0154.bracket2473 (309527398551948133253084433533597529013147/10000000000000000000000000000000000000000) (2170666196211513908186038671278145308727/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0154.bracket2472 BracketBatch0154.bracket2473
  (309527398551948133253084433533597529013147/10000000000000000000000000000000000000000) (2170666196211513908186038671278145308727/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2472
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2473
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (4842304374379381968963227130280034885489/156250000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4842304374379381968963227130280034885489/156250000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (155335703078425920772854639706171972128451/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (155335703078425920772854639706171972128451/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (310289443058566143779677907875133088464099/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (310289443058566143779677907875133088464099/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0154.bracket2473 BracketBatch0154.bracket2474 (310289443058566143779677907875133088464099/10000000000000000000000000000000000000000) (4344890826695224158724774194380748196657/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0154.bracket2473 BracketBatch0154.bracket2474
  (310289443058566143779677907875133088464099/10000000000000000000000000000000000000000) (4344890826695224158724774194380748196657/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2473
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2474
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (310671406156851841545709279412343944256899/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (310671406156851841545709279412343944256899/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (311439123748533416954006175317489994382681/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (311439123748533416954006175317489994382681/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (31105526495269262924985772736491696931979/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (31105526495269262924985772736491696931979/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0154.bracket2474 BracketBatch0154.bracket2475 (31105526495269262924985772736491696931979/1000000000000000000000000000000000000000) (108711463550680323146465178346922720229/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0154.bracket2474 BracketBatch0154.bracket2475
  (31105526495269262924985772736491696931979/1000000000000000000000000000000000000000) (108711463550680323146465178346922720229/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2474
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2475
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (155719561874266708477003087658744997191339/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (155719561874266708477003087658744997191339/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (156105330514643417602301900378715058207029/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (156105330514643417602301900378715058207029/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (9744527887153441439978280876170626731199/312500000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9744527887153441439978280876170626731199/312500000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0154.bracket2475 BracketBatch0154.bracket2476 (9744527887153441439978280876170626731199/312500000000000000000000000000000000000) (4352035584088497852366052072651014907653/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0154.bracket2475 BracketBatch0154.bracket2476
  (9744527887153441439978280876170626731199/312500000000000000000000000000000000000) (4352035584088497852366052072651014907653/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2475
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2476
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0386.rows BesselBatch0386.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (62442132205857367040920760151486023282811/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (62442132205857367040920760151486023282811/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (312986046575307801050765178469032797745359/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (312986046575307801050765178469032797745359/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (312598353802297318127684489613231457079707/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (312598353802297318127684489613231457079707/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0154.bracket2476 BracketBatch0154.bracket2477 (312598353802297318127684489613231457079707/10000000000000000000000000000000000000000) (2177810999438279377177613870808780148033/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0154.bracket2476 BracketBatch0154.bracket2477
  (312598353802297318127684489613231457079707/10000000000000000000000000000000000000000) (2177810999438279377177613870808780148033/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2476
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2477
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (78246511643826950262691294617258199436339/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (78246511643826950262691294617258199436339/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (313765309248553986549676285619622399093961/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (313765309248553986549676285619622399093961/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (626751355823861787600441464088655196839317/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (626751355823861787600441464088655196839317/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0154.bracket2477 BracketBatch0154.bracket2478 (626751355823861787600441464088655196839317/20000000000000000000000000000000000000000) (4359217832719914317950583636161995382507/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0154.bracket2477 BracketBatch0154.bracket2478
  (626751355823861787600441464088655196839317/20000000000000000000000000000000000000000) (4359217832719914317950583636161995382507/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2477
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2478
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (156882654624276993274838142809811199546979/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (156882654624276993274838142809811199546979/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (314548478200326008090706931818833875625579/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (314548478200326008090706931818833875625579/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (628313787448879994640383217438456274719537/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (628313787448879994640383217438456274719537/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0154.bracket2478 BracketBatch0154.bracket2479 (628313787448879994640383217438456274719537/20000000000000000000000000000000000000000) (545352891535152440748777122100630592269/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0154.bracket2478 BracketBatch0154.bracket2479
  (628313787448879994640383217438456274719537/20000000000000000000000000000000000000000) (545352891535152440748777122100630592269/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2478
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2479
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (39318559775040751011338366477354234453197/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (39318559775040751011338366477354234453197/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0387.rows BesselBatch0387.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (78833895718725597000497945431681751280001/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (78833895718725597000497945431681751280001/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0682.rows BesselBatch0682.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (31494203053761419804634935677278044037279/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (31494203053761419804634935677278044037279/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0309.rows ScalarLogs0309.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0154.bracket2479 BracketBatch0155.bracket2480 (31494203053761419804634935677278044037279/1000000000000000000000000000000000000000) (2183218972280199085930065250435104366121/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0154.bracket2479 BracketBatch0155.bracket2480
  (31494203053761419804634935677278044037279/1000000000000000000000000000000000000000) (2183218972280199085930065250435104366121/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2479
