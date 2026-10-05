module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0476
public import BecknerOnofri.EntropyScalarCertificate.Bessel0477
public import BecknerOnofri.EntropyScalarCertificate.Bessel0727
public import BecknerOnofri.EntropyScalarCertificate.Brackets0190
public import BecknerOnofri.EntropyScalarCertificate.Brackets0191
public import BecknerOnofri.EntropyScalarCertificate.Logs0381
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3048
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (1786966919949708436323322518409994445681003/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1786966919949708436323322518409994445681003/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (448341830033725973559364159490433319211809/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (448341830033725973559364159490433319211809/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (3580334240084612330560779156371727722528239/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3580334240084612330560779156371727722528239/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0190.bracket3048 BracketBatch0190.bracket3049 (3580334240084612330560779156371727722528239/20000000000000000000000000000000000000000) (1750926675436851227505798488633769846221/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0190.bracket3048 BracketBatch0190.bracket3049
  (3580334240084612330560779156371727722528239/20000000000000000000000000000000000000000) (1750926675436851227505798488633769846221/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3048
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3049
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (1793367320134903894237456637961733276847233/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1793367320134903894237456637961733276847233/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (224976720804094528462157220422254443961509/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (224976720804094528462157220422254443961509/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (718636217313532024386942880267953765707861/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (718636217313532024386942880267953765707861/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0190.bracket3049 BracketBatch0190.bracket3050 (718636217313532024386942880267953765707861/4000000000000000000000000000000000000000) (7009113609524946267281180328387147761321/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0190.bracket3049 BracketBatch0190.bracket3050
  (718636217313532024386942880267953765707861/4000000000000000000000000000000000000000) (7009113609524946267281180328387147761321/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3049
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3050
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (1799813766432756227697257763378035551692069/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1799813766432756227697257763378035551692069/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (225788344692202968738477079014471952986739/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (225788344692202968738477079014471952986739/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (3606120523970379977605074395493811175585981/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3606120523970379977605074395493811175585981/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0190.bracket3050 BracketBatch0190.bracket3051 (3606120523970379977605074395493811175585981/20000000000000000000000000000000000000000) (7014538034490532177751318404502767024437/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0190.bracket3050 BracketBatch0190.bracket3051
  (3606120523970379977605074395493811175585981/20000000000000000000000000000000000000000) (7014538034490532177751318404502767024437/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3050
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3051
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (1806306757537623749907816632115775623893909/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1806306757537623749907816632115775623893909/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (1812846799371319242576693981505572759343251/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1812846799371319242576693981505572759343251/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (90478838922723574812112765340533709580929/500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (90478838922723574812112765340533709580929/500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0190.bracket3051 BracketBatch0190.bracket3052 (90478838922723574812112765340533709580929/500000000000000000000000000000000000000) (3509990035195540353237212327572654286737/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0190.bracket3051 BracketBatch0190.bracket3052
  (90478838922723574812112765340533709580929/500000000000000000000000000000000000000) (3509990035195540353237212327572654286737/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3051
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3052
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0476.rows BesselBatch0476.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (113302924960707452661043373844098297458953/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (113302924960707452661043373844098297458953/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (909717202607259109488788631502036594001249/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (909717202607259109488788631502036594001249/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (1816140602292918730777135622254822973672873/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1816140602292918730777135622254822973672873/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0190.bracket3052 BracketBatch0190.bracket3053 (1816140602292918730777135622254822973672873/10000000000000000000000000000000000000000) (1756359952851998851388001053331845305711/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0190.bracket3052 BracketBatch0190.bracket3053
  (1816140602292918730777135622254822973672873/10000000000000000000000000000000000000000) (1756359952851998851388001053331845305711/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3052
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3053
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (363886881042903643795515452600814637600499/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (363886881042903643795515452600814637600499/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (228258761980130592527463858217021187278711/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (228258761980130592527463858217021187278711/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (3645504501055562959197288128740242686232183/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3645504501055562959197288128740242686232183/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0190.bracket3053 BracketBatch0190.bracket3054 (3645504501055562959197288128740242686232183/20000000000000000000000000000000000000000) (1757729338037728823639760558602401561699/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0190.bracket3053 BracketBatch0190.bracket3054
  (3645504501055562959197288128740242686232183/20000000000000000000000000000000000000000) (1757729338037728823639760558602401561699/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3053
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3054
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (365214019168208948043942173147233899645937/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (365214019168208948043942173147233899645937/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (916377199827554284069316251705163450945457/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (916377199827554284069316251705163450945457/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (3658824495496153308358343369146496400120599/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3658824495496153308358343369146496400120599/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0190.bracket3054 BracketBatch0190.bracket3055 (3658824495496153308358343369146496400120599/20000000000000000000000000000000000000000) (3518206393825516534060222150984475885563/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0190.bracket3054 BracketBatch0190.bracket3055
  (3658824495496153308358343369146496400120599/20000000000000000000000000000000000000000) (3518206393825516534060222150984475885563/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3054
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3055
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (1832754399655108568138632503410326901890911/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1832754399655108568138632503410326901890911/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0477.rows BesselBatch0477.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (1839487852831569608324205261457338346104893/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1839487852831569608324205261457338346104893/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0727.rows BesselBatch0727.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (918060563121669544115709441216916311998951/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (918060563121669544115709441216916311998951/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0381.rows ScalarLogs0381.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0190.bracket3055 BracketBatch0191.bracket3056 (918060563121669544115709441216916311998951/5000000000000000000000000000000000000000) (7041926213353962799910091848866762216081/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0190.bracket3055 BracketBatch0191.bracket3056
  (918060563121669544115709441216916311998951/5000000000000000000000000000000000000000) (7041926213353962799910091848866762216081/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3055
