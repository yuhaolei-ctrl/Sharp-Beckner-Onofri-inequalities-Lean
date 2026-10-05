module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0435
public import BecknerOnofri.EntropyScalarCertificate.Bessel0436
public import BecknerOnofri.EntropyScalarCertificate.Bessel0706
public import BecknerOnofri.EntropyScalarCertificate.Bessel0707
public import BecknerOnofri.EntropyScalarCertificate.Brackets0174
public import BecknerOnofri.EntropyScalarCertificate.Logs0348
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2784
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (920372782092604818733804669984080443990799/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (920372782092604818733804669984080443990799/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (184413087720989730871944980849074529447479/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (184413087720989730871944980849074529447479/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (921219110348776736546764787114726545614097/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (921219110348776736546764787114726545614097/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0174.bracket2784 BracketBatch0174.bracket2785 (921219110348776736546764787114726545614097/10000000000000000000000000000000000000000) (5985850659122072798471145751906164519979/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0174.bracket2784 BracketBatch0174.bracket2785
  (921219110348776736546764787114726545614097/10000000000000000000000000000000000000000) (5985850659122072798471145751906164519979/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2784
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2785
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (57629089912809290897482806515335790452337/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (57629089912809290897482806515335790452337/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (461882170558797841679916349083979111542173/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (461882170558797841679916349083979111542173/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (922914889861272168859778801206665435160869/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (922914889861272168859778801206665435160869/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0174.bracket2785 BracketBatch0174.bracket2786 (922914889861272168859778801206665435160869/10000000000000000000000000000000000000000) (5988675247204624516263898516526222531009/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0174.bracket2785 BracketBatch0174.bracket2786
  (922914889861272168859778801206665435160869/10000000000000000000000000000000000000000) (5988675247204624516263898516526222531009/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2785
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2786
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (923764341117595683359832698167958223084343/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (923764341117595683359832698167958223084343/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (925469524266405752779749300699884139261937/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (925469524266405752779749300699884139261937/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (46230846634600035903489549971696059058657/500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (46230846634600035903489549971696059058657/500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0174.bracket2786 BracketBatch0174.bracket2787 (46230846634600035903489549971696059058657/500000000000000000000000000000000000000) (5991505143144431677555381964933193350967/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0174.bracket2786 BracketBatch0174.bracket2787
  (46230846634600035903489549971696059058657/500000000000000000000000000000000000000) (5991505143144431677555381964933193350967/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2786
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2787
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (462734762133202876389874650349942069630967/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (462734762133202876389874650349942069630967/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (28974406966993769830036094169686325251343/312500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (28974406966993769830036094169686325251343/312500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (185265054721020638734090431412984654730491/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (185265054721020638734090431412984654730491/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0174.bracket2787 BracketBatch0174.bracket2788 (185265054721020638734090431412984654730491/2000000000000000000000000000000000000000) (5994340365986562795948105743679406417767/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0174.bracket2787 BracketBatch0174.bracket2788
  (185265054721020638734090431412984654730491/2000000000000000000000000000000000000000) (5994340365986562795948105743679406417767/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2787
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2788
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (927181022943800634561155013429962408042973/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (927181022943800634561155013429962408042973/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (928898872301144006292203285892052039993747/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (928898872301144006292203285892052039993747/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (23200998690561808010666978741525180600459/250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (23200998690561808010666978741525180600459/250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0174.bracket2788 BracketBatch0174.bracket2789 (23200998690561808010666978741525180600459/250000000000000000000000000000000000000) (2998590467438038254349622341319778923049/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0174.bracket2788 BracketBatch0174.bracket2789
  (23200998690561808010666978741525180600459/250000000000000000000000000000000000000) (2998590467438038254349622341319778923049/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2788
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2789
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (58056179518821500393262705368253252499609/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (58056179518821500393262705368253252499609/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (465311553875573987247092392350419166404833/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (465311553875573987247092392350419166404833/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (185952198005229198078638807059289037280341/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (185952198005229198078638807059289037280341/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0174.bracket2789 BracketBatch0174.bracket2790 (185952198005229198078638807059289037280341/2000000000000000000000000000000000000000) (3000013434529349587412008735520665670801/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0174.bracket2789 BracketBatch0174.bracket2790
  (185952198005229198078638807059289037280341/2000000000000000000000000000000000000000) (3000013434529349587412008735520665670801/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2789
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2790
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (930623107751147974494184784700838332809663/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (930623107751147974494184784700838332809663/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (932353764970306486436534080497630120470349/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (932353764970306486436534080497630120470349/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (465744218180363615232679716299617113320003/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (465744218180363615232679716299617113320003/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0174.bracket2790 BracketBatch0174.bracket2791 (465744218180363615232679716299617113320003/5000000000000000000000000000000000000000) (6002878187881507944417007586490009361893/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0174.bracket2790 BracketBatch0174.bracket2791
  (465744218180363615232679716299617113320003/5000000000000000000000000000000000000000) (6002878187881507944417007586490009361893/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2790
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2791
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (466176882485153243218267040248815060235173/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (466176882485153243218267040248815060235173/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (934090879901355981636332680923181219472583/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (934090879901355981636332680923181219472583/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (1866444644871662468072866761420811339942929/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1866444644871662468072866761420811339942929/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0348.rows ScalarLogs0348.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0174.bracket2791 BracketBatch0174.bracket2792 (1866444644871662468072866761420811339942929/20000000000000000000000000000000000000000) (3002867455396809674097057842747767875333/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0174.bracket2791 BracketBatch0174.bracket2792
  (1866444644871662468072866761420811339942929/20000000000000000000000000000000000000000) (3002867455396809674097057842747767875333/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2791
