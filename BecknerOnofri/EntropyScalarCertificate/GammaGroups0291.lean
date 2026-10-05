module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0363
public import BecknerOnofri.EntropyScalarCertificate.Bessel0364
public import BecknerOnofri.EntropyScalarCertificate.Bessel0365
public import BecknerOnofri.EntropyScalarCertificate.Bessel0670
public import BecknerOnofri.EntropyScalarCertificate.Bessel0671
public import BecknerOnofri.EntropyScalarCertificate.Brackets0145
public import BecknerOnofri.EntropyScalarCertificate.Brackets0146
public import BecknerOnofri.EntropyScalarCertificate.Logs0291
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2328
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (20993238708166282729905707265756780315797/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (20993238708166282729905707265756780315797/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (84532137545054176552104168041480583916773/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (84532137545054176552104168041480583916773/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (168505092377719307471726997104507705179961/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (168505092377719307471726997104507705179961/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0145.bracket2328 BracketBatch0145.bracket2329 (168505092377719307471726997104507705179961/10000000000000000000000000000000000000000) (691352157155482293876244498446912165559/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0145.bracket2328 BracketBatch0145.bracket2329
  (168505092377719307471726997104507705179961/10000000000000000000000000000000000000000) (691352157155482293876244498446912165559/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2328
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2329
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0363.rows BesselBatch0363.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (169064275090108353104208336082961167833543/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (169064275090108353104208336082961167833543/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (170197756413761223249007712748970007042173/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (170197756413761223249007712748970007042173/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (84815507875967394088304012207982793718929/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (84815507875967394088304012207982793718929/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0145.bracket2329 BracketBatch0145.bracket2330 (84815507875967394088304012207982793718929/5000000000000000000000000000000000000000) (3465645948353017455956635566531603310277/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0145.bracket2329 BracketBatch0145.bracket2330
  (84815507875967394088304012207982793718929/5000000000000000000000000000000000000000) (3465645948353017455956635566531603310277/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2329
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2330
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (17019775641376122324900771274897000704217/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17019775641376122324900771274897000704217/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (85673331060796520840810799926301821767319/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (85673331060796520840810799926301821767319/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (42693052316919283116328664075196706322101/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (42693052316919283116328664075196706322101/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0145.bracket2330 BracketBatch0145.bracket2331 (42693052316919283116328664075196706322101/2500000000000000000000000000000000000000) (694917790137800427583942308690796910381/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0145.bracket2330 BracketBatch0145.bracket2331
  (42693052316919283116328664075196706322101/2500000000000000000000000000000000000000) (694917790137800427583942308690796910381/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2330
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2331
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (34269332424318608336324319970520728706927/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (34269332424318608336324319970520728706927/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (172511309150564413114355279735073846098939/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (172511309150564413114355279735073846098939/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (171928985636078727397988439793838744816787/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (171928985636078727397988439793838744816787/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0145.bracket2331 BracketBatch0145.bracket2332 (171928985636078727397988439793838744816787/10000000000000000000000000000000000000000) (1741795198432362801894678427793506542733/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0145.bracket2331 BracketBatch0145.bracket2332
  (171928985636078727397988439793838744816787/10000000000000000000000000000000000000000) (1741795198432362801894678427793506542733/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2331
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2332
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (21563913643820551639294409966884230762367/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (21563913643820551639294409966884230762367/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (2713937862198887396606941890214016192693/156250000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2713937862198887396606941890214016192693/156250000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (43275416541411650812149945088596360303911/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (43275416541411650812149945088596360303911/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0145.bracket2332 BracketBatch0145.bracket2333 (43275416541411650812149945088596360303911/2500000000000000000000000000000000000000) (3492650896164769297873446843776242990411/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0145.bracket2332 BracketBatch0145.bracket2333
  (43275416541411650812149945088596360303911/2500000000000000000000000000000000000000) (3492650896164769297873446843776242990411/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2332
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2333
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (173692023180728793382844280973697036332349/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (173692023180728793382844280973697036332349/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (34977827787762417863672158972778503956481/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (34977827787762417863672158972778503956481/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (174290581059770441350602537918794778057377/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (174290581059770441350602537918794778057377/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0145.bracket2333 BracketBatch0145.bracket2334 (174290581059770441350602537918794778057377/10000000000000000000000000000000000000000) (700354212581174249590066938596013941521/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0145.bracket2333 BracketBatch0145.bracket2334
  (174290581059770441350602537918794778057377/10000000000000000000000000000000000000000) (700354212581174249590066938596013941521/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2333
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2334
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (87444569469406044659180397431946259891201/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (87444569469406044659180397431946259891201/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (176103000514529864270030843945108847699719/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (176103000514529864270030843945108847699719/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (350992139453341953588391638809001367482121/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (350992139453341953588391638809001367482121/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0145.bracket2334 BracketBatch0145.bracket2335 (350992139453341953588391638809001367482121/20000000000000000000000000000000000000000) (3510951516241778063415128643575299185419/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0145.bracket2334 BracketBatch0145.bracket2335
  (350992139453341953588391638809001367482121/20000000000000000000000000000000000000000) (3510951516241778063415128643575299185419/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2334
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2335
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0364.rows BesselBatch0364.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (44025750128632466067507710986277211924929/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (44025750128632466067507710986277211924929/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (35466792338054011882845392821500636210367/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (35466792338054011882845392821500636210367/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (353436962204799923684257808052612028751551/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (353436962204799923684257808052612028751551/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0291.rows ScalarLogs0291.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0145.bracket2335 BracketBatch0146.bracket2336 (353436962204799923684257808052612028751551/20000000000000000000000000000000000000000) (3520192879944151018909207893665674552743/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0145.bracket2335 BracketBatch0146.bracket2336
  (353436962204799923684257808052612028751551/20000000000000000000000000000000000000000) (3520192879944151018909207893665674552743/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2335
