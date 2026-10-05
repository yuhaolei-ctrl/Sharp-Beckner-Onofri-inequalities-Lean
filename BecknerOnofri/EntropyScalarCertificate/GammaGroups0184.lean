module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0230
public import BecknerOnofri.EntropyScalarCertificate.Bessel0231
public import BecknerOnofri.EntropyScalarCertificate.Bessel0603
public import BecknerOnofri.EntropyScalarCertificate.Bessel0604
public import BecknerOnofri.EntropyScalarCertificate.Brackets0092
public import BecknerOnofri.EntropyScalarCertificate.Logs0184
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1472
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (8669305077395196735666992437918650535047/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8669305077395196735666992437918650535047/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (867399429655335479324272835854117044459/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (867399429655335479324272835854117044459/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (17343299373948551528909720796459820979637/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17343299373948551528909720796459820979637/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0092.bracket1472 BracketBatch0092.bracket1473 (17343299373948551528909720796459820979637/10000000000000000000000000000000000000000) (660591438952756332816368482393053548387/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0092.bracket1472 BracketBatch0092.bracket1473
  (17343299373948551528909720796459820979637/10000000000000000000000000000000000000000) (660591438952756332816368482393053548387/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1472
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1473
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (17347988593106709586485456717082340889177/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17347988593106709586485456717082340889177/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (1084836164189678736163325348603774068047/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1084836164189678736163325348603774068047/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (34705367220141569365098662294742725977929/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (34705367220141569365098662294742725977929/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0092.bracket1473 BracketBatch0092.bracket1474 (34705367220141569365098662294742725977929/20000000000000000000000000000000000000000) (661103982848574772019341574399856814349/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0092.bracket1473 BracketBatch0092.bracket1474
  (34705367220141569365098662294742725977929/20000000000000000000000000000000000000000) (661103982848574772019341574399856814349/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1473
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1474
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (17357378627034859778613205577660385088749/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17357378627034859778613205577660385088749/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (17366780279746543049667919426579873149433/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17366780279746543049667919426579873149433/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (17362079453390701414140562502120129119091/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17362079453390701414140562502120129119091/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0092.bracket1474 BracketBatch0092.bracket1475 (17362079453390701414140562502120129119091/10000000000000000000000000000000000000000) (661617050781393029081723884879746133409/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0092.bracket1474 BracketBatch0092.bracket1475
  (17362079453390701414140562502120129119091/10000000000000000000000000000000000000000) (661617050781393029081723884879746133409/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1474
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1475
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (1736678027974654304966791942657987314943/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1736678027974654304966791942657987314943/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (17376193574472847905229815799369597300789/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17376193574472847905229815799369597300789/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (34742973854219390954897735225949470450219/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (34742973854219390954897735225949470450219/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0092.bracket1475 BracketBatch0092.bracket1476 (34742973854219390954897735225949470450219/20000000000000000000000000000000000000000) (331065321768238927768546605137348736323/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0092.bracket1475 BracketBatch0092.bracket1476
  (34742973854219390954897735225949470450219/20000000000000000000000000000000000000000) (331065321768238927768546605137348736323/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1475
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1476
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (8688096787236423952614907899684798650393/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8688096787236423952614907899684798650393/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (17385618534504434035089621734306989524807/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17385618534504434035089621734306989524807/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (34761812108977281940319437533676586825593/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (34761812108977281940319437533676586825593/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0092.bracket1476 BracketBatch0092.bracket1477 (34761812108977281940319437533676586825593/20000000000000000000000000000000000000000) (41415297618785334027807256599641282371/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0092.bracket1476 BracketBatch0092.bracket1477
  (34761812108977281940319437533676586825593/20000000000000000000000000000000000000000) (41415297618785334027807256599641282371/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1476
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1477
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (4346404633626108508772405433576747381201/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4346404633626108508772405433576747381201/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (17395055183191714640819987644206047047863/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17395055183191714640819987644206047047863/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (34780673717696148675909609378513036572667/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (34780673717696148675909609378513036572667/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0092.bracket1477 BracketBatch0092.bracket1478 (34780673717696148675909609378513036572667/20000000000000000000000000000000000000000) (1326318813323727654564571462044910701/20000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0092.bracket1477 BracketBatch0092.bracket1478
  (34780673717696148675909609378513036572667/20000000000000000000000000000000000000000) (1326318813323727654564571462044910701/20000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1477
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1478
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (869752759159585732040999382210302352393/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (869752759159585732040999382210302352393/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (17404503543945039413035711596835717628491/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17404503543945039413035711596835717628491/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (34799558727136754053855699241041764676351/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (34799558727136754053855699241041764676351/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0092.bracket1478 BracketBatch0092.bracket1479 (34799558727136754053855699241041764676351/20000000000000000000000000000000000000000) (663674578610056776596440222756206022937/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0092.bracket1478 BracketBatch0092.bracket1479
  (34799558727136754053855699241041764676351/20000000000000000000000000000000000000000) (663674578610056776596440222756206022937/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1478
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1479
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (2175562942993129926629463949604464703561/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2175562942993129926629463949604464703561/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0231.rows BesselBatch0231.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (870698182011743908052729135411874481413/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (870698182011743908052729135411874481413/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0604.rows BesselBatch0604.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (8704616796044979393522573576268301814187/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8704616796044979393522573576268301814187/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0184.rows ScalarLogs0184.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0092.bracket1479 BracketBatch0092.bracket1480 (8704616796044979393522573576268301814187/5000000000000000000000000000000000000000) (664190278536305714434752260523331295487/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0092.bracket1479 BracketBatch0092.bracket1480
  (8704616796044979393522573576268301814187/5000000000000000000000000000000000000000) (664190278536305714434752260523331295487/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1479
