module

public import BecknerOnofri.SpinPressureCertificateModel

@[expose] public section

/-!
# The Taylor model of the scalar encloses an explicit real expression

Lemma 5.20 (lem:section5-scalar-pressure). `scalarModel x` encloses `scalarValue t` at
`t = t₀ + s`, where `scalarValue` is the real expression evaluated by the certificate:
eq:12-explicit-scalar written with eq:12-pressure-cancellation, the moments
`m_s = (4(1-t) zˢ + t⁵)/(4 - 4t + t⁵)` and the logarithms `log(q_j/b_j)`. Its identification
with `pressureScalar t - t⁴/200` is `SpinPressureCertificateIdentity`.
-/

namespace BecknerOnofri.HighDim.Spin.PressureCertificate

open Real Finset

/-- The real number `n/d` of a rational pair. -/
noncomputable def ratVal (p : RatPair) : ℝ := (p.1 : ℝ) / (p.2 : ℝ)

theorem mem_ofPair {p : RatPair} (h : 0 < p.2) : (ofPair p).Mem (ratVal p) :=
  Iv.mem_ofRat p.1 p.2 h

theorem getD_pos {l : List RatPair} (h : ∀ p ∈ l, 0 < p.2) (i : ℕ) :
    0 < (l.getD i (0, 1)).2 := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : l[i]? with
  | none => simp
  | some p => simpa using h p (List.mem_of_getElem? hi)

theorem weightData_pos : ∀ p ∈ weightData, 0 < p.2 := by decide
theorem referenceData_pos : ∀ p ∈ referenceData, 0 < p.2 := by decide
theorem coordinateData_pos : ∀ p ∈ coordinateData, 0 < p.2 := by decide
theorem weightedMomentData_pos : ∀ row ∈ weightedMomentData, ∀ p ∈ row, 0 < p.2 := by decide

theorem weightedMomentData_getD_pos (j : ℕ) : ∀ p ∈ weightedMomentData.getD j [], 0 < p.2 := by
  rw [List.getD_eq_getElem?_getD]
  cases hj : weightedMomentData[j]? with
  | none => simp
  | some row => simpa using weightedMomentData_pos row (List.mem_of_getElem? hj)

/-! ### Real counterparts -/

/-- `z = t - t⁵/4`. -/
noncomputable def zR (t : ℝ) : ℝ := t - 1 / 4 * t ^ 5
/-- `4(1-t)`. -/
noncomputable def ppR (t : ℝ) : ℝ := 4 - 4 * t
/-- `4 - 4t + t⁵`. -/
noncomputable def denR (t : ℝ) : ℝ := ppR t + t ^ 5
/-- The moment `m_{i+1} = (4(1-t) z^{i+1} + t⁵)/(4 - 4t + t⁵)`. -/
noncomputable def momR (t : ℝ) (i : ℕ) : ℝ := (ppR t * zR t ^ (i + 1) + t ^ 5) * (denR t)⁻¹
/-- `∑ w_s m_s²`. -/
noncomputable def energyR (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 12, ratVal (weightData.getD i (0, 1)) * (momR t i * momR t i)
/-- `(1 - t²/2)⁻¹`. -/
noncomputable def halfR (t : ℝ) : ℝ := (1 - 1 / 2 * t ^ 2)⁻¹
/-- `η(t)`. -/
noncomputable def etaR (t : ℝ) : ℝ := (1 - t ^ 2) * (9 / 20 * t ^ 2 + 297 / 100 * t ^ 8) * halfR t
/-- `τ(t)`. -/
noncomputable def tauR (t : ℝ) : ℝ := 7 / 25 + etaR t
/-- `μ(t)`. -/
noncomputable def muR (t : ℝ) : ℝ := 5 / 2 * t ^ 3 * halfR t
/-- `log(q_j/b_j)`. -/
noncomputable def logRatioR (t : ℝ) (j : ℕ) : ℝ :=
  if j < 12 then
    (Real.log (ppR t) - Real.log (denR t)) +
      ((j : ℝ) * Real.log (1 + zR t) + (12 - (j : ℝ)) * Real.log (1 - zR t))
  else Real.log (ppR t * (1 + zR t) ^ 12 + 4096 * t ^ 5) - Real.log (denR t)
/-- `(Wq)_j = ∑ w_s A_{s,j} m_s`. -/
noncomputable def linR (t : ℝ) (row : List RatPair) : ℝ :=
  ∑ i ∈ Finset.range 12, ratVal (row.getD i (0, 1)) * momR t i
/-- The summand `b_j exp(E_j)`. -/
noncomputable def termR (t : ℝ) (j : ℕ) : ℝ :=
  ratVal (referenceData.getD j (0, 1)) *
    Real.exp ((-43 / 25 * logRatioR t j + 2 * linR t (weightedMomentData.getD j []) +
      muR t * (ratVal (coordinateData.getD j (0, 1)) - t)) * (tauR t)⁻¹)
/-- The pressure sum (eq:12-pressure-cancellation). -/
noncomputable def pressureR (t : ℝ) : ℝ := ∑ j ∈ Finset.range 13, termR t j
/-- The real expression enclosed by `scalarModel`. -/
noncomputable def scalarValue (t : ℝ) : ℝ :=
  energyR t + 12 * (3 / 40 * t ^ 4 + 33 / 200 * t ^ 10) -
    12 * (etaR t * (1 / 2 * ((1 + t) * Real.log (1 + t) + (1 - t) * Real.log (1 - t)))) -
    tauR t * Real.log (pressureR t) - 1 / 200 * t ^ 4

/-! ### Enclosures of the pieces -/

namespace TM

variable {x : Ctx} {s : ℝ}

theorem mem_sumRange {n : ℕ} {F : ℕ → TM} {f : ℕ → ℝ} (h : ∀ i < n, (F i).Mem s (f i)) :
    (sumRange n F).Mem s (∑ i ∈ Finset.range n, f i) := by
  have hF : List.Forall₂ (fun X g => X.Mem s g) ((List.range n).map F)
      ((List.range n).map f) := by
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr fun i hi => h i (List.mem_range.mp hi)
  refine mem_congr (mem_sum hF) ?_
  clear h hF
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

theorem mem_powList (hx : x.Adm s) {Z : TM} {z : ℝ} (hZ : Z.Mem s z) (n : ℕ) :
    ∀ {P : TM} {p : ℝ}, P.Mem s p → ∀ i < n,
      ((powList x Z n P).getD i (const Iv.zero)).Mem s (p * z ^ i) := by
  induction n with
  | zero => intro P p _ i hi; omega
  | succ n ih =>
    intro P p hP i hi
    cases i with
    | zero => simpa [powList] using hP
    | succ i =>
      have := ih (mem_mul hx hP hZ) i (by omega)
      simpa [powList, pow_succ', mul_assoc] using this

theorem mem_powModel (hx : x.Adm s) {Z : TM} {z : ℝ} (hZ : Z.Mem s z) (n : ℕ) :
    (powModel x Z n).Mem s (z ^ (n + 1)) := by
  induction n with
  | zero => simpa [powModel] using hZ
  | succ n ih => exact mem_congr (mem_mul hx ih hZ) (by ring)

theorem mem_linComb {cs : List RatPair} (hcs : ∀ p ∈ cs, 0 < p.2) {ms : List TM}
    {m : ℕ → ℝ} (hms : ∀ i < 12, (ms.getD i (const Iv.zero)).Mem s (m i)) :
    (linComb cs ms).Mem s (∑ i ∈ Finset.range 12, ratVal (cs.getD i (0, 1)) * m i) :=
  mem_sumRange fun i hi => mem_scal (mem_ofPair (getD_pos hcs i)) (hms i hi)

end TM

/-! ### The main enclosure -/

open TM in
theorem scalarModel_mem {x : Ctx} {s t₀ : ℝ} (hx : x.Adm s) (hmid : x.mid.Mem t₀) :
    (scalarModel x).Mem s (scalarValue (t₀ + s)) := by
  set t := t₀ + s
  have q14 : (Iv.ofRat 1 4).Mem (1 / 4) := by simpa using Iv.mem_ofRat 1 4 (by norm_num)
  have q12 : (Iv.ofRat 1 2).Mem (1 / 2) := by simpa using Iv.mem_ofRat 1 2 (by norm_num)
  have i4 : (Iv.ofInt 4).Mem 4 := by simpa using Iv.mem_ofInt 4
  set T := TM.var x
  have hT : T.Mem s t := mem_var hmid
  set T2 := TM.mul x T T
  have hT2 : T2.Mem s (t ^ 2) := mem_congr (mem_mul hx hT hT) (by ring)
  set T3 := TM.mul x T2 T
  have hT3 : T3.Mem s (t ^ 3) := mem_congr (mem_mul hx hT2 hT) (by ring)
  set T4 := TM.mul x T2 T2
  have hT4 : T4.Mem s (t ^ 4) := mem_congr (mem_mul hx hT2 hT2) (by ring)
  set T5 := TM.mul x T4 T
  have hT5 : T5.Mem s (t ^ 5) := mem_congr (mem_mul hx hT4 hT) (by ring)
  set T8 := TM.mul x T4 T4
  have hT8 : T8.Mem s (t ^ 8) := mem_congr (mem_mul hx hT4 hT4) (by ring)
  set T10 := TM.mul x T5 T5
  have hT10 : T10.Mem s (t ^ 10) := mem_congr (mem_mul hx hT5 hT5) (by ring)
  set Z := TM.sub T (TM.scal (Iv.ofRat 1 4) T5)
  have hZ : Z.Mem s (zR t) := mem_sub hT (mem_scal q14 hT5)
  set PP := TM.sub (TM.const (Iv.ofInt 4)) (TM.scal (Iv.ofInt 4) T)
  have hPP : PP.Mem s (ppR t) := mem_sub (mem_const i4) (mem_scal i4 hT)
  set Den := TM.add PP T5
  have hDen : Den.Mem s (denR t) := mem_add hPP hT5
  set IDen := TM.inv x Den
  have hIDen : IDen.Mem s (denR t)⁻¹ := mem_inv hx hDen
  set Ms := momentModels x PP T5 IDen Z
  have hMs : ∀ i < 12, (Ms.getD i (const Iv.zero)).Mem s (momR t i) := by
    intro i hi
    have hlen : i < (powList x Z 12 Z).length := by
      have : ∀ n (P : TM), (powList x Z n P).length = n := by
        intro n; induction n with
        | zero => intro P; rfl
        | succ n ih => intro P; simp [powList, ih]
      rw [this]; exact hi
    have hP := mem_powList hx hZ 12 hZ i hi
    simp only [Ms, momentModels, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hlen, Option.map_some, Option.getD_some]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some] at hP
    exact mem_congr (mem_mul hx (mem_add (mem_mul hx hPP hP) hT5) hIDen)
      (by simp only [momR]; ring)
  have hEnergy : (sumRange 12 fun i => TM.scal (ofPair (weightData.getD i (0, 1)))
      (TM.mul x (Ms.getD i (TM.const Iv.zero)) (Ms.getD i (TM.const Iv.zero)))).Mem s
      (energyR t) :=
    mem_sumRange fun i hi =>
      mem_scal (mem_ofPair (getD_pos weightData_pos i)) (mem_mul hx (hMs i hi) (hMs i hi))
  set Half := TM.inv x (TM.sub (TM.const Iv.one) (TM.scal (Iv.ofRat 1 2) T2))
  have hHalf : Half.Mem s (halfR t) :=
    mem_inv hx (mem_sub (mem_const Iv.mem_one) (mem_scal q12 hT2))
  set Eta := TM.mul x (TM.mul x (TM.sub (TM.const Iv.one) T2)
    (TM.add (TM.scal (Iv.ofRat 9 20) T2) (TM.scal (Iv.ofRat 297 100) T8))) Half
  have hEta : Eta.Mem s (etaR t) := by
    have h1 : (Iv.ofRat 9 20).Mem (9 / 20) := by simpa using Iv.mem_ofRat 9 20 (by norm_num)
    have h2 : (Iv.ofRat 297 100).Mem (297 / 100) := by
      simpa using Iv.mem_ofRat 297 100 (by norm_num)
    exact mem_mul hx (mem_mul hx (mem_sub (mem_const Iv.mem_one) hT2)
      (mem_add (mem_scal h1 hT2) (mem_scal h2 hT8))) hHalf
  set Tau := TM.add (TM.const (Iv.ofRat 7 25)) Eta
  have hTau : Tau.Mem s (tauR t) := by
    have h1 : (Iv.ofRat 7 25).Mem (7 / 25) := by simpa using Iv.mem_ofRat 7 25 (by norm_num)
    exact mem_add (mem_const h1) hEta
  set ITau := TM.inv x Tau
  have hITau : ITau.Mem s (tauR t)⁻¹ := mem_inv hx hTau
  set Mu := TM.mul x (TM.scal (Iv.ofRat 5 2) T3) Half
  have hMu : Mu.Mem s (muR t) := by
    have h1 : (Iv.ofRat 5 2).Mem (5 / 2) := by simpa using Iv.mem_ofRat 5 2 (by norm_num)
    exact mem_mul hx (mem_scal h1 hT3) hHalf
  set LogDen := TM.log x Den
  have hLogDen : LogDen.Mem s (Real.log (denR t)) := mem_log hx hDen
  set Common := TM.sub (TM.log x PP) LogDen
  have hCommon : Common.Mem s (Real.log (ppR t) - Real.log (denR t)) :=
    mem_sub (mem_log hx hPP) hLogDen
  set OneZ := TM.add (TM.const Iv.one) Z
  have hOneZ : OneZ.Mem s (1 + zR t) := mem_add (mem_const Iv.mem_one) hZ
  set LP := TM.log x OneZ
  have hLP : LP.Mem s (Real.log (1 + zR t)) := mem_log hx hOneZ
  set LM := TM.log x (TM.sub (TM.const Iv.one) Z)
  have hLM : LM.Mem s (Real.log (1 - zR t)) := mem_log hx (mem_sub (mem_const Iv.mem_one) hZ)
  set L12 := TM.sub (TM.log x (TM.add (TM.mul x PP (powModel x OneZ 11))
    (TM.scal (Iv.ofInt 4096) T5))) LogDen
  have hL12 : L12.Mem s (Real.log (ppR t * (1 + zR t) ^ 12 + 4096 * t ^ 5) -
      Real.log (denR t)) := by
    have h1 : (Iv.ofInt 4096).Mem 4096 := by simpa using Iv.mem_ofInt 4096
    exact mem_sub (mem_log hx (mem_add (mem_mul hx hPP (mem_powModel hx hOneZ 11))
      (mem_scal h1 hT5))) hLogDen
  have hLq : ∀ j : ℕ, (logRatioModel Common LP LM L12 j).Mem s (logRatioR t j) := by
    intro j
    by_cases hj : j < 12
    · simp only [logRatioModel, logRatioR, hj, ite_true]
      have h1 : (Iv.ofInt (j : ℤ)).Mem (j : ℝ) := by simpa using Iv.mem_ofInt (j : ℤ)
      have h2 : (Iv.ofInt (12 - (j : ℤ))).Mem (12 - (j : ℝ)) := by
        simpa using Iv.mem_ofInt (12 - (j : ℤ))
      exact mem_add hCommon (mem_add (mem_scal h1 hLP) (mem_scal h2 hLM))
    · simp only [logRatioModel, logRatioR, hj, ite_false]
      exact hL12
  have hPressure : (sumRange 13 fun j => pressureTerm x T Mu ITau
      (logRatioModel Common LP LM L12 j) Ms (referenceData.getD j (0, 1))
      (coordinateData.getD j (0, 1)) (weightedMomentData.getD j [])).Mem s (pressureR t) := by
    refine mem_sumRange fun j _ => ?_
    have h43 : (Iv.ofRat (-43) 25).Mem (-43 / 25) := by
      simpa using Iv.mem_ofRat (-43) 25 (by norm_num)
    have h2 : (Iv.ofInt 2).Mem 2 := by simpa using Iv.mem_ofInt 2
    have hlin := mem_linComb (weightedMomentData_getD_pos j) hMs
    exact mem_scal (mem_ofPair (getD_pos referenceData_pos j)) (mem_exp hx (mem_mul hx
      (mem_add (mem_add (mem_scal h43 (hLq j)) (mem_scal h2 hlin))
        (mem_mul hx hMu (mem_sub (mem_const (mem_ofPair (getD_pos coordinateData_pos j))) hT)))
      hITau))
  have hPsi : (TM.add (TM.scal (Iv.ofRat 3 40) T4) (TM.scal (Iv.ofRat 33 200) T10)).Mem s
      (3 / 40 * t ^ 4 + 33 / 200 * t ^ 10) := by
    have h1 : (Iv.ofRat 3 40).Mem (3 / 40) := by simpa using Iv.mem_ofRat 3 40 (by norm_num)
    have h2 : (Iv.ofRat 33 200).Mem (33 / 200) := by
      simpa using Iv.mem_ofRat 33 200 (by norm_num)
    exact mem_add (mem_scal h1 hT4) (mem_scal h2 hT10)
  have hOneT : (TM.add (TM.const Iv.one) T).Mem s (1 + t) := mem_add (mem_const Iv.mem_one) hT
  have hOneMT : (TM.sub (TM.const Iv.one) T).Mem s (1 - t) :=
    mem_sub (mem_const Iv.mem_one) hT
  have hBent := mem_scal q12 (mem_add (mem_mul hx hOneT (mem_log hx hOneT))
    (mem_mul hx hOneMT (mem_log hx hOneMT)))
  have h12 : (Iv.ofInt 12).Mem 12 := by simpa using Iv.mem_ofInt 12
  have h200 : (Iv.ofRat 1 200).Mem (1 / 200) := by simpa using Iv.mem_ofRat 1 200 (by norm_num)
  exact mem_sub (mem_sub (mem_sub (mem_add hEnergy (mem_scal h12 hPsi))
    (mem_scal h12 (mem_mul hx hEta hBent))) (mem_mul hx hTau (mem_log hx hPressure)))
    (mem_scal h200 hT4)

end BecknerOnofri.HighDim.Spin.PressureCertificate
