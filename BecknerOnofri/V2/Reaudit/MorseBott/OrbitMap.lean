module

public import BecknerOnofri.GeneralSobolevEmbedding
public import BecknerOnofri.Translation
public import BecknerOnofri.SmoothTorusSobolev
public import BecknerOnofri.SmoothTorusFourierDerivative
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

@[expose] public section

/-! # The translation-orbit map into the Sobolev space `H^s`

For `u ∈ ⋂_σ H^σ` and `s ≥ 0` the map `t ↦ u(· - t)` from `ℝ^d` (equivalently from `𝕋^d`) to the
Hilbert space `H^s` is realised in the weighted `ℓ²` coordinates `FourierL2 d = lp (fun _ => ℂ) 2`,
via the existing isometric encoding `encodeSobolev`, `‖encodeSobolev u‖ = ‖u‖_{H^s}`.  We prove that it
is `C^∞`, injective on the torus, has injective differential when all first-shell coefficients of `u`
are nonzero, is a topological embedding of the torus (compactness), and admits a smooth local left
inverse (the phases of the first-shell coefficients). -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexConjugate ContDiff ENNReal
open MeasureTheory

namespace BecknerOnofri.V2.Reaudit.MorseBott
open BecknerOnofri.HighDim

/-- The point of the torus with real coordinates `t`. -/
def lift {d : ℕ} (t : Fin d → ℝ) : Torus d := fun j => ((t j : ℝ) : UnitAddCircle)

theorem sobolevScale_add {d : ℕ} (a b : ℝ) (k : Frequency d) :
    sobolevScale (a + b) k = sobolevScale a k * sobolevScale b k := by
  unfold sobolevScale
  rw [← Real.rpow_add (by positivity)]
  congr 1
  ring

/-- Weighted `ℓ¹` summability of the Fourier coefficients of a function in all Sobolev spaces. -/
theorem summable_scaledFourier {d : ℕ} (hd : 0 < d) {u : Torus d → ℝ}
    (hall : ∀ σ : ℝ, 0 ≤ σ → InSobolev σ u) {a : ℝ} (ha : 0 ≤ a) :
    Summable (fun k : Frequency d => ‖scaledFourier a u k‖) := by
  have hq : (d : ℝ) / 2 < (d : ℝ) / 2 + 1 := by linarith
  have hsum := lp.summable_mul (by simpa using Real.HolderConjugate.two_two)
    (SobolevEmbedding.inverseScaleLp hd hq)
    (encodeSobolev u (hall (a + ((d : ℝ) / 2 + 1)) (by positivity)))
  refine hsum.congr (fun k => ?_)
  rw [← norm_mul]
  congr 1
  change (((sobolevScale ((d : ℝ) / 2 + 1) k)⁻¹ : ℝ) : ℂ) * scaledFourier (a + ((d : ℝ) / 2 + 1)) u k =
    scaledFourier a u k
  unfold scaledFourier
  generalize (d : ℝ) / 2 + 1 = q
  have hpos := sobolevScale_pos q k
  have hne : (sobolevScale q k : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [sobolevScale_add]
  push_cast
  field_simp


/-- The character `t ↦ e^{-2π i k·t}` of `ℝ^d`. -/
def phase {d : ℕ} (k : Frequency d) (t : Fin d → ℝ) : ℂ :=
  Complex.exp (((-(2 * Real.pi * ∑ i, (k i : ℝ) * t i) : ℝ) : ℂ) * Complex.I)

theorem mFourier_neg_lift {d : ℕ} (k : Frequency d) (t : Fin d → ℝ) :
    UnitAddTorus.mFourier (-k) (lift t) = phase k t := by
  unfold phase lift UnitAddTorus.mFourier
  simp only [ContinuousMap.coe_mk, Pi.neg_apply]
  have : ∀ i, fourier (-k i) ((t i : ℝ) : UnitAddCircle) =
      Complex.exp (((-(2 * Real.pi * (k i : ℝ) * t i) : ℝ) : ℂ) * Complex.I) := by
    intro i
    rw [fourier_coe_apply]
    congr 1
    push_cast
    ring
  simp only [this]
  rw [← Complex.exp_sum]
  congr 1
  rw [← Finset.sum_mul]
  push_cast
  simp [Finset.mul_sum, Finset.sum_neg_distrib, mul_assoc]

section Orbit
variable {d : ℕ} {s : ℝ} {u : Torus d → ℝ}

/-- The translation orbit map on the torus, valued in the weighted `ℓ²` model of `H^s`. -/
def orbitMapT (hu : InSobolev s u) (x : Torus d) : FourierL2 d :=
  encodeSobolev (translate u x) ((inSobolev_translate_iff s u x).mpr hu)

/-- The orbit map on `ℝ^d` (the lift of `orbitMapT` to the universal cover). -/
def orbitMap (hu : InSobolev s u) (t : Fin d → ℝ) : FourierL2 d := orbitMapT hu (lift t)

theorem orbitMapT_apply (hu : InSobolev s u) (x : Torus d) (k : Frequency d) :
    orbitMapT hu x k = scaledFourier s u k * UnitAddTorus.mFourier (-k) x := by
  change scaledFourier s (translate u x) k = _
  unfold scaledFourier
  rw [fourierCoeff_translate]
  ring

theorem orbitMap_apply (hu : InSobolev s u) (t : Fin d → ℝ) (k : Frequency d) :
    orbitMap hu t k = scaledFourier s u k * phase k t := by
  rw [orbitMap, orbitMapT_apply, mFourier_neg_lift]

theorem norm_orbitMapT (hu : InSobolev s u) (x : Torus d) :
    ‖orbitMapT hu x‖ = sobolevNorm s u := by
  rw [orbitMapT, encodeSobolev_norm, sobolevNorm_translate]

end Orbit


/-! ### Smoothness of the orbit map -/

/-- `l¹` weight of a frequency. -/
def lone {d : ℕ} (k : Frequency d) : ℝ := ∑ i, |(k i : ℝ)|

theorem abs_le_frequencyLength {d : ℕ} (k : Frequency d) (i : Fin d) : |(k i : ℝ)| ≤ frequencyLength k := by
  unfold frequencyLength
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (f := fun j => (k j : ℝ) ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)

theorem lone_pow_le {d : ℕ} (m : ℕ) (k : Frequency d) :
    (2 * Real.pi * lone k) ^ m ≤ (d : ℝ) ^ m * sobolevScale (m : ℝ) k := by
  have h1 : lone k ≤ d * frequencyLength k := by
    unfold lone
    calc ∑ i, |(k i : ℝ)| ≤ ∑ _i : Fin d, frequencyLength k :=
          Finset.sum_le_sum (fun i _ => abs_le_frequencyLength k i)
      _ = d * frequencyLength k := by simp
  have hL : 0 ≤ frequencyLength k := Real.sqrt_nonneg _
  have h2 : 2 * Real.pi * lone k ≤ d * sobolevScale 1 k := by
    have hs1 : 2 * Real.pi * frequencyLength k ≤ sobolevScale 1 k := by
      unfold sobolevScale
      rw [show ((1 : ℝ) / 2) = (1 / 2 : ℝ) from rfl, ← Real.sqrt_eq_rpow]
      apply Real.le_sqrt_of_sq_le
      nlinarith [sq_nonneg (2 * Real.pi * frequencyLength k)]
    calc 2 * Real.pi * lone k ≤ 2 * Real.pi * (d * frequencyLength k) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = d * (2 * Real.pi * frequencyLength k) := by ring
      _ ≤ d * sobolevScale 1 k := mul_le_mul_of_nonneg_left hs1 (by positivity)
  have h3 : sobolevScale 1 k ^ m = sobolevScale (m : ℝ) k := by
    unfold sobolevScale
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    ring
  calc (2 * Real.pi * lone k) ^ m ≤ ((d : ℝ) * sobolevScale 1 k) ^ m :=
        pow_le_pow_left₀ (by unfold lone; positivity) h2 m
    _ = (d : ℝ) ^ m * sobolevScale (m : ℝ) k := by rw [mul_pow, h3]

/-- The real-linear functional `t ↦ -2π k·t`. -/
def ell {d : ℕ} (k : Frequency d) : (Fin d → ℝ) →L[ℝ] ℝ :=
  -(2 * Real.pi) • ∑ i : Fin d, (k i : ℝ) • (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ)

theorem ell_apply {d : ℕ} (k : Frequency d) (t : Fin d → ℝ) :
    ell k t = -(2 * Real.pi * ∑ i, (k i : ℝ) * t i) := by
  simp [ell, Finset.mul_sum, smul_eq_mul]

theorem norm_ell_le {d : ℕ} (k : Frequency d) : ‖ell k‖ ≤ 2 * Real.pi * lone k := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by unfold lone; positivity)
  intro t
  rw [ell_apply, Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos Real.two_pi_pos]
  rw [mul_assoc (2 * Real.pi) (lone k)]
  refine mul_le_mul_of_nonneg_left ?_ Real.two_pi_pos.le
  calc |∑ i, (k i : ℝ) * t i| ≤ ∑ i, |(k i : ℝ) * t i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |(k i : ℝ)| * ‖t‖ := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (by simpa using norm_le_pi_norm t i) (abs_nonneg _)
    _ = lone k * ‖t‖ := by rw [← Finset.sum_mul]; rfl

/-- The unit-modulus exponential `θ ↦ e^{iθ}`. -/
def expI (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

theorem phase_eq_comp {d : ℕ} (k : Frequency d) : phase k = expI ∘ ell k := by
  funext t
  simp only [phase, expI, Function.comp_apply, ell_apply]

theorem contDiff_expI : ContDiff ℝ ∞ expI := by
  unfold expI
  exact Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.mul contDiff_const)

theorem iteratedDeriv_expI (n : ℕ) :
    iteratedDeriv n expI = fun θ => Complex.I ^ n * expI θ := by
  induction n with
  | zero => funext θ; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext θ
    have h1 : HasDerivAt (fun θ : ℝ => (θ : ℂ) * Complex.I) Complex.I θ := by
      simpa using (hasDerivAt_id θ).ofReal_comp.mul_const Complex.I
    have h2 : HasDerivAt (fun θ : ℝ => Complex.I ^ n * expI θ)
        (Complex.I ^ n * (expI θ * Complex.I)) θ :=
      (h1.cexp).const_mul (Complex.I ^ n)
    rw [h2.deriv, pow_succ]
    ring

theorem norm_iteratedFDeriv_expI (n : ℕ) (θ : ℝ) : ‖iteratedFDeriv ℝ n expI θ‖ = 1 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_expI]
  simp [expI, Complex.norm_exp_ofReal_mul_I]

theorem norm_iteratedFDeriv_phase_le {d : ℕ} (k : Frequency d) (m : ℕ) (t : Fin d → ℝ) :
    ‖iteratedFDeriv ℝ m (phase k) t‖ ≤ ‖ell k‖ ^ m := by
  rw [phase_eq_comp, ContinuousLinearMap.iteratedFDeriv_comp_right (ell k) contDiff_expI t
    (by exact_mod_cast le_top)]
  calc _ ≤ ‖iteratedFDeriv ℝ m expI (ell k t)‖ * ∏ _i : Fin m, ‖ell k‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖ell k‖ ^ m := by rw [norm_iteratedFDeriv_expI]; simp


theorem norm_scaledFourier {d : ℕ} (a : ℝ) (u : Torus d → ℝ) (k : Frequency d) :
    ‖scaledFourier a u k‖ = sobolevScale a k * ‖fourierCoeff u k‖ := by
  unfold scaledFourier
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sobolevScale_pos a k)]

/-- Insertion of a coordinate: `w ↦ c w e_k` in the `ℓ²` model. -/
def insertCLM {d : ℕ} (c : ℂ) (k : Frequency d) : ℂ →L[ℝ] FourierL2 d :=
  (lp.singleContinuousLinearMap ℝ (fun _ : Frequency d => ℂ) 2 k).comp
    ((ContinuousLinearMap.mul ℂ ℂ c).restrictScalars ℝ)

theorem insertCLM_apply {d : ℕ} (c : ℂ) (k : Frequency d) (w : ℂ) :
    insertCLM c k w = lp.single 2 k (c * w) := rfl

theorem norm_insertCLM_le {d : ℕ} (c : ℂ) (k : Frequency d) : ‖insertCLM c k‖ ≤ ‖c‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg c)
  intro w
  rw [insertCLM_apply, lp.norm_single (by norm_num), norm_mul]

section Orbit
variable {d : ℕ} {s : ℝ} {u : Torus d → ℝ}

theorem orbitMap_eq_tsum (hu : InSobolev s u) (t : Fin d → ℝ) :
    orbitMap hu t = ∑' k : Frequency d, insertCLM (scaledFourier s u k) k (phase k t) := by
  have h := (lp.hasSum_single (p := 2) (E := fun _ : Frequency d => ℂ) (by norm_num)
    (orbitMap hu t)).tsum_eq
  rw [← h]
  refine tsum_congr (fun k => ?_)
  rw [insertCLM_apply, orbitMap_apply]

/-- **Smoothness of the orbit map.**  For `u` in every Sobolev space the translation orbit
`t ↦ u(· - t)` is a `C^∞` map `ℝ^d → H^s` (`s ≥ 0`). -/
theorem orbitMap_contDiff (hd : 0 < d) (hall : ∀ σ : ℝ, 0 ≤ σ → InSobolev σ u) (hs : 0 ≤ s)
    (hu : InSobolev s u) : ContDiff ℝ ∞ (orbitMap hu) := by
  have hfun : orbitMap hu = fun t => ∑' k : Frequency d,
      insertCLM (scaledFourier s u k) k (phase k t) := funext (orbitMap_eq_tsum hu)
  rw [hfun]
  refine contDiff_tsum (N := ⊤) (v := fun m k => (d : ℝ) ^ m * ‖scaledFourier (s + m) u k‖) ?_ ?_ ?_
  · intro k
    have hph : ContDiff ℝ ∞ (phase k) := by
      rw [phase_eq_comp]
      exact contDiff_expI.comp (ell k).contDiff
    exact (insertCLM (scaledFourier s u k) k).contDiff.comp hph
  · intro m _
    exact (summable_scaledFourier hd hall (by positivity)).mul_left _
  · intro m k t _
    have hph : ContDiff ℝ ∞ (phase k) := by
      rw [phase_eq_comp]
      exact contDiff_expI.comp (ell k).contDiff
    have h1 := ContinuousLinearMap.norm_iteratedFDeriv_comp_left
      (insertCLM (scaledFourier s u k) k) (hph.contDiffAt (x := t)) (n := m)
      (by exact_mod_cast le_top)
    refine (h1.trans ?_)
    have h2 := norm_iteratedFDeriv_phase_le k m t
    have h3 : ‖ell k‖ ^ m ≤ (2 * Real.pi * lone k) ^ m :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_ell_le k) m
    have h4 := lone_pow_le m k
    have h5 : ‖scaledFourier (s + m) u k‖ = sobolevScale s k * sobolevScale (m : ℝ) k * ‖fourierCoeff u k‖ := by
      rw [norm_scaledFourier, sobolevScale_add]
    have h6 : ‖scaledFourier s u k‖ = sobolevScale s k * ‖fourierCoeff u k‖ := norm_scaledFourier s u k
    calc ‖insertCLM (scaledFourier s u k) k‖ * ‖iteratedFDeriv ℝ m (phase k) t‖
        ≤ ‖scaledFourier s u k‖ * ((d : ℝ) ^ m * sobolevScale (m : ℝ) k) := by
          refine mul_le_mul (norm_insertCLM_le _ _) ?_ (norm_nonneg _) (norm_nonneg _)
          exact (h2.trans h3).trans h4
      _ = (d : ℝ) ^ m * ‖scaledFourier (s + m) u k‖ := by rw [h5, h6]; ring

end Orbit


/-! ### First-shell coordinates: injectivity of the differential, of the orbit, embedding -/

theorem axisFrequency_eq_single' {d : ℕ} (i : Fin d) : axisFrequency i = Pi.single i 1 := by
  funext l
  by_cases h : l = i <;> simp [axisFrequency, h]

theorem mFourier_axisFrequency {d : ℕ} (i : Fin d) (x : Torus d) :
    UnitAddTorus.mFourier (axisFrequency i) x = fourier 1 (x i) := by
  rw [axisFrequency_eq_single', UnitAddTorus.mFourier_single]

theorem fourier_one_injective : Function.Injective (fun y : UnitAddCircle => fourier 1 y) := by
  intro x y h
  simp only [fourier_apply, one_smul] at h
  exact AddCircle.injective_toCircle (by norm_num) (Circle.coe_inj.mp h)

theorem phase_axis {d : ℕ} (j : Fin d) (t : Fin d → ℝ) :
    phase (axisFrequency j) t = expI (-(2 * Real.pi * t j)) := by
  unfold phase expI
  congr 3
  simp [axisFrequency]

/-- `ev_j`: the `e_j`-coordinate of an element of the `ℓ²` model, as a real-linear functional. -/
def evAxis {d : ℕ} (j : Fin d) : FourierL2 d →L[ℝ] ℂ :=
  ((lp.evalCLM ℂ (fun _ : Frequency d => ℂ) 2 (axisFrequency j)).restrictScalars ℝ)

theorem evAxis_apply {d : ℕ} (j : Fin d) (a : FourierL2 d) : evAxis j a = a (axisFrequency j) := rfl

section Orbit2
variable {d : ℕ} {s : ℝ} {u : Torus d → ℝ}

theorem scaled_axis_ne_zero (hfull : ∀ j : Fin d, fourierCoeff u (axisFrequency j) ≠ 0) (j : Fin d) :
    scaledFourier s u (axisFrequency j) ≠ 0 := by
  unfold scaledFourier
  exact mul_ne_zero (by exact_mod_cast (sobolevScale_pos s _).ne') (hfull j)

theorem ell_axis {d : ℕ} (j : Fin d) (h : Fin d → ℝ) :
    ell (axisFrequency j) h = -(2 * Real.pi * h j) := by
  rw [ell_apply]
  congr 2
  simp [axisFrequency, ite_mul]

/-- The `e_j`-coordinate of the orbit map is `c_j e^{-2π i t_j}`; it has the explicit derivative. -/
theorem hasFDerivAt_axis_coord (hu : InSobolev s u) (j : Fin d) (t : Fin d → ℝ) :
    HasFDerivAt (fun t => evAxis j (orbitMap hu t))
      (scaledFourier s u (axisFrequency j) • (expI (ell (axisFrequency j) t) •
        (ContinuousLinearMap.smulRight (ell (axisFrequency j)) Complex.I : (Fin d → ℝ) →L[ℝ] ℂ))) t := by
  have h1 : HasFDerivAt (fun t : Fin d → ℝ => ((ell (axisFrequency j) t : ℝ) : ℂ) * Complex.I)
      (ContinuousLinearMap.smulRight (ell (axisFrequency j)) Complex.I : (Fin d → ℝ) →L[ℝ] ℂ) t := by
    have := (ContinuousLinearMap.smulRight (ell (axisFrequency j)) Complex.I :
      (Fin d → ℝ) →L[ℝ] ℂ).hasFDerivAt (x := t)
    convert this using 1
    funext t
    simp [Complex.real_smul]
  have h2 := (h1.cexp).const_mul (scaledFourier s u (axisFrequency j))
  have heq : (fun t => evAxis j (orbitMap hu t)) = fun t =>
      scaledFourier s u (axisFrequency j) * Complex.exp (((ell (axisFrequency j) t : ℝ) : ℂ) * Complex.I) := by
    funext t
    rw [evAxis_apply, orbitMap_apply, phase_eq_comp]
    rfl
  rw [heq]
  convert h2 using 1
  ext h
  simp [expI]

/-- **The differential of the orbit map is injective.** -/
theorem fderiv_orbitMap_injective (hd : 0 < d) (hall : ∀ σ : ℝ, 0 ≤ σ → InSobolev σ u)
    (hs : 0 ≤ s) (hu : InSobolev s u)
    (hfull : ∀ j : Fin d, fourierCoeff u (axisFrequency j) ≠ 0) (t : Fin d → ℝ) :
    Function.Injective (fderiv ℝ (orbitMap hu) t) := by
  rw [injective_iff_map_eq_zero]
  intro h hh
  have hF : HasFDerivAt (orbitMap hu) (fderiv ℝ (orbitMap hu) t) t :=
    ((orbitMap_contDiff hd hall hs hu).differentiable (by simp)).differentiableAt.hasFDerivAt
  funext j
  have h3 := (evAxis j).hasFDerivAt.comp t hF
  have h4 := h3.unique (hasFDerivAt_axis_coord hu j t)
  have h5 := congrArg (fun L => L h) h4
  simp only [ContinuousLinearMap.comp_apply, hh, map_zero] at h5
  simp only [smul_apply, ContinuousLinearMap.smulRight_apply, ell_axis,
    smul_eq_mul, Complex.real_smul] at h5
  have hc := scaled_axis_ne_zero (s := s) hfull j
  have he : expI (-(2 * Real.pi * t j)) ≠ 0 := by
    unfold expI; exact Complex.exp_ne_zero _
  have h6 : (((-(2 * Real.pi * h j)) : ℝ) : ℂ) = 0 := by
    have h7 : scaledFourier s u (axisFrequency j) * (expI (-(2 * Real.pi * t j)) *
        (((-(2 * Real.pi * h j)) : ℝ) * Complex.I)) = 0 := h5.symm
    rcases mul_eq_zero.mp h7 with h8 | h8
    · exact (hc h8).elim
    rcases mul_eq_zero.mp h8 with h9 | h9
    · exact (he h9).elim
    rcases mul_eq_zero.mp h9 with h10 | h10
    · exact h10
    · exact (Complex.I_ne_zero h10).elim
  have h11 : -(2 * Real.pi * h j) = 0 := by exact_mod_cast h6
  have h12 : h j = 0 := by
    have := Real.pi_pos
    nlinarith
  simpa using h12


/-- **Injectivity of the orbit on the torus.** -/
theorem orbitMapT_injective (hu : InSobolev s u)
    (hfull : ∀ j : Fin d, fourierCoeff u (axisFrequency j) ≠ 0) :
    Function.Injective (orbitMapT hu) := by
  intro x y hxy
  funext j
  have h1 := congrArg (fun a : FourierL2 d => a (axisFrequency j)) hxy
  simp only [orbitMapT_apply] at h1
  have h2 := mul_left_cancel₀ (scaled_axis_ne_zero (s := s) hfull j) h1
  rw [UnitAddTorus.mFourier_neg, UnitAddTorus.mFourier_neg, mFourier_axisFrequency,
    mFourier_axisFrequency] at h2
  exact fourier_one_injective ((starRingEnd ℂ).injective h2)

theorem orbitMapT_eq_tsum (hu : InSobolev s u) (x : Torus d) :
    orbitMapT hu x = ∑' k : Frequency d,
      insertCLM (scaledFourier s u k) k (UnitAddTorus.mFourier (-k) x) := by
  have h := (lp.hasSum_single (p := 2) (E := fun _ : Frequency d => ℂ) (by norm_num)
    (orbitMapT hu x)).tsum_eq
  rw [← h]
  refine tsum_congr (fun k => ?_)
  rw [insertCLM_apply, orbitMapT_apply]

theorem continuous_orbitMapT (hd : 0 < d) (hall : ∀ σ : ℝ, 0 ≤ σ → InSobolev σ u) (hs : 0 ≤ s)
    (hu : InSobolev s u) : Continuous (orbitMapT hu) := by
  have hfun : orbitMapT hu = fun x => ∑' k : Frequency d,
      insertCLM (scaledFourier s u k) k (UnitAddTorus.mFourier (-k) x) := funext (orbitMapT_eq_tsum hu)
  rw [hfun]
  refine continuous_tsum (u := fun k => ‖scaledFourier s u k‖) (fun k => ?_)
    (summable_scaledFourier hd hall hs) (fun k x => ?_)
  · exact (insertCLM (scaledFourier s u k) k).continuous.comp (UnitAddTorus.mFourier (-k)).continuous
  · calc ‖insertCLM (scaledFourier s u k) k (UnitAddTorus.mFourier (-k) x)‖
        ≤ ‖insertCLM (scaledFourier s u k) k‖ * ‖UnitAddTorus.mFourier (-k) x‖ :=
          (insertCLM (scaledFourier s u k) k).le_opNorm _
      _ ≤ ‖scaledFourier s u k‖ * 1 := by
          rw [mFourier_norm_apply]
          exact mul_le_mul_of_nonneg_right (norm_insertCLM_le _ _) (by norm_num)
      _ = ‖scaledFourier s u k‖ := mul_one _

/-- **Compactness gives an embedding**: the orbit map of the torus is a closed topological
embedding into `H^s`. -/
theorem isClosedEmbedding_orbitMapT (hd : 0 < d) (hall : ∀ σ : ℝ, 0 ≤ σ → InSobolev σ u)
    (hs : 0 ≤ s) (hu : InSobolev s u)
    (hfull : ∀ j : Fin d, fourierCoeff u (axisFrequency j) ≠ 0) :
    Topology.IsClosedEmbedding (orbitMapT hu) :=
  (continuous_orbitMapT hd hall hs hu).isClosedEmbedding (orbitMapT_injective hu hfull)


/-! ### The smooth left inverse: phases of the first-shell coefficients -/

/-- Open domain on which all first-shell coordinates have a logarithmic branch relative to `t₀`. -/
def phaseDomain (hu : InSobolev s u) (t₀ : Fin d → ℝ) : Set (FourierL2 d) :=
  {a | ∀ j : Fin d, a (axisFrequency j) / orbitMap hu t₀ (axisFrequency j) ∈ Complex.slitPlane}

/-- The phase retraction `a ↦ t₀ - (2π)⁻¹ Im log (a(e_j)/ orbit(t₀)(e_j))_j`. -/
def phaseCoord (hu : InSobolev s u) (t₀ : Fin d → ℝ) (a : FourierL2 d) : Fin d → ℝ :=
  fun j => t₀ j - (1 / (2 * Real.pi)) *
    (Complex.log (a (axisFrequency j) / orbitMap hu t₀ (axisFrequency j))).im

theorem isOpen_phaseDomain (hu : InSobolev s u) (t₀ : Fin d → ℝ) : IsOpen (phaseDomain hu t₀) := by
  have : phaseDomain hu t₀ = ⋂ j : Fin d, {a : FourierL2 d |
      a (axisFrequency j) / orbitMap hu t₀ (axisFrequency j) ∈ Complex.slitPlane} := by
    ext a; simp [phaseDomain]
  rw [this]
  refine isOpen_iInter_of_finite (fun j => ?_)
  have hc : Continuous (fun a : FourierL2 d => a (axisFrequency j) / orbitMap hu t₀ (axisFrequency j)) :=
    (evAxis j).continuous.div_const _
  exact Complex.isOpen_slitPlane.preimage hc

theorem contDiffOn_phaseCoord (hu : InSobolev s u) (t₀ : Fin d → ℝ) :
    ContDiffOn ℝ ∞ (phaseCoord hu t₀) (phaseDomain hu t₀) := by
  rw [contDiffOn_pi]
  intro j
  have hlog : ContDiffOn ℝ ∞ (fun z : ℂ => Complex.log z) Complex.slitPlane := fun z hz =>
    ((Complex.contDiffAt_log hz).contDiffWithinAt).restrict_scalars ℝ
  have hg : ContDiff ℝ ∞ (fun a : FourierL2 d =>
      a (axisFrequency j) / orbitMap hu t₀ (axisFrequency j)) :=
    ((evAxis j).contDiff).div_const _
  have hcomp : ContDiffOn ℝ ∞ (fun a : FourierL2 d =>
      Complex.log (a (axisFrequency j) / orbitMap hu t₀ (axisFrequency j))) (phaseDomain hu t₀) :=
    hlog.comp hg.contDiffOn (fun a ha => ha j)
  have him := Complex.imCLM.contDiff.comp_contDiffOn hcomp
  exact contDiffOn_const.sub (contDiffOn_const.mul him)

theorem orbitMap_axis_ratio (hu : InSobolev s u)
    (hfull : ∀ j : Fin d, fourierCoeff u (axisFrequency j) ≠ 0) (t₀ t : Fin d → ℝ) (j : Fin d) :
    orbitMap hu t (axisFrequency j) / orbitMap hu t₀ (axisFrequency j) =
      Complex.exp (((-(2 * Real.pi * (t j - t₀ j)) : ℝ) : ℂ) * Complex.I) := by
  have hc := scaled_axis_ne_zero (s := s) hfull j
  rw [orbitMap_apply, orbitMap_apply, phase_axis, phase_axis]
  unfold expI
  rw [mul_div_mul_left _ _ hc, ← Complex.exp_sub]
  congr 1
  push_cast
  ring

theorem exists_smooth_left_inverse (hu : InSobolev s u)
    (hfull : ∀ j : Fin d, fourierCoeff u (axisFrequency j) ≠ 0) (t₀ : Fin d → ℝ) :
    IsOpen (phaseDomain hu t₀) ∧ orbitMap hu t₀ ∈ phaseDomain hu t₀ ∧
      ContDiffOn ℝ ∞ (phaseCoord hu t₀) (phaseDomain hu t₀) ∧
      ∀ t : Fin d → ℝ, (∀ j, |t j - t₀ j| < 1 / 2) →
        orbitMap hu t ∈ phaseDomain hu t₀ ∧ phaseCoord hu t₀ (orbitMap hu t) = t := by
  have key : ∀ t : Fin d → ℝ, (∀ j, |t j - t₀ j| < 1 / 2) → ∀ j : Fin d,
      (orbitMap hu t (axisFrequency j) / orbitMap hu t₀ (axisFrequency j) ∈ Complex.slitPlane) ∧
      (Complex.log (orbitMap hu t (axisFrequency j) / orbitMap hu t₀ (axisFrequency j))).im =
        -(2 * Real.pi * (t j - t₀ j)) := by
    intro t ht j
    have hj := ht j
    rw [abs_lt] at hj
    have hθ1 : -Real.pi < -(2 * Real.pi * (t j - t₀ j)) := by nlinarith [Real.pi_pos]
    have hθ2 : -(2 * Real.pi * (t j - t₀ j)) < Real.pi := by nlinarith [Real.pi_pos]
    rw [orbitMap_axis_ratio hu hfull]
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_slitPlane_iff_arg]
      refine ⟨?_, Complex.exp_ne_zero _⟩
      rw [Complex.arg_exp_mul_I, (toIocMod_eq_self _).2 ⟨hθ1, by linarith [Real.pi_pos]⟩]
      exact hθ2.ne
    · rw [Complex.log_exp (by simpa using hθ1) (by simpa using hθ2.le)]
      simp
  refine ⟨isOpen_phaseDomain hu t₀, ?_, contDiffOn_phaseCoord hu t₀, fun t ht => ⟨fun j => (key t ht j).1, ?_⟩⟩
  · intro j
    have := (key t₀ (fun j => by simp) j).1
    exact this
  · funext j
    unfold phaseCoord
    rw [(key t ht j).2]
    field_simp
    ring


/-! ### The differential of the orbit map in coordinates -/

/-- The `k`-th coordinate of the `ℓ²` model, real-linear. -/
def evCoord {d : ℕ} (k : Frequency d) : FourierL2 d →L[ℝ] ℂ :=
  ((lp.evalCLM ℂ (fun _ : Frequency d => ℂ) 2 k).restrictScalars ℝ)

theorem evCoord_apply {d : ℕ} (k : Frequency d) (a : FourierL2 d) : evCoord k a = a k := rfl

theorem hasFDerivAt_coord (hu : InSobolev s u) (k : Frequency d) (t : Fin d → ℝ) :
    HasFDerivAt (fun t => evCoord k (orbitMap hu t))
      (scaledFourier s u k • (expI (ell k t) •
        (ContinuousLinearMap.smulRight (ell k) Complex.I : (Fin d → ℝ) →L[ℝ] ℂ))) t := by
  have h1 : HasFDerivAt (fun t : Fin d → ℝ => ((ell k t : ℝ) : ℂ) * Complex.I)
      (ContinuousLinearMap.smulRight (ell k) Complex.I : (Fin d → ℝ) →L[ℝ] ℂ) t := by
    have := (ContinuousLinearMap.smulRight (ell k) Complex.I :
      (Fin d → ℝ) →L[ℝ] ℂ).hasFDerivAt (x := t)
    convert this using 1
    funext t
    simp [Complex.real_smul]
  have h2 := (h1.cexp).const_mul (scaledFourier s u k)
  have heq : (fun t => evCoord k (orbitMap hu t)) = fun t =>
      scaledFourier s u k * Complex.exp (((ell k t : ℝ) : ℂ) * Complex.I) := by
    funext t
    rw [evCoord_apply, orbitMap_apply, phase_eq_comp]
    rfl
  rw [heq]
  convert h2 using 1
  ext h
  simp [expI]

/-- **The differential of the orbit map**: in the coordinate `k`,
`D Γ(t) h = (-2π i k·h) Γ(t)_k`. -/
theorem fderiv_orbitMap_apply (hd : 0 < d) (hall : ∀ σ : ℝ, 0 ≤ σ → InSobolev σ u)
    (hs : 0 ≤ s) (hu : InSobolev s u) (t h : Fin d → ℝ) (k : Frequency d) :
    fderiv ℝ (orbitMap hu) t h k = orbitMap hu t k * (((ell k h : ℝ) : ℂ) * Complex.I) := by
  have hF : HasFDerivAt (orbitMap hu) (fderiv ℝ (orbitMap hu) t) t :=
    ((orbitMap_contDiff hd hall hs hu).differentiable (by simp)).differentiableAt.hasFDerivAt
  have h3 := (evCoord k).hasFDerivAt.comp t hF
  have h4 := h3.unique (hasFDerivAt_coord hu k t)
  have h5 := congrArg (fun L => L h) h4
  simp only [ContinuousLinearMap.comp_apply, evCoord_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, Complex.real_smul] at h5
  rw [h5, orbitMap_apply, phase_eq_comp]
  simp only [Function.comp_apply, expI]
  ring

end Orbit2

end BecknerOnofri.V2.Reaudit.MorseBott

#print axioms BecknerOnofri.V2.Reaudit.MorseBott.orbitMap_contDiff
#print axioms BecknerOnofri.V2.Reaudit.MorseBott.fderiv_orbitMap_injective
#print axioms BecknerOnofri.V2.Reaudit.MorseBott.orbitMapT_injective
#print axioms BecknerOnofri.V2.Reaudit.MorseBott.isClosedEmbedding_orbitMapT
#print axioms BecknerOnofri.V2.Reaudit.MorseBott.exists_smooth_left_inverse
#print axioms BecknerOnofri.V2.Reaudit.MorseBott.fderiv_orbitMap_apply
