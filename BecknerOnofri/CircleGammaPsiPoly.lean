module

public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

/-! Exact rational polynomial arithmetic and a kernel-checkable Bernstein
positivity test, used for the finite certificates in the proof of Lemma 5.17
(`lem:section5-global-small-gamma`). Polynomials are lists of rational
coefficients, lowest degree first. The scaled Bernstein coefficients of `p` on
`[0,1]` are the coefficients `c k` with `p s = ∑ c k s^k (1-s)^(n-k)`. -/
noncomputable section
namespace BecknerOnofri.HighDim.CircleScalar.GammaPoly

/-- Horner evaluation of a rational coefficient list at a real point. -/
def eval : List ℚ → ℝ → ℝ
  | [], _ => 0
  | a :: p, x => (a : ℝ) + x * eval p x

def add : List ℚ → List ℚ → List ℚ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: add p q

def smul (c : ℚ) (p : List ℚ) : List ℚ := p.map (c * ·)

def mul : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | a :: p, q => add (smul a q) (0 :: mul p q)

def sub (p q : List ℚ) : List ℚ := add p (smul (-1) q)

/-- Substitution `x ↦ x^2`. -/
def subsq : List ℚ → List ℚ
  | [] => []
  | a :: p => a :: 0 :: subsq p

def npow (p : List ℚ) : ℕ → List ℚ
  | 0 => [1]
  | n + 1 => mul p (npow p n)

/-- Formal derivative. -/
def derivL : List ℚ → List ℚ
  | [] => []
  | _ :: p => add p (0 :: derivL p)

/-- The coefficients of `(1+X)^m`. -/
def binom : ℕ → List ℚ
  | 0 => [1]
  | m + 1 => add (binom m) (0 :: binom m)

/-- Scaled Bernstein coefficients on `[0,1]`. -/
def toBern : List ℚ → List ℚ
  | [] => []
  | a :: p => add (smul a (binom p.length)) (0 :: toBern p)

/-- The polynomial `s ↦ p (lo + w s)`. -/
def affine (lo w : ℚ) : List ℚ → List ℚ
  | [] => []
  | a :: p => add [a] (mul [lo, w] (affine lo w p))

/-- Strict positivity test on `[lo,hi]` by scaled Bernstein coefficients. -/
def posCheck (p : List ℚ) (lo hi : ℚ) : Bool :=
  decide (lo < hi) && !(toBern (affine lo (hi - lo) p)).isEmpty &&
    (toBern (affine lo (hi - lo) p)).all (fun c => decide (0 < c))

/-- Homogeneous evaluation `∑ c k a^k b^(n-k)`. -/
def hom : List ℚ → ℕ → ℝ → ℝ → ℝ
  | [], _, _, _ => 0
  | c :: cs, n, a, b => (c : ℝ) * b ^ n + a * hom cs (n - 1) a b

theorem hom_cons (c : ℚ) (cs : List ℚ) (n : ℕ) (a b : ℝ) :
    hom (c :: cs) n a b = (c : ℝ) * b ^ n + a * hom cs (n - 1) a b := rfl

@[simp] theorem eval_nil (x : ℝ) : eval [] x = 0 := rfl

@[simp] theorem eval_cons (a : ℚ) (p : List ℚ) (x : ℝ) :
    eval (a :: p) x = a + x * eval p x := rfl

@[simp] theorem eval_add (p q : List ℚ) (x : ℝ) :
    eval (add p q) x = eval p x + eval q x := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih =>
    cases q with
    | nil => simp [add]
    | cons b q => simp [add, ih]; ring

@[simp] theorem eval_smul (c : ℚ) (p : List ℚ) (x : ℝ) :
    eval (smul c p) x = c * eval p x := by
  induction p with
  | nil => simp [smul]
  | cons a p ih => simp only [smul, List.map_cons] at ih ⊢; simp [ih]; ring

@[simp] theorem eval_mul (p q : List ℚ) (x : ℝ) :
    eval (mul p q) x = eval p x * eval q x := by
  induction p with
  | nil => simp [mul]
  | cons a p ih => simp [mul, ih]; ring

@[simp] theorem eval_sub (p q : List ℚ) (x : ℝ) :
    eval (sub p q) x = eval p x - eval q x := by
  simp [sub]; ring

@[simp] theorem eval_subsq (p : List ℚ) (x : ℝ) :
    eval (subsq p) x = eval p (x ^ 2) := by
  induction p with
  | nil => simp [subsq]
  | cons a p ih => simp [subsq, ih]; ring

@[simp] theorem eval_npow (p : List ℚ) (n : ℕ) (x : ℝ) :
    eval (npow p n) x = eval p x ^ n := by
  induction n with
  | zero => simp [npow]
  | succ n ih => simp [npow, ih]; ring

theorem hasDerivAt_eval (p : List ℚ) (x : ℝ) :
    HasDerivAt (eval p) (eval (derivL p) x) x := by
  induction p with
  | nil =>
    have he : eval [] = fun _ => (0 : ℝ) := funext fun _ => rfl
    rw [he]
    simpa [derivL] using hasDerivAt_const x (0 : ℝ)
  | cons a p ih =>
    have he : eval (a :: p) = fun y => (a : ℝ) + y * eval p y := funext fun _ => rfl
    rw [he]
    have h := ((hasDerivAt_id' x).mul ih).const_add (a : ℝ)
    have e2 : eval (derivL (a :: p)) x = 1 * eval p x + x * eval (derivL p) x := by
      simp [derivL]
    rw [e2]
    exact h

theorem eval_affine (lo w : ℚ) (p : List ℚ) (s : ℝ) :
    eval (affine lo w p) s = eval p (lo + w * s) := by
  induction p with
  | nil => simp [affine]
  | cons a p ih =>
    simp only [affine, eval_add, eval_mul, eval_cons, eval_nil, ih]
    ring

theorem eval_drop (k : ℕ) (p : List ℚ) (h : (p.take k).all (· = 0) = true) (x : ℝ) :
    eval p x = x ^ k * eval (p.drop k) x := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    cases p with
    | nil => simp
    | cons a p =>
      simp only [List.take_succ_cons, List.all_cons, Bool.and_eq_true,
        decide_eq_true_eq] at h
      simp [h.1, ih p h.2]; ring

theorem length_add (p q : List ℚ) : (add p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih =>
    cases q with
    | nil => simp [add]
    | cons b q => simp [add, ih, Nat.succ_max_succ]

theorem length_binom (m : ℕ) : (binom m).length = m + 1 := by
  induction m with
  | zero => simp [binom]
  | succ m ih => simp [binom, length_add, ih]

theorem length_toBern (p : List ℚ) : (toBern p).length = p.length := by
  induction p with
  | nil => simp [toBern]
  | cons a p ih => simp [toBern, length_add, smul, length_binom, ih]

theorem hom_add (p q : List ℚ) (n : ℕ) (a b : ℝ) :
    hom (add p q) n a b = hom p n a b + hom q n a b := by
  induction p generalizing q n with
  | nil => simp [add, hom]
  | cons c p ih =>
    cases q with
    | nil => simp [add, hom]
    | cons d q => simp [add, hom, ih]; ring

theorem hom_smul (r : ℚ) (p : List ℚ) (n : ℕ) (a b : ℝ) :
    hom (smul r p) n a b = r * hom p n a b := by
  induction p generalizing n with
  | nil => simp [smul, hom]
  | cons c p ih =>
    simp only [smul, List.map_cons] at ih ⊢
    simp [hom, ih]; ring

theorem hom_binom (m n : ℕ) (hmn : m ≤ n) (a b : ℝ) :
    hom (binom m) n a b = (a + b) ^ m * b ^ (n - m) := by
  induction m generalizing n with
  | zero => simp [binom, hom]
  | succ m ih =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    simp only [binom, hom_add, hom]
    rw [ih (m + 1 + k) (by omega), ih (m + 1 + k - 1) (by omega)]
    have h1 : m + 1 + k - m = k + 1 := by omega
    have h2 : m + 1 + k - 1 - m = k := by omega
    have h3 : m + 1 + k - (m + 1) = k := by omega
    rw [h1, h2, h3]
    simp; ring

theorem hom_toBern (p : List ℚ) (n : ℕ) (hn : p.length ≤ n + 1) (a : ℝ) :
    hom (toBern p) n a (1 - a) = (1 - a) ^ (n + 1 - p.length) * eval p a := by
  induction p generalizing n with
  | nil => simp [toBern, hom]
  | cons c p ih =>
    simp only [List.length_cons] at hn
    simp only [toBern, hom_add, hom_smul, hom, hom_binom _ _ (by omega : p.length ≤ n)]
    cases n with
    | zero =>
      have hp : p = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hp
      simp [toBern, hom]
    | succ n =>
      simp only [Nat.add_sub_cancel]
      rw [ih n (by omega)]
      have h1 : n + 1 + 1 - (p.length + 1) = n + 1 - p.length := by omega
      simp only [List.length_cons, h1, eval_cons]
      simp; ring

theorem hom_pos (l : List ℚ) (hl : ∀ c ∈ l, 0 < c) (n : ℕ) (hn : l.length = n + 1)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) : 0 < hom l n a b := by
  induction l generalizing n with
  | nil => simp at hn
  | cons c cs ih =>
    have hc : (0 : ℝ) < c := by exact_mod_cast hl c (by simp)
    simp only [List.length_cons] at hn
    cases cs with
    | nil =>
      have : n = 0 := by simp at hn; omega
      subst this; simp [hom, hc]
    | cons d ds =>
      have hrec := ih (fun e he => hl e (List.mem_cons_of_mem _ he)) (n - 1)
        (by simp at hn ⊢; omega)
      rw [hom_cons]
      rcases ha.lt_or_eq with ha' | ha'
      · have := mul_pos ha' hrec
        have : 0 ≤ (c : ℝ) * b ^ n := by positivity
        linarith
      · subst ha'
        have hb' : 0 < b := by linarith
        simp only [zero_mul, add_zero]
        positivity

/-- Soundness of the Bernstein test. -/
theorem pos_of_posCheck {p : List ℚ} {lo hi : ℚ} (h : posCheck p lo hi = true) {x : ℝ}
    (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ hi) : 0 < eval p x := by
  simp only [posCheck, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    List.isEmpty_eq_false_iff, List.all_eq_true] at h
  obtain ⟨⟨hlh, hne⟩, hall⟩ := h
  set q := affine lo (hi - lo) p
  have hw : (0 : ℝ) < (hi : ℝ) - lo := by
    have : (lo : ℝ) < hi := by exact_mod_cast hlh
    linarith
  set s : ℝ := (x - lo) / ((hi : ℝ) - lo)
  have hs0 : 0 ≤ s := div_nonneg (by linarith) hw.le
  have hs1 : s ≤ 1 := (div_le_one hw).mpr (by linarith)
  have hq : eval q s = eval p x := by
    rw [eval_affine]
    congr 1
    simp only [s]; push_cast; field_simp; ring
  have hlen : (toBern q).length = q.length := length_toBern q
  have hqn : q ≠ [] := by
    intro hq0; apply hne; simp [hq0, toBern]
  obtain ⟨n, hn⟩ : ∃ n, q.length = n + 1 :=
    ⟨q.length - 1, by have := List.length_pos_of_ne_nil hqn; omega⟩
  have hhom := hom_toBern q n (by omega) s
  rw [hn, Nat.sub_self, pow_zero, one_mul, hq] at hhom
  rw [← hhom]
  exact hom_pos _ (fun c hc => by simpa using hall c hc) n (by rw [hlen, hn]) hs0
    (by linarith) (by linarith)

/-- Bernstein tests on consecutive subintervals `[a,b₁], [b₁,b₂], …`. -/
def posChain (p : List ℚ) (a : ℚ) : List ℚ → Bool
  | [] => false
  | b :: rest => posCheck p a b && (rest.isEmpty || posChain p b rest)

theorem pos_of_posChain {p : List ℚ} {a : ℚ} {bs : List ℚ} (h : posChain p a bs = true)
    {x : ℝ} (hlo : (a : ℝ) ≤ x) (hhi : x ≤ (bs.getLastD a : ℚ)) : 0 < eval p x := by
  induction bs generalizing a with
  | nil => simp [posChain] at h
  | cons b rest ih =>
    simp only [posChain, Bool.and_eq_true, Bool.or_eq_true, List.isEmpty_iff] at h
    obtain ⟨hab, hrest⟩ := h
    by_cases hxb : x ≤ b
    · exact pos_of_posCheck hab hlo hxb
    · rcases hrest with hr | hr
      · subst hr; simp at hhi; exact absurd hhi hxb
      · apply ih hr (le_of_lt (lt_of_not_ge hxb))
        cases rest with
        | nil => simp [posChain] at hr
        | cons c cs => rwa [List.getLastD_cons] at hhi

end BecknerOnofri.HighDim.CircleScalar.GammaPoly
