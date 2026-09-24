import Mathlib

/-!
# Leading digits of partition-type sequences

This file begins a formalization of Theorem 1.1 in the attached paper.  The two
published asymptotic estimates for the partition and plane-partition functions
will be supplied as explicit hypotheses.  Everything downstream of those
estimates is proved in Lean.
-/

namespace PartitionDigits

open Set

noncomputable section

/-- `x` lies in the interval `[a, a + δ)` modulo an integer translation. -/
def InIntervalModOne (x a δ : ℝ) : Prop :=
  ∃ k : ℤ, a + (k : ℝ) ≤ x ∧ x < a + δ + (k : ℝ)

/-- Base-`b` logarithm, written explicitly to keep the assumptions on `b` visible. -/
def logBase (b x : ℝ) : ℝ := Real.log x / Real.log b

/-- The logarithmic characterization of “`q n` begins with the digits `f` in base `b`”. -/
def BeginsWith (q : ℕ → ℕ) (b f n : ℕ) : Prop :=
  InIntervalModOne (logBase b (q n)) (logBase b f)
    (logBase b (f + 1) - logBase b f)

/--
The direct leading-digit condition: after shifting by an integral power of the
base, `q n` lies between `f` and `f + 1`.  The exponential form handles both
positive and negative integral shifts uniformly.
-/
def HasLeadingDigits (q : ℕ → ℕ) (b f n : ℕ) : Prop :=
  ∃ k : ℤ,
    (f : ℝ) * Real.exp ((k : ℝ) * Real.log b) ≤ (q n : ℝ) ∧
    (q n : ℝ) < (f + 1 : ℕ) * Real.exp ((k : ℝ) * Real.log b)

/-- The least index with the requested leading digits, or `0` if none exists. -/
noncomputable def firstOccurrence (q : ℕ → ℕ) (b f : ℕ) : ℕ := by
  classical
  exact if h : ∃ n, HasLeadingDigits q b f n then Nat.find h else 0

lemma firstOccurrence_le_of_exists {q : ℕ → ℕ} {b f : ℕ} {B : ℝ}
    (h : ∃ n : ℕ, (n : ℝ) ≤ B ∧ HasLeadingDigits q b f n) :
    (firstOccurrence q b f : ℝ) ≤ B := by
  classical
  obtain ⟨n, hnB, hn⟩ := h
  have hex : ∃ m, HasLeadingDigits q b f m := ⟨n, hn⟩
  have hmin : firstOccurrence q b f ≤ n := by
    rw [firstOccurrence, dite_eq_left hex]
    exact Nat.find_min' hex hn
  exact (Nat.cast_le.mpr hmin).trans hnB

/-- `f` is a nonzero string of exactly `t` base-`b` digits. -/
structure IsDigitString (b t f : ℕ) : Prop where
  base : 2 ≤ b
  length_pos : 1 ≤ t
  lower : b ^ (t - 1) ≤ f
  upper : f < b ^ t

lemma IsDigitString.f_pos {b t f : ℕ} (hf : IsDigitString b t f) : 0 < f := by
  have hb : 0 < b := lt_of_lt_of_le (by norm_num) hf.base
  exact (pow_pos hb _).trans_le hf.lower

lemma log_base_pos {b : ℕ} (hb : 2 ≤ b) : 0 < Real.log (b : ℝ) := by
  exact Real.log_pos (by exact_mod_cast hb)

lemma InIntervalModOne.mono_width {x a δ ε : ℝ}
    (h : InIntervalModOne x a δ) (hδε : δ ≤ ε) : InIntervalModOne x a ε := by
  obtain ⟨k, hk₁, hk₂⟩ := h
  exact ⟨k, hk₁, hk₂.trans_le (by linarith)⟩

lemma BeginsWith.toHasLeadingDigits {q : ℕ → ℕ} {b f n : ℕ}
    (hb : 2 ≤ b) (hf : 0 < f) (hq : 0 < q n) (h : BeginsWith q b f n) :
    HasLeadingDigits q b f n := by
  obtain ⟨k, hk₁, hk₂⟩ := h
  have hlogb : 0 < Real.log (b : ℝ) := log_base_pos hb
  have hfR : 0 < (f : ℝ) := by exact_mod_cast hf
  have hf1R : 0 < ((f + 1 : ℕ) : ℝ) := by positivity
  have hqR : 0 < ((q n : ℕ) : ℝ) := by exact_mod_cast hq
  have hlo_div :
      (Real.log (f : ℝ) + (k : ℝ) * Real.log b) / Real.log b ≤
        Real.log (q n : ℝ) / Real.log b := by
    calc
      (Real.log (f : ℝ) + (k : ℝ) * Real.log b) / Real.log b =
          logBase b f + (k : ℝ) := by
            simp only [logBase]
            field_simp
      _ ≤ logBase b (q n) := hk₁
      _ = Real.log (q n : ℝ) / Real.log b := rfl
  have hlo_log : Real.log (f : ℝ) + (k : ℝ) * Real.log b ≤ Real.log (q n : ℝ) :=
    (div_le_div_iff_of_pos_right hlogb).mp hlo_div
  have hup_div : Real.log (q n : ℝ) / Real.log b <
      (Real.log ((f + 1 : ℕ) : ℝ) + (k : ℝ) * Real.log b) / Real.log b := by
    calc
      Real.log (q n : ℝ) / Real.log b = logBase b (q n) := rfl
      _ < logBase b f + (logBase b (f + 1) - logBase b f) + (k : ℝ) := by
        simpa [add_assoc] using hk₂
      _ = (Real.log ((f + 1 : ℕ) : ℝ) + (k : ℝ) * Real.log b) /
          Real.log b := by
            simp only [logBase, Nat.cast_add, Nat.cast_one]
            field_simp
            ring
  have hup_log : Real.log (q n : ℝ) <
      Real.log ((f + 1 : ℕ) : ℝ) + (k : ℝ) * Real.log b :=
    (div_lt_div_iff_of_pos_right hlogb).mp hup_div
  refine ⟨k, ?_, ?_⟩
  · have := Real.exp_le_exp.mpr hlo_log
    rw [Real.exp_add, Real.exp_log hfR, Real.exp_log hqR] at this
    exact this
  · have := Real.exp_lt_exp.mpr hup_log
    rw [Real.exp_add, Real.exp_log hf1R, Real.exp_log hqR] at this
    exact this

/-- The target interval has width at least `b⁻ᵗ / log b`, as used in (4.1). -/
lemma target_width_lower {b t f : ℕ} (hf : IsDigitString b t f) :
    1 / ((b : ℝ) ^ t * Real.log b) ≤
      logBase b (f + 1) - logBase b f := by
  have hf_pos_nat := hf.f_pos
  have hF : 0 < (f : ℝ) := by exact_mod_cast hf_pos_nat
  have hlogb : 0 < Real.log (b : ℝ) := log_base_pos hf.base
  have hFone : (f : ℝ) + 1 ≤ (b : ℝ) ^ t := by
    exact_mod_cast hf.upper
  have hlog_identity :
      Real.log ((f : ℝ) + 1) - Real.log (f : ℝ) = Real.log (1 + 1 / (f : ℝ)) := by
    rw [← Real.log_div (by positivity) (ne_of_gt hF)]
    congr 1
    field_simp
  have hbasic := Real.le_log_one_add_of_nonneg (show 0 ≤ 1 / (f : ℝ) by positivity)
  have hone : 1 / ((f : ℝ) + 1) ≤ Real.log (1 + 1 / (f : ℝ)) := by
    calc
      1 / ((f : ℝ) + 1) ≤ 2 * (1 / (f : ℝ)) / (1 / (f : ℝ) + 2) := by
        field_simp
        nlinarith
      _ ≤ Real.log (1 + 1 / (f : ℝ)) := hbasic
  have hdenom :
      1 / ((b : ℝ) ^ t * Real.log b) ≤ 1 / (((f : ℝ) + 1) * Real.log b) := by
    apply one_div_le_one_div_of_le
    · positivity
    · exact mul_le_mul_of_nonneg_right hFone hlogb.le
  simp only [logBase]
  calc
    1 / ((b : ℝ) ^ t * Real.log b)
        ≤ 1 / (((f : ℝ) + 1) * Real.log b) := hdenom
    _ = (1 / ((f : ℝ) + 1)) / Real.log b := by field_simp
    _ ≤ (Real.log ((f : ℝ) + 1) - Real.log (f : ℝ)) / Real.log b := by
      exact div_le_div_of_nonneg_right (hlog_identity ▸ hone) hlogb.le
    _ = Real.log ((f : ℝ) + 1) / Real.log (b : ℝ) -
          Real.log (f : ℝ) / Real.log (b : ℝ) := by ring

/--
The elementary interval-hitting argument used in Proposition 3.1 of the paper.

The analytic estimates on `h` are exposed as hypotheses so that this lemma can
be reused for both exponents `1/2` and `2/3`.  The proof itself contains the
ceiling, intermediate-value, and rounding arguments from the paper.
-/
theorem exists_natural_hit
    (g : ℕ → ℝ) (h : ℝ → ℝ) (a δ X Y M : ℝ)
    (hX : 0 ≤ X)
    (hXY : X ≤ Y)
    (hY : Y ≤ 2 * X)
    (hcont : ContinuousOn h (Icc X Y))
    (hmono : MonotoneOn h (Icc X Y))
    (hrange : 1 + δ / 3 < h Y - h X)
    (hM : 0 < M)
    (hstep : M ≤ δ / 3)
    (hlip : ∀ u ∈ Icc X Y, ∀ v ∈ Icc X Y, u ≤ v → h v - h u ≤ M * (v - u))
    (herr : ∀ m : ℕ, X ≤ (m : ℝ) → (m : ℝ) ≤ Y → |g m - h m| < δ / 3) :
    ∃ m : ℕ, (m : ℝ) ≤ 2 * X ∧ InIntervalModOne (g m) a δ := by
  let k : ℤ := ⌈h X - (a + δ / 3)⌉
  let y₁ : ℝ := a + δ / 3 + (k : ℝ)
  let y₂ : ℝ := y₁ + δ / 3
  have hk_lower : h X ≤ y₁ := by
    have hc := Int.le_ceil (h X - (a + δ / 3))
    dsimp [k, y₁]
    linarith
  have hk_upper : y₁ < h X + 1 := by
    have hc := Int.ceil_lt_add_one (h X - (a + δ / 3))
    dsimp [k, y₁]
    linarith
  have hy₁y₂ : y₁ < y₂ := by
    dsimp [y₂]
    linarith
  have hy₂_upper : y₂ < h Y := by
    dsimp [y₂]
    linarith
  have hy₁_mem : y₁ ∈ Icc (h X) (h Y) :=
    ⟨hk_lower, le_trans (le_of_lt hy₁y₂) (le_of_lt hy₂_upper)⟩
  have hy₂_mem : y₂ ∈ Icc (h X) (h Y) :=
    ⟨le_trans hk_lower (le_of_lt hy₁y₂), le_of_lt hy₂_upper⟩
  obtain ⟨x₁, hx₁, hx₁eq⟩ := (intermediate_value_Icc hXY hcont) hy₁_mem
  obtain ⟨x₂, hx₂, hx₂eq⟩ := (intermediate_value_Icc hXY hcont) hy₂_mem
  have hx₁x₂ : x₁ ≤ x₂ := by
    by_contra hnot
    have hlt : x₂ < x₁ := lt_of_not_ge hnot
    have := hmono hx₂ hx₁ (le_of_lt hlt)
    rw [hx₁eq, hx₂eq] at this
    linarith
  have hgap_upper : y₂ - y₁ ≤ M * (x₂ - x₁) := by
    simpa [hx₁eq, hx₂eq] using hlip x₁ hx₁ x₂ hx₂ hx₁x₂
  have hgap : 1 ≤ x₂ - x₁ := by
    dsimp [y₂] at hgap_upper
    nlinarith
  let m : ℕ := ⌈x₁⌉₊
  have hx₁_nonneg : 0 ≤ x₁ := hX.trans hx₁.1
  have hx₁m : x₁ ≤ (m : ℝ) := by
    dsimp [m]
    exact Nat.le_ceil x₁
  have hm_lt : (m : ℝ) < x₁ + 1 := by
    dsimp [m]
    exact Nat.ceil_lt_add_one hx₁_nonneg
  have hm_x₂ : (m : ℝ) ≤ x₂ := by
    have : x₁ + 1 ≤ x₂ := by linarith
    exact (le_of_lt hm_lt).trans this
  have hm_mem : (m : ℝ) ∈ Icc X Y :=
    ⟨hx₁.1.trans hx₁m, hm_x₂.trans hx₂.2⟩
  have hh_lower : y₁ ≤ h m := by
    rw [← hx₁eq]
    exact hmono hx₁ hm_mem hx₁m
  have hh_upper : h m ≤ y₂ := by
    rw [← hx₂eq]
    exact hmono hm_mem hx₂ hm_x₂
  have he := herr m hm_mem.1 hm_mem.2
  have he' := (abs_lt.mp he)
  refine ⟨m, ?_, ?_⟩
  · exact hm_mem.2.trans (hY.trans_eq (by ring))
  · refine ⟨k, ?_, ?_⟩
    · dsimp [y₁] at hh_lower
      linarith [he'.1]
    · dsimp [y₂, y₁] at hh_upper
      linarith [he'.2]

/--
A calculus-friendly form of `exists_natural_hit`.  A positive lower derivative
bound makes `h` cross a full unit interval, while the upper derivative bound
makes the preimage of the target interval long enough to contain an integer.
-/
theorem exists_natural_hit_of_deriv_bounds
    (g : ℕ → ℝ) (h d : ℝ → ℝ) (a δ X L M : ℝ)
    (hX : 0 < X)
    (hL : 0 < L)
    (hM : 0 < M)
    (hderiv : ∀ x ∈ Icc X (2 * X), HasDerivAt h (d x) x)
    (hderiv_lower : ∀ x ∈ Icc X (2 * X), L ≤ d x)
    (hderiv_upper : ∀ x ∈ Icc X (2 * X), d x ≤ M)
    (hrange : 1 + δ / 3 < L * X)
    (hstep : M ≤ δ / 3)
    (herr : ∀ m : ℕ, X ≤ (m : ℝ) → (m : ℝ) ≤ 2 * X → |g m - h m| < δ / 3) :
    ∃ m : ℕ, (m : ℝ) ≤ 2 * X ∧ InIntervalModOne (g m) a δ := by
  have hX2 : X ≤ 2 * X := by linarith
  have hcont : ContinuousOn h (Icc X (2 * X)) := fun x hx =>
    (hderiv x hx).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ h (interior (Icc X (2 * X))) := fun x hx =>
    (hderiv x (interior_subset hx)).differentiableAt.differentiableWithinAt
  have hmono : MonotoneOn h (Icc X (2 * X)) :=
    monotoneOn_of_deriv_nonneg (convex_Icc X (2 * X)) hcont hdiff fun x hx => by
      rw [(hderiv x (interior_subset hx)).deriv]
      exact (le_of_lt hL).trans (hderiv_lower x (interior_subset hx))
  have hgrowth : L * ((2 * X) - X) ≤ h (2 * X) - h X := by
    apply (convex_Icc X (2 * X)).mul_sub_le_image_sub_of_le_deriv hcont hdiff
    · intro x hx
      rw [(hderiv x (interior_subset hx)).deriv]
      exact hderiv_lower x (interior_subset hx)
    · exact left_mem_Icc.mpr hX2
    · exact right_mem_Icc.mpr hX2
    · exact hX2
  have hrange' : 1 + δ / 3 < h (2 * X) - h X := by
    have : L * X ≤ h (2 * X) - h X := by convert hgrowth using 1 <;> ring_nf
    exact hrange.trans_le this
  have hlip : ∀ u ∈ Icc X (2 * X), ∀ v ∈ Icc X (2 * X), u ≤ v →
      h v - h u ≤ M * (v - u) := by
    intro u hu v hv huv
    apply (convex_Icc X (2 * X)).image_sub_le_mul_sub_of_deriv_le hcont hdiff
    · intro x hx
      rw [(hderiv x (interior_subset hx)).deriv]
      exact hderiv_upper x (interior_subset hx)
    · exact hu
    · exact hv
    · exact huv
  exact exists_natural_hit g h a δ X (2 * X) M hX.le hX2 le_rfl hcont hmono hrange'
    hM hstep hlip herr

section Partition

/-- The main term in Lemma 2.2, with its irrelevant additive constant exposed. -/
def partitionMainTerm (b C x : ℝ) : ℝ :=
  (Real.pi * Real.sqrt 24 / (6 * Real.log b)) * Real.sqrt x -
    Real.log x / Real.log b + C

/-- Derivative of `partitionMainTerm` away from zero. -/
def partitionMainDeriv (b x : ℝ) : ℝ :=
  (Real.pi * Real.sqrt 24 / (6 * Real.log b)) * (1 / (2 * Real.sqrt x)) -
    (1 / x) / Real.log b

lemma partitionMainTerm_hasDerivAt {b C x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (partitionMainTerm b C) (partitionMainDeriv b x) x := by
  have hs := (Real.hasDerivAt_sqrt hx).const_mul
    (Real.pi * Real.sqrt 24 / (6 * Real.log b))
  have hl := (Real.hasDerivAt_log hx).div_const (Real.log b)
  change HasDerivAt
    (fun y => (Real.pi * Real.sqrt 24 / (6 * Real.log b)) * Real.sqrt y -
      Real.log y / Real.log b + C)
    ((Real.pi * Real.sqrt 24 / (6 * Real.log b)) * (1 / (2 * Real.sqrt x)) -
      (1 / x) / Real.log b) x
  convert HasDerivAt.add_const C (hs.sub hl) using 1 <;> ring_nf

/-- The estimate for `p(n)` quoted as Lemma 2.2 in the paper. -/
def PartitionEstimate (p : ℕ → ℕ) (b : ℕ) : Prop :=
  (∀ n : ℕ, 0 < p n) ∧ ∃ C : ℝ, ∀ n : ℕ, 4 ≤ n →
    |logBase b (p n) - partitionMainTerm b C n| ≤
      4 / (Real.sqrt n * Real.log b)

/-- The partition-function half of Theorem 1.1. -/
theorem partition_leading_digits_bound
    (p : ℕ → ℕ) {b t f : ℕ} (hf : IsDigitString b t f)
    (hp : PartitionEstimate p b) :
    ∃ n : ℕ, (n : ℝ) ≤ 288 * (b : ℝ) ^ (2 * t) + 2 ∧
      HasLeadingDigits p b f n := by
  obtain ⟨hp_pos, C, hp⟩ := hp
  let R : ℝ := (b : ℝ) ^ t
  let logb : ℝ := Real.log (b : ℝ)
  let δ : ℝ := 1 / (R * logb)
  let X : ℝ := 144 * R ^ 2 + 1
  let M : ℝ := 1 / (6 * R * logb)
  let L : ℝ := 1 / (24 * R * logb)
  let h : ℝ → ℝ := partitionMainTerm b C
  let d : ℝ → ℝ := partitionMainDeriv b
  have hlogb : 0 < logb := by simpa [logb] using log_base_pos hf.base
  have hbR : (b : ℝ) ≤ R := by
    dsimp [R]
    simpa only [pow_one] using
      (pow_le_pow_right₀
        (show (1 : ℝ) ≤ b by exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hf.base))
        hf.length_pos)
  have hR : 2 ≤ R := (show (2 : ℝ) ≤ b by exact_mod_cast hf.base).trans hbR
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hX : 0 < X := by dsimp [X]; positivity
  have hM : 0 < M := by dsimp [M]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hsqrt24_lower : (4 : ℝ) < Real.sqrt 24 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hsqrt24_upper : Real.sqrt 24 < (5 : ℝ) := by
    rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  have hc_lower : 2 / logb < Real.pi * Real.sqrt 24 / (6 * logb) := by
    rw [show Real.pi * Real.sqrt 24 / (6 * logb) =
      (Real.pi * Real.sqrt 24 / 6) / logb by field_simp]
    apply (div_lt_div_iff₀ hlogb hlogb).2
    have hpimul : (12 : ℝ) < Real.pi * Real.sqrt 24 := by
      calc
        (12 : ℝ) = 3 * 4 := by norm_num
        _ < Real.pi * Real.sqrt 24 :=
          mul_lt_mul Real.pi_gt_three (le_of_lt hsqrt24_lower) (by norm_num) Real.pi_pos.le
    nlinarith
  have hc_upper : Real.pi * Real.sqrt 24 / (6 * logb) < 4 / logb := by
    rw [show Real.pi * Real.sqrt 24 / (6 * logb) =
      (Real.pi * Real.sqrt 24 / 6) / logb by field_simp]
    apply (div_lt_div_iff₀ hlogb hlogb).2
    have hpimul : Real.pi * Real.sqrt 24 < (20 : ℝ) := by
      calc
        Real.pi * Real.sqrt 24 < 4 * 5 :=
          mul_lt_mul Real.pi_lt_four (le_of_lt hsqrt24_upper)
            (Real.sqrt_pos.2 (by norm_num)) (by norm_num)
        _ = 20 := by norm_num
    nlinarith
  have hsqrtX_lower : 12 * R < Real.sqrt X := by
    rw [Real.lt_sqrt (by positivity)]
    dsimp [X]
    nlinarith
  have hderiv : ∀ x ∈ Icc X (2 * X), HasDerivAt h (d x) x := by
    intro x hx
    dsimp [h, d]
    apply partitionMainTerm_hasDerivAt
    exact ne_of_gt (hX.trans_le hx.1)
  have hderiv_upper : ∀ x ∈ Icc X (2 * X), d x ≤ M := by
    intro x hx
    have hxpos : 0 < x := hX.trans_le hx.1
    have hsxpos : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
    have hsxlower : 12 * R < Real.sqrt x :=
      hsqrtX_lower.trans_le (Real.sqrt_le_sqrt hx.1)
    have hlead :
        (Real.pi * Real.sqrt 24 / (6 * logb)) / (2 * Real.sqrt x) < M := by
      calc
        (Real.pi * Real.sqrt 24 / (6 * logb)) / (2 * Real.sqrt x)
            < (4 / logb) / (2 * (12 * R)) := by
              apply div_lt_div₀ hc_upper
              · nlinarith
              · positivity
              · positivity
        _ = M := by dsimp [M]; field_simp; ring
    dsimp [d, partitionMainDeriv]
    rw [show Real.log (b : ℝ) = logb by rfl]
    have hneg : 0 ≤ (1 / x) / logb := by positivity
    rw [mul_one_div]
    linarith
  have hderiv_lower : ∀ x ∈ Icc X (2 * X), L ≤ d x := by
    intro x hx
    have hxpos : 0 < x := hX.trans_le hx.1
    have hsxpos : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
    have hx_upper_sq : x ≤ (18 * R) ^ 2 := by
      calc
        x ≤ 2 * X := hx.2
        _ ≤ (18 * R) ^ 2 := by
          dsimp [X]
          nlinarith [sq_nonneg R]
    have hsxupper : Real.sqrt x ≤ 18 * R := by
      rw [Real.sqrt_le_iff]
      exact ⟨by positivity, hx_upper_sq⟩
    have hlead : 1 / (18 * R * logb) <
        (Real.pi * Real.sqrt 24 / (6 * logb)) / (2 * Real.sqrt x) := by
      calc
        1 / (18 * R * logb) = (2 / logb) / (2 * (18 * R)) := by
          field_simp
        _ < (Real.pi * Real.sqrt 24 / (6 * logb)) / (2 * Real.sqrt x) := by
          apply div_lt_div₀ hc_lower
          · nlinarith
          · positivity
          · positivity
    have hneg : (1 / x) / logb < 1 / (144 * R * logb) := by
      have hxlarge : 144 * R < x := by
        have : 144 * R < X := by
          dsimp [X]
          nlinarith [sq_nonneg (R - 1)]
        exact this.trans_le hx.1
      calc
        (1 / x) / logb = 1 / (x * logb) := by field_simp
        _ < 1 / ((144 * R) * logb) := by
          apply one_div_lt_one_div_of_lt
          · positivity
          · exact mul_lt_mul_of_pos_right hxlarge hlogb
        _ = 1 / (144 * R * logb) := by ring
    dsimp [d, partitionMainDeriv, L]
    rw [show Real.log (b : ℝ) = logb by rfl, mul_one_div]
    have hdenpos : 0 < R * logb := mul_pos hRpos hlogb
    have hcalc :
        1 / (24 * R * logb) < 1 / (18 * R * logb) - 1 / (144 * R * logb) := by
      field_simp
      nlinarith
    linarith
  have hrange : 1 + δ / 3 < L * X := by
    have hlog_lt_R : logb < R := by
      have hlog_lt_b : logb < (b : ℝ) := by
        dsimp [logb]
        have hbpos : 0 < b := lt_of_lt_of_le (by norm_num) hf.base
        have hbne : b ≠ 1 := by
          have hb2 := hf.base
          omega
        have := Real.log_lt_sub_one_of_pos (show 0 < (b : ℝ) by exact_mod_cast hbpos)
          (show (b : ℝ) ≠ 1 by exact_mod_cast hbne)
        linarith
      exact hlog_lt_b.trans_le hbR
    have hδsmall : δ < 1 := by
      dsimp [δ]
      have : 1 < R * logb := by
        have hlog2le : Real.log 2 ≤ logb := by
          dsimp [logb]
          apply Real.strictMonoOn_log.monotoneOn
          · norm_num
          · show (0 : ℝ) < b
            exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hf.base)
          · exact_mod_cast hf.base
        have hmul : 2 * Real.log 2 ≤ R * logb :=
          mul_le_mul hR hlog2le (Real.log_nonneg (by norm_num)) hRpos.le
        nlinarith [Real.log_two_gt_d9]
      simpa using (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) this)
    have hLX : 6 * R / logb < L * X := by
      dsimp [L, X]
      field_simp
      nlinarith
    have : 1 < R / logb := (lt_div_iff₀ hlogb).2 (by simpa using hlog_lt_R)
    have heq : 6 * R / logb = 6 * (R / logb) := by ring
    nlinarith
  have hstep : M ≤ δ / 3 := by
    dsimp [M, δ]
    have : 0 < R * logb := mul_pos hRpos hlogb
    field_simp
    norm_num
  have herr : ∀ m : ℕ, X ≤ (m : ℝ) → (m : ℝ) ≤ 2 * X →
      |logBase b (p m) - h m| < δ / 3 := by
    intro m hmX hm2X
    have hm4 : 4 ≤ m := by
      have : (4 : ℝ) < X := by dsimp [X]; nlinarith
      exact_mod_cast (this.trans_le hmX).le
    have hsqrtm : 12 * R < Real.sqrt m :=
      hsqrtX_lower.trans_le (Real.sqrt_le_sqrt hmX)
    have herror_lt : 4 / (Real.sqrt m * logb) < δ / 3 := by
      calc
        4 / (Real.sqrt m * logb) < 4 / ((12 * R) * logb) := by
          apply div_lt_div_of_pos_left (by norm_num)
          · positivity
          · exact mul_lt_mul_of_pos_right hsqrtm hlogb
        _ = δ / 3 := by dsimp [δ]; field_simp; ring
    exact (hp m hm4).trans_lt (by simpa [h, logb] using herror_lt)
  obtain ⟨n, hn, hhit⟩ := exists_natural_hit_of_deriv_bounds
    (fun n => logBase b (p n)) h d (logBase b f) δ X L M hX hL hM
    hderiv hderiv_lower hderiv_upper hrange hstep herr
  refine ⟨n, ?_, ?_⟩
  · calc
      (n : ℝ) ≤ 2 * X := hn
      _ = 288 * (b : ℝ) ^ (2 * t) + 2 := by
        dsimp [X, R]
        rw [show 2 * t = t * 2 by omega, pow_mul]
        ring
  · exact BeginsWith.toHasLeadingDigits hf.base hf.f_pos (hp_pos n)
      (hhit.mono_width (by simpa [δ, R] using target_width_lower hf))

end Partition

section PlanePartition

lemma rpow_one_third_mul_cube (a R : ℝ) (ha : 0 ≤ a) (hR : 0 ≤ R) :
    (a * R ^ 3) ^ ((1 : ℝ) / 3) = a ^ ((1 : ℝ) / 3) * R := by
  rw [Real.mul_rpow ha (pow_nonneg hR 3)]
  congr 1
  rw [← Real.rpow_natCast R 3, ← Real.rpow_mul hR]
  norm_num

lemma six_hundred_rpow_three_halves_lt :
    (600 : ℝ) ^ ((3 : ℝ) / 2) < 14700 := by
  rw [Real.rpow_div_two_eq_sqrt 3 (by norm_num)]
  rw [show (3 : ℝ) = 2 + 1 by norm_num,
    Real.rpow_add (Real.sqrt_pos.2 (by norm_num)), Real.rpow_two, Real.rpow_one,
    Real.sq_sqrt (by norm_num)]
  have hs : Real.sqrt 600 < (49 : ℝ) / 2 := by
    rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  nlinarith

/-- The main term in Lemma 2.3, again with the additive constant exposed. -/
def planeMainTerm (b A C x : ℝ) : ℝ :=
  (3 * (A / 4) ^ ((1 : ℝ) / 3) / Real.log b) * x ^ ((2 : ℝ) / 3) -
    (25 / (36 * Real.log b)) * Real.log x + C

def planeMainDeriv (b A x : ℝ) : ℝ :=
  (2 * (A / 4) ^ ((1 : ℝ) / 3) / Real.log b) * x ^ (-(1 : ℝ) / 3) -
    25 / (36 * Real.log b * x)

lemma planeMainTerm_hasDerivAt {b A C x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (planeMainTerm b A C) (planeMainDeriv b A x) x := by
  have hp := (Real.hasDerivAt_rpow_const (p := (2 : ℝ) / 3) (Or.inl hx)).const_mul
    (3 * (A / 4) ^ ((1 : ℝ) / 3) / Real.log b)
  have hl := (Real.hasDerivAt_log hx).const_mul (25 / (36 * Real.log b))
  change HasDerivAt
    (fun y => (3 * (A / 4) ^ ((1 : ℝ) / 3) / Real.log b) * y ^ ((2 : ℝ) / 3) -
      (25 / (36 * Real.log b)) * Real.log y + C)
    ((2 * (A / 4) ^ ((1 : ℝ) / 3) / Real.log b) * x ^ (-(1 : ℝ) / 3) -
      25 / (36 * Real.log b * x)) x
  convert HasDerivAt.add_const C (hp.sub hl) using 1 <;>
    field_simp <;> ring_nf

/-- The estimate for `PL(n)` quoted as Lemma 2.3 in the paper. -/
def PlanePartitionEstimate (PL : ℕ → ℕ) (b : ℕ) (A : ℝ) : Prop :=
  (∀ n : ℕ, 0 < PL n) ∧ ∃ C : ℝ, ∀ n : ℕ, 2829 ≤ n →
    |logBase b (PL n) - planeMainTerm b A C n| ≤
      200 / ((n : ℝ) ^ ((2 : ℝ) / 3) * Real.log b)

/--
The two numerical facts about `A = ζ(3)` actually needed by the rounded
constants in the paper.  Keeping them explicit avoids treating the decimal
`A ≈ 1.202` as an exact equality.
-/
structure PlaneConstantBounds (A : ℝ) : Prop where
  lower : (1 : ℝ) / 2 ≤ (A / 4) ^ ((1 : ℝ) / 3)
  upper : 6 * (A / 4) ^ ((1 : ℝ) / 3) ≤ 65 ^ ((1 : ℝ) / 3)

/-- A convenient rigorous replacement for the decimal statement `A ≈ 1.202`. -/
lemma planeConstantBounds_of_interval {A : ℝ} (hA_lower : 1 ≤ A) (hA_upper : 54 * A ≤ 65) :
    PlaneConstantBounds A := by
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA_lower
  constructor
  · have hbase : (1 : ℝ) / 8 ≤ A / 4 := by linarith
    have hh := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1 / 8) hbase
      (by norm_num : (0 : ℝ) ≤ 1 / 3)
    have heq : ((1 : ℝ) / 8) ^ ((1 : ℝ) / 3) = 1 / 2 := by
      rw [show (1 : ℝ) / 8 = ((1 : ℝ) / 2) ^ 3 by norm_num]
      rw [← Real.rpow_natCast ((1 : ℝ) / 2) 3,
        ← Real.rpow_mul (by positivity)]
      norm_num
    rw [heq] at hh
    exact hh
  · have hsix : (216 : ℝ) ^ ((1 : ℝ) / 3) = 6 := by
      rw [show (216 : ℝ) = (6 : ℝ) ^ 3 by norm_num]
      rw [← Real.rpow_natCast (6 : ℝ) 3, ← Real.rpow_mul (by norm_num)]
      norm_num
    have heq : 6 * (A / 4) ^ ((1 : ℝ) / 3) =
        (54 * A) ^ ((1 : ℝ) / 3) := by
      calc
        6 * (A / 4) ^ ((1 : ℝ) / 3) =
            216 ^ ((1 : ℝ) / 3) * (A / 4) ^ ((1 : ℝ) / 3) := by rw [hsix]
        _ = (216 * (A / 4)) ^ ((1 : ℝ) / 3) := by
          rw [Real.mul_rpow (by norm_num) (by positivity)]
        _ = (54 * A) ^ ((1 : ℝ) / 3) := by
          congr 1
          ring
    rw [heq]
    exact Real.rpow_le_rpow (by positivity) hA_upper (by norm_num)

/-- The plane-partition half of Theorem 1.1. -/
theorem plane_partition_leading_digits_bound
    (PL : ℕ → ℕ) {b t f : ℕ} (hf : IsDigitString b t f)
    (A : ℝ) (hA : PlaneConstantBounds A)
    (hPL : PlanePartitionEstimate PL b A) :
    ∃ n : ℕ,
      (n : ℝ) ≤ 130 * (b : ℝ) ^ (3 * t) +
        29400 * (b : ℝ) ^ ((3 * (t : ℝ)) / 2) ∧
      HasLeadingDigits PL b f n := by
  obtain ⟨hPL_pos, C, hPL⟩ := hPL
  let R : ℝ := (b : ℝ) ^ t
  let R32 : ℝ := R ^ ((3 : ℝ) / 2)
  let S : ℝ := (A / 4) ^ ((1 : ℝ) / 3)
  let logb : ℝ := Real.log (b : ℝ)
  let δ : ℝ := 1 / (R * logb)
  let X : ℝ := 65 * R ^ 3 + 14700 * R32
  let M : ℝ := δ / 3
  let L : ℝ := 1 / (50 * R * logb)
  let h : ℝ → ℝ := planeMainTerm b A C
  let d : ℝ → ℝ := planeMainDeriv b A
  have hlogb : 0 < logb := by simpa [logb] using log_base_pos hf.base
  have hbR : (b : ℝ) ≤ R := by
    dsimp [R]
    simpa only [pow_one] using
      (pow_le_pow_right₀
        (show (1 : ℝ) ≤ b by exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hf.base))
        hf.length_pos)
  have hR : 2 ≤ R := (show (2 : ℝ) ≤ b by exact_mod_cast hf.base).trans hbR
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hRone : 1 ≤ R := le_trans (by norm_num) hR
  have hR32pos : 0 < R32 := by dsimp [R32]; positivity
  have hR32_nonneg : 0 ≤ R32 := hR32pos.le
  have hR32_le_cube : R32 ≤ R ^ 3 := by
    dsimp [R32]
    have hh := Real.rpow_le_rpow_of_exponent_le hRone
      (show (3 : ℝ) / 2 ≤ (3 : ℝ) by norm_num)
    rw [show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast] at hh
    exact hh
  have hX : 0 < X := by dsimp [X]; positivity
  have hM : 0 < M := by dsimp [M]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hderiv : ∀ x ∈ Icc X (2 * X), HasDerivAt h (d x) x := by
    intro x hx
    dsimp [h, d]
    apply planeMainTerm_hasDerivAt
    exact ne_of_gt (hX.trans_le hx.1)
  have hderiv_upper : ∀ x ∈ Icc X (2 * X), d x ≤ M := by
    intro x hx
    have hxpos : 0 < x := hX.trans_le hx.1
    have hbase : 65 * R ^ 3 ≤ x := by
      calc
        65 * R ^ 3 ≤ X := by dsimp [X]; nlinarith
        _ ≤ x := hx.1
    have hroot : 65 ^ ((1 : ℝ) / 3) * R ≤ x ^ ((1 : ℝ) / 3) := by
      have hh := Real.rpow_le_rpow (by positivity : 0 ≤ 65 * R ^ 3) hbase
        (by norm_num : (0 : ℝ) ≤ 1 / 3)
      rw [rpow_one_third_mul_cube 65 R (by norm_num) hRpos.le] at hh
      exact hh
    have h6 : 6 * S * R ≤ x ^ ((1 : ℝ) / 3) := by
      exact (mul_le_mul_of_nonneg_right (by simpa [S] using hA.upper) hRpos.le).trans hroot
    have hxrootpos : 0 < x ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hxpos _
    have hlead :
        (2 * S / logb) * x ^ (-(1 : ℝ) / 3) ≤ M := by
      rw [show -(1 : ℝ) / 3 = -((1 : ℝ) / 3) by ring,
        Real.rpow_neg hxpos.le]
      rw [show (2 * S / logb) * (x ^ ((1 : ℝ) / 3))⁻¹ =
        (2 * S) / (logb * x ^ ((1 : ℝ) / 3)) by field_simp]
      apply (div_le_iff₀ (mul_pos hlogb hxrootpos)).2
      dsimp [M, δ]
      field_simp
      nlinarith
    dsimp [d, planeMainDeriv]
    rw [show Real.log (b : ℝ) = logb by rfl, show (A / 4) ^ ((1 : ℝ) / 3) = S by rfl]
    have hneg : 0 ≤ 25 / (36 * logb * x) := by positivity
    linarith
  have hderiv_lower : ∀ x ∈ Icc X (2 * X), L ≤ d x := by
    intro x hx
    have hxpos : 0 < x := hX.trans_le hx.1
    have htwoX : 2 * X ≤ (31 * R) ^ 3 := by
      have hsum : 2 * X ≤ 29530 * R ^ 3 := by
        dsimp [X]
        nlinarith
      calc
        2 * X ≤ 29530 * R ^ 3 := hsum
        _ ≤ (31 * R) ^ 3 := by
          have : (0 : ℝ) ≤ R ^ 3 := by positivity
          nlinarith
    have hroot_upper : x ^ ((1 : ℝ) / 3) ≤ 31 * R := by
      have hh := Real.rpow_le_rpow hxpos.le (hx.2.trans htwoX)
        (by norm_num : (0 : ℝ) ≤ 1 / 3)
      have heq : ((31 * R) ^ 3) ^ ((1 : ℝ) / 3) = 31 * R := by
        rw [← Real.rpow_natCast (31 * R) 3, ← Real.rpow_mul (by positivity)]
        norm_num
      rw [heq] at hh
      exact hh
    have hxrootpos : 0 < x ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hxpos _
    have hinv : 1 / (31 * R) ≤ (x ^ ((1 : ℝ) / 3))⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hxrootpos hroot_upper
    have hSone : 1 ≤ 2 * S := by
      dsimp [S]
      nlinarith [hA.lower]
    have hlead : 1 / (31 * R * logb) ≤
        (2 * S / logb) * x ^ (-(1 : ℝ) / 3) := by
      rw [show -(1 : ℝ) / 3 = -((1 : ℝ) / 3) by ring,
        Real.rpow_neg hxpos.le]
      calc
        1 / (31 * R * logb) = (1 / logb) * (1 / (31 * R)) := by field_simp
        _ ≤ (1 / logb) * (x ^ ((1 : ℝ) / 3))⁻¹ := by
          exact mul_le_mul_of_nonneg_left hinv (by positivity)
        _ ≤ (2 * S / logb) * (x ^ ((1 : ℝ) / 3))⁻¹ := by
          apply mul_le_mul_of_nonneg_right
          · exact div_le_div_of_nonneg_right hSone hlogb.le
          · positivity
    have hxlarge : 2500 * R < 36 * x := by
      have hcube : 4 * R ≤ R ^ 3 := by
        have hR2 : 4 ≤ R ^ 2 := by nlinarith
        calc
          4 * R ≤ R ^ 2 * R := mul_le_mul_of_nonneg_right hR2 hRpos.le
          _ = R ^ 3 := by ring
      have : 65 * R ^ 3 ≤ x := by
        calc
          65 * R ^ 3 ≤ X := by dsimp [X]; nlinarith
          _ ≤ x := hx.1
      nlinarith
    have hneg : 25 / (36 * logb * x) < 1 / (100 * R * logb) := by
      have hden1 : 0 < 36 * logb * x := by positivity
      have hden2 : 0 < 100 * R * logb := by positivity
      apply (div_lt_div_iff₀ hden1 hden2).2
      nlinarith
    have hcalc : 1 / (50 * R * logb) <
        1 / (31 * R * logb) - 1 / (100 * R * logb) := by
      field_simp
      nlinarith
    dsimp [d, planeMainDeriv, L]
    rw [show Real.log (b : ℝ) = logb by rfl, show (A / 4) ^ ((1 : ℝ) / 3) = S by rfl]
    linarith
  have hrange : 1 + δ / 3 < L * X := by
    have hlog_lt_R : logb < R := by
      have hbpos : 0 < b := lt_of_lt_of_le (by norm_num) hf.base
      have hbne : b ≠ 1 := by
        have hb2 := hf.base
        omega
      have hlog_lt_b : logb < (b : ℝ) := by
        dsimp [logb]
        have := Real.log_lt_sub_one_of_pos (show 0 < (b : ℝ) by exact_mod_cast hbpos)
          (show (b : ℝ) ≠ 1 by exact_mod_cast hbne)
        linarith
      exact hlog_lt_b.trans_le hbR
    have hδsmall : δ < 1 := by
      dsimp [δ]
      have hlog2le : Real.log 2 ≤ logb := by
        dsimp [logb]
        apply Real.strictMonoOn_log.monotoneOn
        · norm_num
        · show (0 : ℝ) < b
          exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hf.base)
        · exact_mod_cast hf.base
      have hmul : 2 * Real.log 2 ≤ R * logb :=
        mul_le_mul hR hlog2le (Real.log_nonneg (by norm_num)) hRpos.le
      have hone : 1 < R * logb := by nlinarith [Real.log_two_gt_d9]
      simpa using (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hone)
    have hLX : 13 * R ^ 2 / (10 * logb) < L * X := by
      dsimp [L, X]
      field_simp
      nlinarith
    have hratio : 1 < R / logb :=
      (lt_div_iff₀ hlogb).2 (by simpa using hlog_lt_R)
    have hlarge : 2 < 13 * R ^ 2 / (10 * logb) := by
      have heq : 13 * R ^ 2 / (10 * logb) = (13 / 10) * R * (R / logb) := by ring
      rw [heq]
      nlinarith
    nlinarith
  have hstep : M ≤ δ / 3 := by rfl
  have herr : ∀ m : ℕ, X ≤ (m : ℝ) → (m : ℝ) ≤ 2 * X →
      |logBase b (PL m) - h m| < δ / 3 := by
    intro m hmX hm2X
    have h600 : (600 * R) ^ ((3 : ℝ) / 2) < X := by
      have hfactor :
          (600 * R) ^ ((3 : ℝ) / 2) = 600 ^ ((3 : ℝ) / 2) * R32 := by
        dsimp [R32]
        exact Real.mul_rpow (by norm_num) hRpos.le
      rw [hfactor]
      dsimp [X]
      have := mul_lt_mul_of_pos_right six_hundred_rpow_three_halves_lt hR32pos
      nlinarith
    have hpow : 600 * R < (m : ℝ) ^ ((2 : ℝ) / 3) := by
      have hh : (600 * R) ^ ((3 : ℝ) / 2) < (m : ℝ) := h600.trans_le hmX
      have hr := Real.rpow_lt_rpow (by positivity : 0 ≤ (600 * R) ^ ((3 : ℝ) / 2)) hh
        (by norm_num : (0 : ℝ) < 2 / 3)
      rw [← Real.rpow_mul (by positivity : 0 ≤ 600 * R)] at hr
      norm_num at hr
      exact hr
    have hm2829 : 2829 ≤ m := by
      have hR32one : 1 ≤ R32 := by
        dsimp [R32]
        exact Real.one_le_rpow hRone (by norm_num)
      have : (2829 : ℝ) < X := by dsimp [X]; nlinarith [sq_nonneg R]
      exact_mod_cast (this.trans_le hmX).le
    have herror_lt : 200 / ((m : ℝ) ^ ((2 : ℝ) / 3) * logb) < δ / 3 := by
      calc
        200 / ((m : ℝ) ^ ((2 : ℝ) / 3) * logb) < 200 / ((600 * R) * logb) := by
          apply div_lt_div_of_pos_left (by norm_num)
          · positivity
          · exact mul_lt_mul_of_pos_right hpow hlogb
        _ = δ / 3 := by dsimp [δ]; field_simp; ring
    exact (hPL m hm2829).trans_lt (by simpa [h, logb] using herror_lt)
  obtain ⟨n, hn, hhit⟩ := exists_natural_hit_of_deriv_bounds
    (fun n => logBase b (PL n)) h d (logBase b f) δ X L M hX hL hM
    hderiv hderiv_lower hderiv_upper hrange hstep herr
  refine ⟨n, ?_, ?_⟩
  · calc
      (n : ℝ) ≤ 2 * X := hn
      _ = 130 * (b : ℝ) ^ (3 * t) + 29400 * (b : ℝ) ^ ((3 * (t : ℝ)) / 2) := by
        dsimp [X, R32, R]
        rw [show 3 * t = t * 3 by omega, pow_mul]
        rw [← Real.rpow_natCast (b : ℝ) t, ← Real.rpow_mul (by positivity)]
        ring
  · exact BeginsWith.toHasLeadingDigits hf.base hf.f_pos (hPL_pos n)
      (hhit.mono_width (by simpa [δ, R] using target_width_lower hf))

/--
Theorem 1.1 in its existence form.  An upper bound on the first occurrence is
equivalent to exhibiting an occurrence below that bound.
-/
theorem theorem_1_1
    (p PL : ℕ → ℕ) {b t f : ℕ} (hf : IsDigitString b t f)
    (A : ℝ) (hA_lower : 1 ≤ A) (hA_upper : 54 * A ≤ 65)
    (hp : PartitionEstimate p b) (hPL : PlanePartitionEstimate PL b A) :
    (∃ n : ℕ, (n : ℝ) ≤ 288 * (b : ℝ) ^ (2 * t) + 2 ∧ HasLeadingDigits p b f n) ∧
    (∃ n : ℕ,
      (n : ℝ) ≤ 130 * (b : ℝ) ^ (3 * t) +
        29400 * (b : ℝ) ^ ((3 * (t : ℝ)) / 2) ∧
      HasLeadingDigits PL b f n) := by
  exact ⟨partition_leading_digits_bound p hf hp,
    plane_partition_leading_digits_bound PL hf A
      (planeConstantBounds_of_interval hA_lower hA_upper) hPL⟩

/-- The same result stated with the paper's least-occurrence notation. -/
theorem theorem_1_1_first_occurrence
    (p PL : ℕ → ℕ) {b t f : ℕ} (hf : IsDigitString b t f)
    (A : ℝ) (hA_lower : 1 ≤ A) (hA_upper : 54 * A ≤ 65)
    (hp : PartitionEstimate p b) (hPL : PlanePartitionEstimate PL b A) :
    (firstOccurrence p b f : ℝ) ≤ 288 * (b : ℝ) ^ (2 * t) + 2 ∧
    (firstOccurrence PL b f : ℝ) ≤ 130 * (b : ℝ) ^ (3 * t) +
      29400 * (b : ℝ) ^ ((3 * (t : ℝ)) / 2) := by
  obtain ⟨hp_hit, hPL_hit⟩ := theorem_1_1 p PL hf A hA_lower hA_upper hp hPL
  exact ⟨firstOccurrence_le_of_exists hp_hit, firstOccurrence_le_of_exists hPL_hit⟩

end PlanePartition

end

end PartitionDigits
