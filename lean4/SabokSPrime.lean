import Mathlib

/-!
# Finite and Urysohn obstructions for Sabok's `S'`

This file formalizes the algebraic and metric core of
`sabok_sprime_obstructions_proc_revised.tex`.

* The finite section checks the four-cycle distance matrix and exhibits two
  distinct probability vectors with the same distance-row barycenter.
* The Urysohn section works over a metric space satisfying the exact finite
  rational one-point extension property used in the paper.  It constructs the
  required equilateral and plateau triangles, proves midpoint extremality of
  the four Katetov functions, and packages the two different extreme midpoint
  representations.

The custom predicate `MidpointExtreme` is the midpoint characterization of an
extreme point.  For a convex set it is equivalent to the usual definition.
-/

open scoped BigOperators

namespace SabokSPrime

noncomputable section

section FiniteObstruction

abbrev C4 := Fin 4

/-- The diameter-one cycle distance matrix from the paper. -/
def c4Matrix : Matrix C4 C4 ℝ :=
  fun i j =>
    if i = j then 0
    else if (i.val + 2) % 4 = j.val then 1
    else 1 / 2

/-- The two probability vectors supported on the opposite pairs `{0,2}` and `{1,3}`. -/
def p02 : C4 → ℝ := ![1 / 2, 0, 1 / 2, 0]
def p13 : C4 → ℝ := ![0, 1 / 2, 0, 1 / 2]

/-- Barycenter of the distance rows, written as multiplication by the distance matrix. -/
def c4Barycenter (p : C4 → ℝ) : C4 → ℝ := fun j => ∑ i, p i * c4Matrix i j

theorem c4_row_relation :
    (fun j => c4Matrix 0 j + c4Matrix 2 j) =
      (fun j => c4Matrix 1 j + c4Matrix 3 j) := by
  funext j
  fin_cases j <;> norm_num [c4Matrix, Fin.ext_iff]

theorem p02_is_probability :
    (∀ i, 0 ≤ p02 i) ∧ ∑ i, p02 i = 1 := by
  constructor
  · intro i
    fin_cases i <;> norm_num [p02]
  · norm_num [p02, Fin.sum_univ_succ]

theorem p13_is_probability :
    (∀ i, 0 ≤ p13 i) ∧ ∑ i, p13 i = 1 := by
  constructor
  · intro i
    fin_cases i <;> norm_num [p13]
  · norm_num [p13, Fin.sum_univ_succ]

theorem p02_ne_p13 : p02 ≠ p13 := by
  intro h
  have := congrFun h 0
  norm_num [p02, p13] at this

theorem c4_nonunique_barycenter : c4Barycenter p02 = c4Barycenter p13 := by
  funext j
  have hrel := congrFun c4_row_relation j
  simp [c4Barycenter, p02, p13, Fin.sum_univ_succ]
  linarith

/-- A concise formal witness that the distance-row polytope does not have
unique barycentric coordinates. -/
theorem c4_finite_obstruction :
    ∃ p q : C4 → ℝ,
      p ≠ q ∧
      (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧
      (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1 ∧
      c4Barycenter p = c4Barycenter q := by
  refine ⟨p02, p13, p02_ne_p13, p02_is_probability.1,
    p02_is_probability.2, p13_is_probability.1, p13_is_probability.2, ?_⟩
  exact c4_nonunique_barycenter

end FiniteObstruction

section Katetov

variable {D : Type*} [PseudoMetricSpace D]

/-- Bounded Katetov functions with values in `[0,1]`. -/
def IsBoundedKatetov (f : D → ℝ) : Prop :=
  (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
    ∀ x y, |f x - f y| ≤ dist x y ∧ dist x y ≤ f x + f y

/-- The bounded Katetov functions, viewed as a concrete convex set. -/
def katetovSet (D : Type*) [PseudoMetricSpace D] : Set (D → ℝ) :=
  {f | IsBoundedKatetov f}

@[simp] lemma mem_katetovSet {f : D → ℝ} :
    f ∈ katetovSet D ↔ IsBoundedKatetov f := Iff.rfl

/-- The defining Katetov inequalities are preserved by convex combinations. -/
theorem katetovSet_convex : Convex ℝ (katetovSet D) := by
  intro f hf g hg a b ha hb hab
  change IsBoundedKatetov (a • f + b • g)
  change IsBoundedKatetov f at hf
  change IsBoundedKatetov g at hg
  constructor
  · intro x
    constructor
    · change 0 ≤ a * f x + b * g x
      exact add_nonneg (mul_nonneg ha (hf.1 x).1) (mul_nonneg hb (hg.1 x).1)
    · change a * f x + b * g x ≤ 1
      calc
        a * f x + b * g x ≤ a * 1 + b * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left (hf.1 x).2 ha)
            (mul_le_mul_of_nonneg_left (hg.1 x).2 hb)
        _ = 1 := by linarith
  · intro x y
    constructor
    · change
        |(a * f x + b * g x) - (a * f y + b * g y)| ≤ dist x y
      have hfxy := (hf.2 x y).1
      have hgxy := (hg.2 x y).1
      rw [abs_le] at hfxy hgxy ⊢
      constructor
      · calc
          -dist x y = a * (-dist x y) + b * (-dist x y) := by
            rw [← add_mul, hab, one_mul]
          _ ≤ a * (f x - f y) + b * (g x - g y) :=
            add_le_add
              (mul_le_mul_of_nonneg_left hfxy.1 ha)
              (mul_le_mul_of_nonneg_left hgxy.1 hb)
          _ = (a * f x + b * g x) - (a * f y + b * g y) := by ring
      · calc
          (a * f x + b * g x) - (a * f y + b * g y) =
              a * (f x - f y) + b * (g x - g y) := by ring
          _ ≤ a * dist x y + b * dist x y :=
            add_le_add
              (mul_le_mul_of_nonneg_left hfxy.2 ha)
              (mul_le_mul_of_nonneg_left hgxy.2 hb)
          _ = dist x y := by rw [← add_mul, hab, one_mul]
    · change dist x y ≤
        (a * f x + b * g x) + (a * f y + b * g y)
      calc
        dist x y = a * dist x y + b * dist x y := by
          rw [← add_mul, hab, one_mul]
        _ ≤ a * (f x + f y) + b * (g x + g y) :=
          add_le_add
            (mul_le_mul_of_nonneg_left (hf.2 x y).2 ha)
            (mul_le_mul_of_nonneg_left (hg.2 x y).2 hb)
        _ = (a * f x + b * g x) + (a * f y + b * g y) := by ring

/-- Midpoint characterization of an extreme point of the Katetov set. -/
def MidpointExtreme (e : D → ℝ) : Prop :=
  IsBoundedKatetov e ∧
    ∀ u v : D → ℝ,
      IsBoundedKatetov u →
      IsBoundedKatetov v →
      (∀ x, (u x + v x) / 2 = e x) →
      u = e ∧ v = e

/-- The elementary midpoint predicate agrees with Mathlib's standard extreme-point
predicate because the Katetov set is convex. -/
theorem midpointExtreme_iff_mem_extremePoints {e : D → ℝ} :
    MidpointExtreme e ↔ e ∈ (katetovSet D).extremePoints ℝ := by
  constructor
  · intro he
    rw [mem_extremePoints_iff_left]
    refine ⟨he.1, ?_⟩
    intro u hu v hv hopen
    rcases hopen with ⟨a, b, ha, hb, hab, hcombo⟩
    by_cases hhalf : (1 / 2 : ℝ) ≤ a
    · let w : D → ℝ := (2 * a - 1) • u + (2 * b) • v
      have hca : 0 ≤ 2 * a - 1 := by linarith
      have hcb : 0 ≤ 2 * b := by positivity
      have hsum : (2 * a - 1) + 2 * b = 1 := by linarith
      have hw : IsBoundedKatetov w := by
        exact katetovSet_convex hu hv hca hcb hsum
      have hmid : ∀ x, (u x + w x) / 2 = e x := by
        intro x
        have hx := congrFun hcombo x
        change a * u x + b * v x = e x at hx
        change (u x + ((2 * a - 1) * u x + 2 * b * v x)) / 2 = e x
        linarith
      exact (he.2 u w hu hw hmid).1
    · have hbhalf : (1 / 2 : ℝ) ≤ b := by linarith
      let w : D → ℝ := (2 * a) • u + (2 * b - 1) • v
      have hca : 0 ≤ 2 * a := by positivity
      have hcb : 0 ≤ 2 * b - 1 := by linarith
      have hsum : 2 * a + (2 * b - 1) = 1 := by linarith
      have hw : IsBoundedKatetov w := by
        exact katetovSet_convex hu hv hca hcb hsum
      have hmid : ∀ x, (w x + v x) / 2 = e x := by
        intro x
        have hx := congrFun hcombo x
        change a * u x + b * v x = e x at hx
        change (((2 * a) * u x + (2 * b - 1) * v x) + v x) / 2 = e x
        linarith
      have hve : v = e := (he.2 w v hw hv hmid).2
      funext x
      have hx := congrFun hcombo x
      have hvx := congrFun hve x
      change a * u x + b * v x = e x at hx
      have ha0 : a ≠ 0 := ne_of_gt ha
      have hx' : a * u x + b * e x = e x := by
        simpa only [hvx] using hx
      have hxe : a * e x + b * e x = e x := by
        calc
          a * e x + b * e x = (a + b) * e x := by ring
          _ = e x := by rw [hab, one_mul]
      have hae : a * u x = a * e x := by linarith
      have hmul : a * (u x - e x) = 0 := by
        rw [mul_sub, hae, sub_self]
      exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left ha0)
  · intro he
    have heK : e ∈ katetovSet D :=
      (extremePoints_subset (𝕜 := ℝ)) he
    refine ⟨heK, ?_⟩
    intro u v hu hv hmid
    have hopen : e ∈ openSegment ℝ u v := by
      refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
      funext x
      change (1 / 2 : ℝ) * u x + (1 / 2 : ℝ) * v x = e x
      linarith [hmid x]
    exact (mem_extremePoints.mp he).2 u hu v hv hopen

/-- The exact rational finite one-point extension property used for
`ℚU₁`.  A finite family is represented by `Fin n`; repetitions are harmless. -/
def RationalOnePointExtension (D : Type*) [PseudoMetricSpace D] : Prop :=
  ∀ {n : ℕ} (x : Fin n → D) (p : Fin n → ℚ),
    (∀ i, (0 : ℚ) ≤ p i ∧ p i ≤ 1) →
    (∀ i j,
      |((p i : ℚ) : ℝ) - ((p j : ℚ) : ℝ)| ≤ dist (x i) (x j) ∧
        dist (x i) (x j) ≤ (p i : ℝ) + (p j : ℝ)) →
    ∃ z : D, ∀ i, dist z (x i) = (p i : ℝ)

lemma tight_at_one
    {u v e : D → ℝ}
    (hu : IsBoundedKatetov u) (hv : IsBoundedKatetov v)
    (hm : ∀ x, (u x + v x) / 2 = e x)
    {x : D} (hx : e x = 1) : u x = v x := by
  have hu1 := (hu.1 x).2
  have hv1 := (hv.1 x).2
  have hm' := hm x
  linarith

lemma tight_lower
    {u v e : D → ℝ}
    (hu : IsBoundedKatetov u) (hv : IsBoundedKatetov v)
    (hm : ∀ x, (u x + v x) / 2 = e x)
    {x y : D} (hxy : e x + e y = dist x y) :
    u x + u y = v x + v y := by
  have huLower := (hu.2 x y).2
  have hvLower := (hv.2 x y).2
  have hmx := hm x
  have hmy := hm y
  linarith

lemma tight_difference
    {u v e : D → ℝ}
    (hu : IsBoundedKatetov u) (hv : IsBoundedKatetov v)
    (hm : ∀ x, (u x + v x) / 2 = e x)
    {x y : D} (hxy : e x - e y = dist x y) :
    u x - u y = v x - v y := by
  have huAbs := (hu.2 x y).1
  have hvAbs := (hv.2 x y).1
  have huUpper : u x - u y ≤ dist x y := le_trans (le_abs_self _) huAbs
  have hvUpper : v x - v y ≤ dist x y := le_trans (le_abs_self _) hvAbs
  have hmx := hm x
  have hmy := hm y
  linarith

lemma const_one_katetov (hdiam : ∀ x y : D, dist x y ≤ 1) :
    IsBoundedKatetov (fun _ : D => (1 : ℝ)) := by
  constructor
  · intro x
    norm_num
  · intro x y
    constructor
    · simpa using dist_nonneg
    · linarith [hdiam x y]

lemma const_half_katetov (hdiam : ∀ x y : D, dist x y ≤ 1) :
    IsBoundedKatetov (fun _ : D => (1 / 2 : ℝ)) := by
  constructor
  · intro x
    norm_num
  · intro x y
    constructor
    · simpa using dist_nonneg
    · norm_num
      exact hdiam x y

lemma exists_point_at_distance_one
    (hdiam : ∀ x y : D, dist x y ≤ 1)
    (hext : RationalOnePointExtension D)
    {n : ℕ} (x : Fin n → D) :
    ∃ z : D, ∀ i, dist z (x i) = 1 := by
  obtain ⟨z, hz⟩ := hext x (fun _ => (1 : ℚ)) (by
    intro i
    norm_num) (by
    intro i j
    constructor
    · norm_num
    · norm_num
      linarith [hdiam (x i) (x j)])
  exact ⟨z, fun i => by simpa using hz i⟩

lemma equilateral_through_point
    (hdiam : ∀ x y : D, dist x y ≤ 1)
    (hext : RationalOnePointExtension D)
    (x : D) :
    ∃ y z : D, dist x y = 1 ∧ dist y z = 1 ∧ dist z x = 1 := by
  obtain ⟨y, hy⟩ := exists_point_at_distance_one hdiam hext (fun _ : Fin 1 => x)
  obtain ⟨z, hz⟩ := exists_point_at_distance_one hdiam hext ![x, y]
  refine ⟨y, z, ?_, ?_, ?_⟩
  · simpa [dist_comm] using hy 0
  · simpa [dist_comm] using hz 1
  · simpa using hz 0

theorem const_one_extreme (hdiam : ∀ x y : D, dist x y ≤ 1) :
    MidpointExtreme (fun _ : D => (1 : ℝ)) := by
  refine ⟨const_one_katetov hdiam, ?_⟩
  intro u v hu hv hm
  have huv : u = v := by
    funext x
    exact tight_at_one hu hv hm rfl
  have hve : v = (fun _ : D => (1 : ℝ)) := by
    funext x
    have hmx := hm x
    rw [huv] at hmx
    norm_num at hmx ⊢
    linarith
  exact ⟨huv.trans hve, hve⟩

theorem const_half_extreme
    (hdiam : ∀ x y : D, dist x y ≤ 1)
    (hext : RationalOnePointExtension D) :
    MidpointExtreme (fun _ : D => (1 / 2 : ℝ)) := by
  refine ⟨const_half_katetov hdiam, ?_⟩
  intro u v hu hv hm
  have huv : u = v := by
    funext x
    obtain ⟨y, z, hxy, hyz, hzx⟩ := equilateral_through_point hdiam hext x
    have h₁ := tight_lower hu hv hm (x := x) (y := y) (by norm_num [hxy])
    have h₂ := tight_lower hu hv hm (x := y) (y := z) (by norm_num [hyz])
    have h₃ := tight_lower hu hv hm (x := z) (y := x) (by norm_num [hzx])
    linarith
  have hve : v = (fun _ : D => (1 / 2 : ℝ)) := by
    funext x
    have hmx := hm x
    rw [huv] at hmx
    norm_num at hmx ⊢
    linarith
  exact ⟨huv.trans hve, hve⟩

/-- A named side-one equilateral triple. -/
structure EquilateralTriple (D : Type*) [PseudoMetricSpace D] where
  a₀ : D
  a₁ : D
  a₂ : D
  dist₀₁ : dist a₀ a₁ = 1
  dist₁₂ : dist a₁ a₂ = 1
  dist₂₀ : dist a₂ a₀ = 1

variable (A : EquilateralTriple D)

/-- Distance to the three-point set underlying `A`. -/
def radius (x : D) : ℝ := min (dist x A.a₀) (min (dist x A.a₁) (dist x A.a₂))

lemma radius_nonneg (x : D) : 0 ≤ radius A x := by
  exact le_min (dist_nonneg : 0 ≤ dist x A.a₀)
    (le_min (dist_nonneg : 0 ≤ dist x A.a₁) (dist_nonneg : 0 ≤ dist x A.a₂))

lemma radius_le_dist₀ (x : D) : radius A x ≤ dist x A.a₀ := by
  exact min_le_left _ _

lemma radius_le_dist₁ (x : D) : radius A x ≤ dist x A.a₁ := by
  exact le_trans (min_le_right _ _) (min_le_left _ _)

lemma radius_le_dist₂ (x : D) : radius A x ≤ dist x A.a₂ := by
  exact le_trans (min_le_right _ _) (min_le_right _ _)

lemma radius_at₀ : radius A A.a₀ = 0 := by
  simp [radius]

lemma radius_at₁ : radius A A.a₁ = 0 := by
  simp [radius]

lemma radius_at₂ : radius A A.a₂ = 0 := by
  simp [radius]

lemma radius_attained (x : D) :
    (radius A x = dist x A.a₀) ∨
      (radius A x = dist x A.a₁) ∨
        radius A x = dist x A.a₂ := by
  unfold radius
  rcases min_choice (dist x A.a₀) (min (dist x A.a₁) (dist x A.a₂)) with h₀ | h₁₂
  · exact Or.inl h₀
  · rcases min_choice (dist x A.a₁) (dist x A.a₂) with h₁ | h₂
    · exact Or.inr (Or.inl (h₁₂.trans h₁))
    · exact Or.inr (Or.inr (h₁₂.trans h₂))

lemma radius_le_one (hdiam : ∀ x y : D, dist x y ≤ 1) (x : D) : radius A x ≤ 1 := by
  exact le_trans (radius_le_dist₀ A x) (hdiam x A.a₀)

lemma radius_lipschitz (x y : D) : |radius A x - radius A y| ≤ dist x y := by
  have hxy : radius A x ≤ dist x y + radius A y := by
    rcases radius_attained A y with h | h | h
    · calc
        radius A x ≤ dist x A.a₀ := radius_le_dist₀ A x
        _ ≤ dist x y + dist y A.a₀ := dist_triangle _ _ _
        _ = dist x y + radius A y := by rw [h]
    · calc
        radius A x ≤ dist x A.a₁ := radius_le_dist₁ A x
        _ ≤ dist x y + dist y A.a₁ := dist_triangle _ _ _
        _ = dist x y + radius A y := by rw [h]
    · calc
        radius A x ≤ dist x A.a₂ := radius_le_dist₂ A x
        _ ≤ dist x y + dist y A.a₂ := dist_triangle _ _ _
        _ = dist x y + radius A y := by rw [h]
  have hyx : radius A y ≤ dist x y + radius A x := by
    rw [dist_comm]
    rcases radius_attained A x with h | h | h
    · calc
        radius A y ≤ dist y A.a₀ := radius_le_dist₀ A y
        _ ≤ dist y x + dist x A.a₀ := dist_triangle _ _ _
        _ = dist y x + radius A x := by rw [h]
    · calc
        radius A y ≤ dist y A.a₁ := radius_le_dist₁ A y
        _ ≤ dist y x + dist x A.a₁ := dist_triangle _ _ _
        _ = dist y x + radius A x := by rw [h]
    · calc
        radius A y ≤ dist y A.a₂ := radius_le_dist₂ A y
        _ ≤ dist y x + dist x A.a₂ := dist_triangle _ _ _
        _ = dist y x + radius A x := by rw [h]
  rw [abs_le]
  constructor <;> linarith

/-- The two half-radius functions from the paper. -/
def fA (x : D) : ℝ := min 1 (1 / 2 + radius A x)
def gA (x : D) : ℝ := max (1 / 2) (1 - radius A x)

private lemma abs_min_half_add_le {a b d : ℝ} (h : |a - b| ≤ d) :
    |min 1 (1 / 2 + a) - min 1 (1 / 2 + b)| ≤ d := by
  rw [abs_le] at h ⊢
  simp only [min_def]
  split_ifs <;> constructor <;> linarith

private lemma abs_max_one_sub_le {a b d : ℝ} (h : |a - b| ≤ d) :
    |max (1 / 2) (1 - a) - max (1 / 2) (1 - b)| ≤ d := by
  rw [abs_le] at h ⊢
  simp only [max_def]
  split_ifs <;> constructor <;> linarith

lemma fA_katetov (hdiam : ∀ x y : D, dist x y ≤ 1) : IsBoundedKatetov (fA A) := by
  constructor
  · intro x
    constructor
    · have hr := radius_nonneg A x
      simp only [fA, min_def]
      split_ifs <;> linarith
    · exact min_le_left _ _
  · intro x y
    constructor
    · exact abs_min_half_add_le (radius_lipschitz A x y)
    · have hfx : 1 / 2 ≤ fA A x := by
        have hr := radius_nonneg A x
        simp only [fA, min_def]
        split_ifs <;> linarith
      have hfy : 1 / 2 ≤ fA A y := by
        have hr := radius_nonneg A y
        simp only [fA, min_def]
        split_ifs <;> linarith
      linarith [hdiam x y]

lemma gA_katetov (hdiam : ∀ x y : D, dist x y ≤ 1) : IsBoundedKatetov (gA A) := by
  constructor
  · intro x
    constructor
    · exact le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) (le_max_left _ _)
    · have hr := radius_nonneg A x
      simp only [gA, max_def]
      split_ifs <;> linarith
  · intro x y
    constructor
    · exact abs_max_one_sub_le (radius_lipschitz A x y)
    · have hgx : 1 / 2 ≤ gA A x := le_max_left _ _
      have hgy : 1 / 2 ≤ gA A y := le_max_left _ _
      linarith [hdiam x y]

lemma fA_add_gA (hdiam : ∀ x y : D, dist x y ≤ 1) (x : D) :
    fA A x + gA A x = 3 / 2 := by
  have hr0 := radius_nonneg A x
  have hr1 := radius_le_one A hdiam x
  simp only [fA, gA, min_def, max_def]
  split_ifs <;> linarith

@[simp] lemma fA_at₀ : fA A A.a₀ = 1 / 2 := by norm_num [fA, radius_at₀]
@[simp] lemma fA_at₁ : fA A A.a₁ = 1 / 2 := by norm_num [fA, radius_at₁]
@[simp] lemma fA_at₂ : fA A A.a₂ = 1 / 2 := by norm_num [fA, radius_at₂]
@[simp] lemma gA_at₀ : gA A A.a₀ = 1 := by norm_num [gA, radius_at₀]
@[simp] lemma gA_at₁ : gA A A.a₁ = 1 := by norm_num [gA, radius_at₁]
@[simp] lemma gA_at₂ : gA A A.a₂ = 1 := by norm_num [gA, radius_at₂]

theorem fA_extreme (hdiam : ∀ x y : D, dist x y ≤ 1) : MidpointExtreme (fA A) := by
  refine ⟨fA_katetov A hdiam, ?_⟩
  intro u v hu hv hm
  have h₀₁ := tight_lower hu hv hm (x := A.a₀) (y := A.a₁) (by norm_num [A.dist₀₁])
  have h₁₂ := tight_lower hu hv hm (x := A.a₁) (y := A.a₂) (by norm_num [A.dist₁₂])
  have h₂₀ := tight_lower hu hv hm (x := A.a₂) (y := A.a₀) (by norm_num [A.dist₂₀])
  have huv₀ : u A.a₀ = v A.a₀ := by linarith
  have huv₁ : u A.a₁ = v A.a₁ := by linarith
  have huv₂ : u A.a₂ = v A.a₂ := by linarith
  have huv : u = v := by
    funext x
    by_cases hx : fA A x = 1
    · exact tight_at_one hu hv hm hx
    · have hrlt : radius A x < 1 / 2 := by
        by_contra h
        have hge : 1 / 2 ≤ radius A x := le_of_not_gt h
        have hmin : (1 : ℝ) ≤ 1 / 2 + radius A x := by
          norm_num at hge ⊢
          linarith
        have : fA A x = 1 := by
          unfold fA
          exact min_eq_left hmin
        exact hx this
      have hfx : fA A x = 1 / 2 + radius A x := by
        have hmin : 1 / 2 + radius A x ≤ (1 : ℝ) := by
          norm_num at hrlt ⊢
          linarith
        unfold fA
        exact min_eq_right hmin
      rcases radius_attained A x with h | h | h
      · have hd : fA A x - fA A A.a₀ = dist x A.a₀ := by simp [hfx, h]
        have ht := tight_difference hu hv hm hd
        linarith
      · have hd : fA A x - fA A A.a₁ = dist x A.a₁ := by simp [hfx, h]
        have ht := tight_difference hu hv hm hd
        linarith
      · have hd : fA A x - fA A A.a₂ = dist x A.a₂ := by simp [hfx, h]
        have ht := tight_difference hu hv hm hd
        linarith
  have hve : v = fA A := by
    funext x
    have hmx := hm x
    rw [huv] at hmx
    norm_num at hmx ⊢
    linarith
  exact ⟨huv.trans hve, hve⟩

/-- Every point on the `g = 1/2` plateau lies in a side-one equilateral
triangle which remains in the plateau. -/
lemma plateau_triangles
    (hdiam : ∀ x y : D, dist x y ≤ 1)
    (hext : RationalOnePointExtension D)
    (x : D) (hx : 1 / 2 ≤ radius A x) :
    ∃ y z : D,
      radius A y = 1 / 2 ∧ radius A z = 1 / 2 ∧
        dist x y = 1 ∧ dist y z = 1 ∧ dist z x = 1 := by
  have hx₀ : 1 / 2 ≤ dist x A.a₀ := le_trans hx (radius_le_dist₀ A x)
  have hx₁ : 1 / 2 ≤ dist x A.a₁ := le_trans hx (radius_le_dist₁ A x)
  have hx₂ : 1 / 2 ≤ dist x A.a₂ := le_trans hx (radius_le_dist₂ A x)
  have hA₀₂ : dist A.a₀ A.a₂ = 1 := by simpa [dist_comm] using A.dist₂₀
  let ptsY : Fin 4 → D := ![x, A.a₀, A.a₁, A.a₂]
  let valY : Fin 4 → ℚ := ![1, 1 / 2, 1 / 2, 1 / 2]
  have valY_bounds : ∀ i, (0 : ℚ) ≤ valY i ∧ valY i ≤ 1 := by
    intro i
    fin_cases i <;> norm_num [valY]
  have valY_kat : ∀ i j,
      |((valY i : ℚ) : ℝ) - ((valY j : ℚ) : ℝ)| ≤ dist (ptsY i) (ptsY j) ∧
        dist (ptsY i) (ptsY j) ≤ (valY i : ℝ) + (valY j : ℝ) := by
    intro i j
    fin_cases i <;> fin_cases j <;> constructor <;>
      simp [ptsY, valY, A.dist₀₁, A.dist₁₂, A.dist₂₀, dist_comm] <;>
      norm_num at * <;>
      linarith [hA₀₂, hdiam x A.a₀, hdiam x A.a₁, hdiam x A.a₂]
  obtain ⟨y, hy⟩ := hext ptsY valY valY_bounds valY_kat
  have hyx : dist y x = 1 := by simpa [ptsY, valY] using hy 0
  have hy₀ : dist y A.a₀ = 1 / 2 := by simpa [ptsY, valY] using hy 1
  have hy₁ : dist y A.a₁ = 1 / 2 := by simpa [ptsY, valY] using hy 2
  have hy₂ : dist y A.a₂ = 1 / 2 := by simpa [ptsY, valY] using hy 3
  have hry : radius A y = 1 / 2 := by simp [radius, hy₀, hy₁, hy₂]
  let ptsZ : Fin 5 → D := ![x, y, A.a₀, A.a₁, A.a₂]
  let valZ : Fin 5 → ℚ := ![1, 1, 1 / 2, 1 / 2, 1 / 2]
  have valZ_bounds : ∀ i, (0 : ℚ) ≤ valZ i ∧ valZ i ≤ 1 := by
    intro i
    fin_cases i <;> norm_num [valZ]
  have valZ_kat : ∀ i j,
      |((valZ i : ℚ) : ℝ) - ((valZ j : ℚ) : ℝ)| ≤ dist (ptsZ i) (ptsZ j) ∧
        dist (ptsZ i) (ptsZ j) ≤ (valZ i : ℝ) + (valZ j : ℝ) := by
    intro i j
    fin_cases i <;> fin_cases j <;> constructor <;>
      simp [ptsZ, valZ, A.dist₀₁, A.dist₁₂, A.dist₂₀,
        hyx, hy₀, hy₁, hy₂, dist_comm] <;>
      norm_num at * <;>
      linarith [hA₀₂, hdiam x y, hdiam y x,
        hdiam x A.a₀, hdiam x A.a₁, hdiam x A.a₂]
  obtain ⟨z, hz⟩ := hext ptsZ valZ valZ_bounds valZ_kat
  have hzx : dist z x = 1 := by simpa [ptsZ, valZ] using hz 0
  have hzy : dist z y = 1 := by simpa [ptsZ, valZ] using hz 1
  have hz₀ : dist z A.a₀ = 1 / 2 := by simpa [ptsZ, valZ] using hz 2
  have hz₁ : dist z A.a₁ = 1 / 2 := by simpa [ptsZ, valZ] using hz 3
  have hz₂ : dist z A.a₂ = 1 / 2 := by simpa [ptsZ, valZ] using hz 4
  have hrz : radius A z = 1 / 2 := by simp [radius, hz₀, hz₁, hz₂]
  exact ⟨y, z, hry, hrz, by simpa [dist_comm] using hyx,
    by simpa [dist_comm] using hzy, hzx⟩

theorem gA_extreme
    (hdiam : ∀ x y : D, dist x y ≤ 1)
    (hext : RationalOnePointExtension D) : MidpointExtreme (gA A) := by
  refine ⟨gA_katetov A hdiam, ?_⟩
  intro u v hu hv hm
  have huv₀ : u A.a₀ = v A.a₀ := tight_at_one hu hv hm (by simp)
  have huv₁ : u A.a₁ = v A.a₁ := tight_at_one hu hv hm (by simp)
  have huv₂ : u A.a₂ = v A.a₂ := tight_at_one hu hv hm (by simp)
  have huv : u = v := by
    funext x
    by_cases hx : radius A x < 1 / 2
    · have hgx : gA A x = 1 - radius A x := by
        have hmax : (1 / 2 : ℝ) ≤ 1 - radius A x := by
          norm_num at hx ⊢
          linarith
        unfold gA
        exact max_eq_right hmax
      rcases radius_attained A x with h | h | h
      · have hd : gA A A.a₀ - gA A x = dist A.a₀ x := by
          simp [hgx, h, dist_comm]
        have ht := tight_difference hu hv hm hd
        linarith
      · have hd : gA A A.a₁ - gA A x = dist A.a₁ x := by
          simp [hgx, h, dist_comm]
        have ht := tight_difference hu hv hm hd
        linarith
      · have hd : gA A A.a₂ - gA A x = dist A.a₂ x := by
          simp [hgx, h, dist_comm]
        have ht := tight_difference hu hv hm hd
        linarith
    · have hx' : 1 / 2 ≤ radius A x := le_of_not_gt hx
      obtain ⟨y, z, hry, hrz, hxy, hyz, hzx⟩ := plateau_triangles A hdiam hext x hx'
      have hmax : 1 - radius A x ≤ (1 / 2 : ℝ) := by
        norm_num at hx' ⊢
        linarith
      have hgx : gA A x = 1 / 2 := by
        unfold gA
        exact max_eq_left hmax
      have hgy : gA A y = 1 / 2 := by norm_num [gA, hry]
      have hgz : gA A z = 1 / 2 := by norm_num [gA, hrz]
      have h₁ := tight_lower hu hv hm (x := x) (y := y) (by norm_num [hgx, hgy, hxy])
      have h₂ := tight_lower hu hv hm (x := y) (y := z) (by norm_num [hgy, hgz, hyz])
      have h₃ := tight_lower hu hv hm (x := z) (y := x) (by norm_num [hgz, hgx, hzx])
      linarith
  have hve : v = gA A := by
    funext x
    have hmx := hm x
    rw [huv] at hmx
    norm_num at hmx ⊢
    linarith
  exact ⟨huv.trans hve, hve⟩

/-- Four extreme points with two genuinely different two-point supports and
the same midpoint.  This is the finite-support obstruction to Choquet
uniqueness used in the paper. -/
def HasNonuniqueExtremeMidpoint : Prop :=
  ∃ f g one half : D → ℝ,
    MidpointExtreme f ∧ MidpointExtreme g ∧
      MidpointExtreme one ∧ MidpointExtreme half ∧
      ({f, g} : Set (D → ℝ)) ≠ {one, half} ∧
      ∀ x, (f x + g x) / 2 = (one x + half x) / 2

theorem urysohn_extreme_midpoint_obstruction
    (A : EquilateralTriple D)
    (hdiam : ∀ x y : D, dist x y ≤ 1)
    (hext : RationalOnePointExtension D) :
    HasNonuniqueExtremeMidpoint (D := D) := by
  let one : D → ℝ := fun _ => 1
  let half : D → ℝ := fun _ => 1 / 2
  obtain ⟨b, hb⟩ := exists_point_at_distance_one hdiam hext ![A.a₀, A.a₁, A.a₂]
  have hb₀ : dist b A.a₀ = 1 := by simpa using hb 0
  have hb₁ : dist b A.a₁ = 1 := by simpa using hb 1
  have hb₂ : dist b A.a₂ = 1 := by simpa using hb 2
  have hrb : radius A b = 1 := by simp [radius, hb₀, hb₁, hb₂]
  have hf_ne_one : fA A ≠ one := by
    intro h
    have := congrFun h A.a₀
    norm_num [one] at this
  have hf_ne_half : fA A ≠ half := by
    intro h
    have := congrFun h b
    norm_num [fA, hrb, half] at this
  have hpairs : ({fA A, gA A} : Set (D → ℝ)) ≠ {one, half} := by
    intro hsets
    have hfmem : fA A ∈ ({one, half} : Set (D → ℝ)) := by
      rw [← hsets]
      simp
    rcases hfmem with hf | hf
    · exact hf_ne_one hf
    · exact hf_ne_half hf
  refine ⟨fA A, gA A, one, half, fA_extreme A hdiam,
    gA_extreme A hdiam hext, const_one_extreme hdiam,
    const_half_extreme hdiam hext, hpairs, ?_⟩
  intro x
  have hfg := fA_add_gA A hdiam x
  change (fA A x + gA A x) / 2 = ((1 : ℝ) + 1 / 2) / 2
  linarith

/-- Closed form of the Urysohn argument: a single point, the diameter bound,
and rational finite extension already produce the equilateral triple and the
nonunique extreme midpoint representation. -/
theorem rational_urysohn_core_obstruction
    (x₀ : D)
    (hdiam : ∀ x y : D, dist x y ≤ 1)
    (hext : RationalOnePointExtension D) :
    HasNonuniqueExtremeMidpoint (D := D) := by
  obtain ⟨y, z, hxy, hyz, hzx⟩ := equilateral_through_point hdiam hext x₀
  let A : EquilateralTriple D :=
    { a₀ := x₀
      a₁ := y
      a₂ := z
      dist₀₁ := hxy
      dist₁₂ := hyz
      dist₂₀ := hzx }
  exact urysohn_extreme_midpoint_obstruction A hdiam hext

/-! ## Standard extreme points and the two-atomic obstruction -/

/-- Two different unordered pairs of standard extreme points with the same
equal-weight barycenter. -/
def HasNonuniqueExtremePointMidpoint : Prop :=
  ∃ f g one half : D → ℝ,
    f ∈ (katetovSet D).extremePoints ℝ ∧
      g ∈ (katetovSet D).extremePoints ℝ ∧
      one ∈ (katetovSet D).extremePoints ℝ ∧
      half ∈ (katetovSet D).extremePoints ℝ ∧
      ({f, g} : Set (D → ℝ)) ≠ {one, half} ∧
      ∀ x, (f x + g x) / 2 = (one x + half x) / 2

/-- The internal midpoint obstruction is exactly an obstruction formulated with
Mathlib's standard extreme points. -/
theorem hasNonuniqueExtremeMidpoint_iff_standard :
    HasNonuniqueExtremeMidpoint (D := D) ↔
      HasNonuniqueExtremePointMidpoint (D := D) := by
  constructor
  · rintro ⟨f, g, one, half, hf, hg, hone, hhalf, hpairs, hmid⟩
    exact ⟨f, g, one, half,
      midpointExtreme_iff_mem_extremePoints.mp hf,
      midpointExtreme_iff_mem_extremePoints.mp hg,
      midpointExtreme_iff_mem_extremePoints.mp hone,
      midpointExtreme_iff_mem_extremePoints.mp hhalf,
      hpairs, hmid⟩
  · rintro ⟨f, g, one, half, hf, hg, hone, hhalf, hpairs, hmid⟩
    exact ⟨f, g, one, half,
      midpointExtreme_iff_mem_extremePoints.mpr hf,
      midpointExtreme_iff_mem_extremePoints.mpr hg,
      midpointExtreme_iff_mem_extremePoints.mpr hone,
      midpointExtreme_iff_mem_extremePoints.mpr hhalf,
      hpairs, hmid⟩

/-- The equal-weight two-atomic uniqueness consequence needed from Choquet
uniqueness, stated entirely with standard extreme points. -/
def HasUniqueExtremeMidpointRepresentation : Prop :=
  ∀ f g h k : D → ℝ,
    f ∈ (katetovSet D).extremePoints ℝ →
    g ∈ (katetovSet D).extremePoints ℝ →
    h ∈ (katetovSet D).extremePoints ℝ →
    k ∈ (katetovSet D).extremePoints ℝ →
    (∀ x, (f x + g x) / 2 = (h x + k x) / 2) →
    ({f, g} : Set (D → ℝ)) = {h, k}

/-- A nonunique standard-extreme midpoint representation refutes the
corresponding two-atomic uniqueness property. -/
theorem nonuniqueExtremePointMidpoint_not_uniqueRepresentation
    (h : HasNonuniqueExtremePointMidpoint (D := D)) :
    ¬ HasUniqueExtremeMidpointRepresentation (D := D) := by
  intro hUnique
  rcases h with ⟨f, g, one, half, hf, hg, hone, hhalf, hpairs, hmid⟩
  exact hpairs (hUnique f g one half hf hg hone hhalf hmid)

/-- The Urysohn construction gives two different equal-weight two-atomic
representations supported on standard extreme points. -/
theorem urysohn_extremePoint_midpoint_obstruction
    (A : EquilateralTriple D)
    (hdiam : ∀ x y : D, dist x y ≤ 1)
    (hext : RationalOnePointExtension D) :
    HasNonuniqueExtremePointMidpoint (D := D) := by
  exact hasNonuniqueExtremeMidpoint_iff_standard.mp
    (urysohn_extreme_midpoint_obstruction A hdiam hext)

/-- Starting from one point, rational finite extension already refutes
equal-weight two-atomic uniqueness on the standard extreme boundary. -/
theorem rational_urysohn_not_uniqueExtremeMidpointRepresentation
    (x₀ : D)
    (hdiam : ∀ x y : D, dist x y ≤ 1)
    (hext : RationalOnePointExtension D) :
    ¬ HasUniqueExtremeMidpointRepresentation (D := D) := by
  apply nonuniqueExtremePointMidpoint_not_uniqueRepresentation
  exact hasNonuniqueExtremeMidpoint_iff_standard.mp
    (rational_urysohn_core_obstruction x₀ hdiam hext)

end Katetov

end

end SabokSPrime
