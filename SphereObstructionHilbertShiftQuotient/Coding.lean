import Mathlib.Data.Fintype.EquivFin
import SphereObstructionHilbertShiftQuotient.SphereQuotient

set_option linter.style.header false
open scoped ENNReal

/-!
Finite mixed-radix coding into the one-dimensional shift quotient.

This file contains the finite-support coding interface used to pass from
higher-rank quotients to the bilateral-shift quotient.
-/

namespace SphereObstructionHilbertShiftQuotient

noncomputable section

private abbrev codingHigherRankL2Space (n : Nat) : Type :=
  ↥(lp (fun (_ : Fin n -> Int) => Real) 2)

private abbrev codingShiftL2Space : Type :=
  ↥(lp (fun (_ : Int) => Real) 2)

private noncomputable def defaultShiftL2Vector : codingShiftL2Space :=
  lp.single (E := fun (_ : Int) => Real) 2 0 1

private lemma defaultShiftL2Vector_norm :
    ‖defaultShiftL2Vector‖ = 1 := by
  simp [defaultShiftL2Vector]

private noncomputable def defaultShiftSphereVector : shiftHilbertSphere :=
  ⟨defaultShiftL2Vector, by
    rw [Metric.mem_sphere, dist_zero_right]
    exact defaultShiftL2Vector_norm⟩

private noncomputable def normalizedShiftL2Vector
    (f : codingShiftL2Space) (hf : f ≠ 0) : shiftHilbertSphere :=
  ⟨(‖f‖)⁻¹ • f, by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul]
    have hnorm : ‖f‖ ≠ 0 := norm_ne_zero_iff.mpr hf
    simp [hnorm]⟩

/-- A finitely supported representative in the higher-rank Hilbert sphere. -/
noncomputable def finitelySupportedHigherRankPoint (n : Nat) : Type :=
  Sigma fun x : higherRankHilbertSphere n =>
    {S : Finset (Fin n -> Int) //
      ∀ k : Fin n -> Int, k ∉ S -> ((x : codingHigherRankL2Space n) k) = 0}

/-- The higher-rank Hilbert-sphere representative carried by finitely supported data. -/
noncomputable def finitelySupportedHigherRankRepresentative
    (n : Nat) : finitelySupportedHigherRankPoint n -> higherRankHilbertSphere n :=
  fun x => x.1

/-- The quotient point represented by a finitely supported higher-rank vector. -/
noncomputable def finitelySupportedToHigherRankQuotient
    (n : Nat) : finitelySupportedHigherRankPoint n -> higherRankSphereQuotient n := by
  exact fun x => higherRankQuotientMk n (finitelySupportedHigherRankRepresentative n x)

/--
The assertion that all support differences relevant to a finite family of finitely supported
higher-rank data lie in the coordinate box `[-L, L]^n`.
-/
def finiteSupportDifferenceBoxBound
    (n L : Nat) (F : Finset (finitelySupportedHigherRankPoint n)) : Prop :=
  ∀ x, x ∈ F -> ∀ y, y ∈ F -> ∀ k, k ∈ x.2.1 -> ∀ l, l ∈ y.2.1 ->
    ∀ i : Fin n, -(L : Int) <= k i - l i ∧ k i - l i <= (L : Int)

/-- The mixed-radix homomorphism from `Z^n` to `Z`. -/
def mixedRadixMap (n M : Nat) (k : Fin n -> Int) : Int :=
  Finset.univ.sum (fun i : Fin n => (M : Int) ^ (i : Nat) * k i)

private lemma mixedRadixMap_succ (n M : Nat) (k : Fin (n + 1) -> Int) :
    mixedRadixMap (n + 1) M k =
      k 0 + (M : Int) * mixedRadixMap n M (fun i => k i.succ) := by
  simp [mixedRadixMap, Fin.sum_univ_succ, Finset.mul_sum, pow_succ, mul_left_comm,
    mul_comm]

private lemma int_sub_abs_lt_base_of_box {M L : Nat} {a b : Int}
    (hM : 2 * L + 1 < M)
    (ha : -(L : Int) <= a ∧ a <= (L : Int))
    (hb : -(L : Int) <= b ∧ b <= (L : Int)) :
    |a - b| < (M : Int) := by
  have hLM : (2 * (L : Int)) < (M : Int) := by
    have hnat : 2 * L < M := Nat.lt_trans (by omega) hM
    exact_mod_cast hnat
  rw [abs_lt]
  constructor <;> linarith

private lemma mixedRadixMap_head_eq_of_eq (n M L : Nat) (hM : 2 * L + 1 < M)
    {k l : Fin (n + 1) -> Int}
    (hk : forall i : Fin (n + 1), -(L : Int) <= k i ∧ k i <= (L : Int))
    (hl : forall i : Fin (n + 1), -(L : Int) <= l i ∧ l i <= (L : Int))
    (h : mixedRadixMap (n + 1) M k = mixedRadixMap (n + 1) M l) :
    k 0 = l 0 := by
  have hstep := h
  rw [mixedRadixMap_succ, mixedRadixMap_succ] at hstep
  have hdvd : (M : Int) ∣ k 0 - l 0 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hZ := congrArg (fun z : Int => (z : ZMod M)) hstep
    simp at hZ
    simpa [Int.cast_sub] using sub_eq_zero.mpr hZ
  exact sub_eq_zero.mp
    (Int.eq_zero_of_abs_lt_dvd hdvd (int_sub_abs_lt_base_of_box hM (hk 0) (hl 0)))

private lemma mixedRadixMap_tail_eq_of_head_eq (n M L : Nat) (hM : 2 * L + 1 < M)
    {k l : Fin (n + 1) -> Int}
    (hhead : k 0 = l 0)
    (h : mixedRadixMap (n + 1) M k = mixedRadixMap (n + 1) M l) :
    mixedRadixMap n M (fun i => k i.succ) =
      mixedRadixMap n M (fun i => l i.succ) := by
  have hM_ne : (M : Int) ≠ 0 := by
    have hposNat : 0 < M := Nat.lt_trans (by omega) hM
    exact_mod_cast hposNat.ne'
  have hstep := h
  rw [mixedRadixMap_succ, mixedRadixMap_succ, hhead] at hstep
  have hmul : (M : Int) * mixedRadixMap n M (fun i => k i.succ) =
      (M : Int) * mixedRadixMap n M (fun i => l i.succ) := by
    exact add_left_cancel hstep
  exact mul_left_cancel₀ hM_ne hmul

private noncomputable def encodedShiftL2Vector
    (n M : Nat) (x : finitelySupportedHigherRankPoint n) : codingShiftL2Space :=
  ∑ k ∈ x.2.1, lp.single (E := fun (_ : Int) => Real) 2 (mixedRadixMap n M k)
    ((x.1 : codingHigherRankL2Space n) k)

/-- One-dimensional shift representative obtained by mixed-radix coding. -/
noncomputable def encodedShiftRepresentative
    (n M : Nat) : finitelySupportedHigherRankPoint n -> shiftHilbertSphere := by
  classical
  exact fun x =>
    let raw : codingShiftL2Space := encodedShiftL2Vector n M x
    if h : ‖raw‖ = 1 then
      ⟨raw, by
        rw [Metric.mem_sphere, dist_zero_right]
        exact h⟩
    else
      defaultShiftSphereVector

/-- The set of translated correlations between two shift representatives. -/
noncomputable def shiftCorrelationSet (f g : shiftHilbertSphere) : Set Real :=
  Set.range fun k : Int => shiftRepresentativeInner f (shiftAction k g)

/-- The set of translated correlations between finitely supported higher-rank representatives. -/
noncomputable def finitelySupportedHigherRankCorrelationSet
    (n : Nat) (x y : finitelySupportedHigherRankPoint n) : Set Real :=
  higherRankCorrelationSet n (finitelySupportedHigherRankRepresentative n x)
    (finitelySupportedHigherRankRepresentative n y)

/-- The mixed-radix map is injective on boxes of bounded differences. -/
theorem mixedRadixInjectiveOnDifferenceBox
    (n M L : Nat) (hM : 2 * L + 1 < M) :
    Set.InjOn (mixedRadixMap n M)
      {k : Fin n -> Int | forall i : Fin n, -(L : Int) <= k i /\ k i <= (L : Int)} := by
  induction n with
  | zero =>
      intro k _hk l _hl _h
      ext i
      exact i.elim0
  | succ n ih =>
      intro k hk l hl hmap
      have hhead : k 0 = l 0 :=
        mixedRadixMap_head_eq_of_eq n M L hM hk hl hmap
      have htailMap : mixedRadixMap n M (fun i : Fin n => k i.succ) =
          mixedRadixMap n M (fun i : Fin n => l i.succ) :=
        mixedRadixMap_tail_eq_of_head_eq n M L hM hhead hmap
      have htail : (fun i : Fin n => k i.succ) = (fun i : Fin n => l i.succ) := by
        exact ih (fun i => hk i.succ) (fun i => hl i.succ) htailMap
      ext i
      cases i using Fin.cases with
      | zero => exact hhead
      | succ i => exact congrFun htail i

private lemma mixedRadixMap_sub (n M : Nat) (k l : Fin n -> Int) :
    mixedRadixMap n M (k - l) = mixedRadixMap n M k - mixedRadixMap n M l := by
  simp [mixedRadixMap, sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    mul_add, mul_neg]

private lemma mixedRadixMap_add (n M : Nat) (k l : Fin n -> Int) :
    mixedRadixMap n M (k + l) = mixedRadixMap n M k + mixedRadixMap n M l := by
  simp [mixedRadixMap, Finset.sum_add_distrib, mul_add]

private lemma mixedRadixMap_zero (n M : Nat) :
    mixedRadixMap n M (0 : Fin n -> Int) = 0 := by
  simp [mixedRadixMap]

private noncomputable def shiftL2Vector (r : Int) (f : codingShiftL2Space) :
    codingShiftL2Space :=
  ⟨fun t => f (t - r), by
    change Memℓp (fun t : Int => f ((Equiv.subRight r) t)) (2 : ℝ≥0∞)
    have hpos : 0 < (2 : ℝ≥0∞).toReal := by norm_num
    rw [memℓp_gen_iff hpos]
    have hf : Summable fun t : Int => ‖f t‖ ^ (2 : ℝ≥0∞).toReal :=
      (lp.memℓp f).summable hpos
    simpa [Function.comp_def] using
      (Equiv.subRight r).summable_iff
        (f := fun t : Int => ‖f t‖ ^ (2 : ℝ≥0∞).toReal) |>.mpr hf⟩

private lemma shiftL2Vector_single (r j : Int) (b : Real) :
    shiftL2Vector r (lp.single (E := fun (_ : Int) => Real) 2 j b) =
      lp.single (E := fun (_ : Int) => Real) 2 (j + r) b := by
  ext t
  by_cases h : t = j + r
  · subst h
    have hsub : j + r - r = j := by omega
    simp only [shiftL2Vector, lp.coeFn_single]
    rw [hsub]
    simp
  · have hne : t - r ≠ j := by omega
    simp [shiftL2Vector, h, hne]

private lemma shiftL2Vector_encoded
    (n M : Nat) (x : finitelySupportedHigherRankPoint n) (r : Int) :
    shiftL2Vector r (encodedShiftL2Vector n M x) =
      ∑ k ∈ x.2.1, lp.single (E := fun (_ : Int) => Real) 2
        (mixedRadixMap n M k + r) ((x.1 : codingHigherRankL2Space n) k) := by
  ext t
  simp only [shiftL2Vector, encodedShiftL2Vector, lp.coeFn_sum, lp.coeFn_single,
    Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k _hk
  by_cases h : t = mixedRadixMap n M k + r
  · subst h
    have hsub : mixedRadixMap n M k + r - r = mixedRadixMap n M k := by omega
    rw [hsub]
    simp
  · have hne : t - r ≠ mixedRadixMap n M k := by omega
    simp [h, hne]

private lemma finitelySupportedHigherRank_l2_eq_sum_single
    (n : Nat) (x : finitelySupportedHigherRankPoint n) :
    (x.1 : codingHigherRankL2Space n) =
      ∑ k ∈ x.2.1, lp.single (E := fun (_ : Fin n -> Int) => Real) 2 k
        ((x.1 : codingHigherRankL2Space n) k) := by
  ext k
  simp only [lp.coeFn_sum, lp.coeFn_single, Finset.sum_apply]
  by_cases hk : k ∈ x.2.1
  · rw [Finset.sum_eq_single k]
    · simp
    · intro i hi hik
      have hne : i ≠ k := hik
      simp [hne]
    · intro hnot
      exact (hnot hk).elim
  · have hxk : ((x.1 : codingHigherRankL2Space n) k) = 0 := x.2.2 k hk
    rw [hxk, Finset.sum_eq_zero]
    intro i hi
    have hne : i ≠ k := by
      intro hik
      exact hk (hik ▸ hi)
    simp [hne]

private lemma encodedShiftL2Vector_apply
    (n M : Nat) (x : finitelySupportedHigherRankPoint n) (r : Int) :
    (encodedShiftL2Vector n M x : Int -> Real) r =
      ∑ k ∈ x.2.1,
        if mixedRadixMap n M k = r then ((x.1 : codingHigherRankL2Space n) k) else 0 := by
  simp only [encodedShiftL2Vector, lp.coeFn_sum, lp.coeFn_single, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k _hk
  by_cases h : mixedRadixMap n M k = r
  · rw [← h]
    simp
  · simp [h]

private lemma lp_inner_single_single {ι : Type*} [DecidableEq ι]
    (i j : ι) (a b : Real) :
    inner Real (lp.single (E := fun (_ : ι) => Real) 2 i a)
      (lp.single (E := fun (_ : ι) => Real) 2 j b) =
      if i = j then a * b else 0 := by
  rw [lp.inner_eq_tsum]
  by_cases h : i = j
  · subst h
    rw [tsum_eq_single i]
    · simp [lp.single_apply]
      ring
    · intro k hk
      simp [lp.single_apply, hk]
  · rw [if_neg h]
    trans ∑' _k : ι, (0 : Real)
    · apply tsum_congr
      intro k
      by_cases hki : k = i
      · have hkj : k ≠ j := by
          intro hkj
          exact h (hki.symm.trans hkj)
        simp [lp.single_apply, hki, h]
      · simp [lp.single_apply, Pi.single_apply, hki]
    · simp

private noncomputable def higherRankShiftL2Vector
    (n : Nat) (a : Fin n -> Int) (f : codingHigherRankL2Space n) :
    codingHigherRankL2Space n :=
  ⟨fun k => f (k - a), by
    change Memℓp (fun k : Fin n -> Int => f ((Equiv.subRight a) k)) (2 : ℝ≥0∞)
    have hpos : 0 < (2 : ℝ≥0∞).toReal := by norm_num
    rw [memℓp_gen_iff hpos]
    have hf : Summable fun k : Fin n -> Int => ‖f k‖ ^ (2 : ℝ≥0∞).toReal :=
      (lp.memℓp f).summable hpos
    simpa [Function.comp_def] using
      (Equiv.subRight a).summable_iff
        (f := fun k : Fin n -> Int => ‖f k‖ ^ (2 : ℝ≥0∞).toReal) |>.mpr hf⟩

private lemma higherRankShiftL2Vector_single
    (n : Nat) (a j : Fin n -> Int) (b : Real) :
    higherRankShiftL2Vector n a
        (lp.single (E := fun (_ : Fin n -> Int) => Real) 2 j b) =
      lp.single (E := fun (_ : Fin n -> Int) => Real) 2 (j + a) b := by
  ext k
  by_cases h : k = j + a
  · subst h
    have hsub : j + a - a = j := by ext i; simp
    simp only [higherRankShiftL2Vector, lp.coeFn_single]
    rw [hsub]
    simp
  · have hne : k - a ≠ j := by
      intro hka
      apply h
      ext i
      have := congrFun hka i
      simp only [Pi.sub_apply] at this
      simp only [Pi.add_apply]
      linarith
    simp [higherRankShiftL2Vector, h, hne]

private lemma higherRankShiftL2Vector_finitelySupported
    (n : Nat) (a : Fin n -> Int) (x : finitelySupportedHigherRankPoint n) :
    higherRankShiftL2Vector n a (x.1 : codingHigherRankL2Space n) =
      ∑ k ∈ x.2.1, lp.single (E := fun (_ : Fin n -> Int) => Real) 2 (k + a)
        ((x.1 : codingHigherRankL2Space n) k) := by
  let v : codingHigherRankL2Space n :=
    ∑ k ∈ x.2.1, lp.single (E := fun (_ : Fin n -> Int) => Real) 2 k
      ((x.1 : codingHigherRankL2Space n) k)
  have hxv : (x.1 : codingHigherRankL2Space n) = v :=
    finitelySupportedHigherRank_l2_eq_sum_single n x
  calc
    higherRankShiftL2Vector n a (x.1 : codingHigherRankL2Space n) =
        higherRankShiftL2Vector n a v := by rw [hxv]
    _ = ∑ k ∈ x.2.1, lp.single (E := fun (_ : Fin n -> Int) => Real) 2 (k + a)
        ((x.1 : codingHigherRankL2Space n) k) := by
      ext t
      simp only [v, higherRankShiftL2Vector, lp.coeFn_sum, lp.coeFn_single,
        Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro k _hk
      by_cases h : t = k + a
      · subst h
        have hsub : k + a - a = k := by ext i; simp
        rw [hsub]
        simp
      · have hne : t - a ≠ k := by
          intro hta
          apply h
          ext i
          have := congrFun hta i
          simp only [Pi.sub_apply] at this
          simp only [Pi.add_apply]
          linarith
        simp [h, hne]

private lemma higherRankTranslation_l2_eq_shiftL2
    (n : Nat) (a : Fin n -> Int) (x : higherRankHilbertSphere n) :
    (higherRankTranslation n a x : codingHigherRankL2Space n) =
      higherRankShiftL2Vector n a (x : codingHigherRankL2Space n) := by
  rfl

private lemma encodedShiftL2_inner_shift_sum
    (n M : Nat) (x y : finitelySupportedHigherRankPoint n) (r : Int) :
    inner Real (encodedShiftL2Vector n M x) (shiftL2Vector r (encodedShiftL2Vector n M y)) =
      ∑ k ∈ x.2.1, ∑ l ∈ y.2.1,
        if mixedRadixMap n M k = mixedRadixMap n M l + r then
          ((x.1 : codingHigherRankL2Space n) k) * ((y.1 : codingHigherRankL2Space n) l)
        else
          0 := by
  rw [shiftL2Vector_encoded]
  simp [encodedShiftL2Vector, inner_sum, sum_inner]
  rw [Finset.sum_comm]
  simp [lp_inner_single_single]

private lemma higherRank_inner_translation_sum
    (n : Nat) (x y : finitelySupportedHigherRankPoint n) (a : Fin n -> Int) :
    higherRankRepresentativeInner n x.1 (higherRankTranslation n a y.1) =
      ∑ k ∈ x.2.1, ∑ l ∈ y.2.1,
        if k = l + a then
          ((x.1 : codingHigherRankL2Space n) k) * ((y.1 : codingHigherRankL2Space n) l)
        else
          0 := by
  let vx : codingHigherRankL2Space n :=
    ∑ k ∈ x.2.1, lp.single (E := fun (_ : Fin n -> Int) => Real) 2 k
      ((x.1 : codingHigherRankL2Space n) k)
  let vy : codingHigherRankL2Space n :=
    ∑ l ∈ y.2.1, lp.single (E := fun (_ : Fin n -> Int) => Real) 2 (l + a)
      ((y.1 : codingHigherRankL2Space n) l)
  have hxv : (x.1 : codingHigherRankL2Space n) = vx :=
    finitelySupportedHigherRank_l2_eq_sum_single n x
  have hyv :
      (higherRankTranslation n a y.1 : codingHigherRankL2Space n) = vy := by
    rw [higherRankTranslation_l2_eq_shiftL2]
    exact higherRankShiftL2Vector_finitelySupported n a y
  calc
    higherRankRepresentativeInner n x.1 (higherRankTranslation n a y.1) =
        inner Real (x.1 : codingHigherRankL2Space n)
          (higherRankTranslation n a y.1 : codingHigherRankL2Space n) := by
      rfl
    _ = inner Real vx vy := by rw [hxv, hyv]
    _ = ∑ k ∈ x.2.1, ∑ l ∈ y.2.1,
        if k = l + a then
          ((x.1 : codingHigherRankL2Space n) k) * ((y.1 : codingHigherRankL2Space n) l)
        else
          0 := by
      simp [vx, vy, inner_sum, sum_inner]
      rw [Finset.sum_comm]
      simp [lp_inner_single_single]

private def boundedByBox (n L : Nat) (a : Fin n -> Int) : Prop :=
  ∀ i : Fin n, -(L : Int) <= a i ∧ a i <= (L : Int)

private lemma add_eq_of_sub_eq {n : Nat} {k l a : Fin n -> Int} (h : k - l = a) :
    k = l + a := by
  ext i
  have hi := congrFun h i
  simp only [Pi.sub_apply, Pi.add_apply] at hi ⊢
  linarith

private lemma sub_eq_of_add_eq {n : Nat} {k l a : Fin n -> Int} (h : k = l + a) :
    a = k - l := by
  ext i
  have hi := congrFun h i
  simp only [Pi.sub_apply, Pi.add_apply] at hi ⊢
  linarith

private lemma mixedRadix_condition_iff_add
    (n M L : Nat) (hM : 2 * L + 1 < M)
    {k l a : Fin n -> Int}
    (hkla : boundedByBox n L (k - l)) (ha : boundedByBox n L a) :
    mixedRadixMap n M k = mixedRadixMap n M l + mixedRadixMap n M a ↔ k = l + a := by
  constructor
  · intro hmap
    apply add_eq_of_sub_eq
    apply mixedRadixInjectiveOnDifferenceBox n M L hM hkla ha
    rw [mixedRadixMap_sub, hmap]
    ring
  · intro h
    rw [h, mixedRadixMap_add]

private lemma encodedShiftL2_inner_eq_higherRank_inner_of_box
    (n M L : Nat) (F : Finset (finitelySupportedHigherRankPoint n))
    (hM : 2 * L + 1 < M) (hF : finiteSupportDifferenceBoxBound n L F)
    {x y : finitelySupportedHigherRankPoint n} (hx : x ∈ F) (hy : y ∈ F)
    {a : Fin n -> Int} (ha : boundedByBox n L a) :
    inner Real (encodedShiftL2Vector n M x)
        (shiftL2Vector (mixedRadixMap n M a) (encodedShiftL2Vector n M y)) =
      higherRankRepresentativeInner n x.1 (higherRankTranslation n a y.1) := by
  rw [encodedShiftL2_inner_shift_sum, higherRank_inner_translation_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  have hkla : boundedByBox n L (k - l) := hF x hx y hy k hk l hl
  have hiff := mixedRadix_condition_iff_add n M L hM hkla ha
  by_cases hcond :
      mixedRadixMap n M k = mixedRadixMap n M l + mixedRadixMap n M a
  · have hka : k = l + a := hiff.mp hcond
    simp [hka, mixedRadixMap_add]
  · have hka : k ≠ l + a := fun hka => hcond (hiff.mpr hka)
    simp [hcond, hka]

private lemma encodedShiftL2Vector_norm_one
    (n M L : Nat) (F : Finset (finitelySupportedHigherRankPoint n))
    (hM : 2 * L + 1 < M) (hF : finiteSupportDifferenceBoxBound n L F)
    {x : finitelySupportedHigherRankPoint n} (hx : x ∈ F) :
    ‖encodedShiftL2Vector n M x‖ = 1 := by
  let raw := encodedShiftL2Vector n M x
  have hzeroBox : boundedByBox n L (0 : Fin n -> Int) := by
    intro i
    constructor
    · exact neg_nonpos.mpr (Int.natCast_nonneg L)
    · exact Int.natCast_nonneg L
  have hinner :=
    encodedShiftL2_inner_eq_higherRank_inner_of_box n M L F hM hF hx hx hzeroBox
  have hshift0 : shiftL2Vector (mixedRadixMap n M (0 : Fin n -> Int)) raw = raw := by
    rw [mixedRadixMap_zero]
    ext r
    simp [shiftL2Vector, raw]
  have htrans0 : higherRankTranslation n (0 : Fin n -> Int) x.1 = x.1 := by
    ext k
    change ((x.1 : codingHigherRankL2Space n) (k - (0 : Fin n -> Int))) =
      ((x.1 : codingHigherRankL2Space n) k)
    simp
  have hxnorm : ‖(x.1 : codingHigherRankL2Space n)‖ = 1 := by
    rw [← dist_zero_right (x.1 : codingHigherRankL2Space n)]
    exact x.1.2
  have hsquare : ‖raw‖ ^ 2 = 1 := by
    calc
      ‖raw‖ ^ 2 = inner Real raw raw := by rw [real_inner_self_eq_norm_sq]
      _ = inner Real raw (shiftL2Vector (mixedRadixMap n M (0 : Fin n -> Int)) raw) := by
        rw [hshift0]
      _ = higherRankRepresentativeInner n x.1 (higherRankTranslation n (0 : Fin n -> Int) x.1) := by
        exact hinner
      _ = 1 := by
        rw [htrans0]
        simp [higherRankRepresentativeInner, hxnorm]
  have hnonneg : 0 <= ‖raw‖ := norm_nonneg raw
  nlinarith

private lemma encodedShiftRepresentative_l2_eq_raw
    (n M L : Nat) (F : Finset (finitelySupportedHigherRankPoint n))
    (hM : 2 * L + 1 < M) (hF : finiteSupportDifferenceBoxBound n L F)
    {x : finitelySupportedHigherRankPoint n} (hx : x ∈ F) :
    (encodedShiftRepresentative n M x : codingShiftL2Space) = encodedShiftL2Vector n M x := by
  have hnorm := encodedShiftL2Vector_norm_one n M L F hM hF hx
  simp [encodedShiftRepresentative, hnorm]

private lemma shiftAction_encoded_l2_eq_shiftL2
    (n M L : Nat) (F : Finset (finitelySupportedHigherRankPoint n))
    (hM : 2 * L + 1 < M) (hF : finiteSupportDifferenceBoxBound n L F)
    {x : finitelySupportedHigherRankPoint n} (hx : x ∈ F) (r : Int) :
    (shiftAction r (encodedShiftRepresentative n M x) : codingShiftL2Space) =
      shiftL2Vector r (encodedShiftL2Vector n M x) := by
  ext t
  change ((encodedShiftRepresentative n M x : codingShiftL2Space) (t - r)) =
    (encodedShiftL2Vector n M x : codingShiftL2Space) (t - r)
  rw [encodedShiftRepresentative_l2_eq_raw n M L F hM hF hx]

private lemma shiftRepresentativeInner_encoded_eq_raw
    (n M L : Nat) (F : Finset (finitelySupportedHigherRankPoint n))
    (hM : 2 * L + 1 < M) (hF : finiteSupportDifferenceBoxBound n L F)
    {x y : finitelySupportedHigherRankPoint n} (hx : x ∈ F) (hy : y ∈ F) (r : Int) :
    shiftRepresentativeInner (encodedShiftRepresentative n M x)
        (shiftAction r (encodedShiftRepresentative n M y)) =
      inner Real (encodedShiftL2Vector n M x)
        (shiftL2Vector r (encodedShiftL2Vector n M y)) := by
  rw [shiftRepresentativeInner]
  rw [encodedShiftRepresentative_l2_eq_raw n M L F hM hF hx,
    shiftAction_encoded_l2_eq_shiftL2 n M L F hM hF hy r]

private lemma shiftRepresentativeInner_encoded_mixedRadix_eq_higherRank
    (n M L : Nat) (F : Finset (finitelySupportedHigherRankPoint n))
    (hM : 2 * L + 1 < M) (hF : finiteSupportDifferenceBoxBound n L F)
    {x y : finitelySupportedHigherRankPoint n} (hx : x ∈ F) (hy : y ∈ F)
    {a : Fin n -> Int} (ha : boundedByBox n L a) :
    shiftRepresentativeInner (encodedShiftRepresentative n M x)
        (shiftAction (mixedRadixMap n M a) (encodedShiftRepresentative n M y)) =
      higherRankRepresentativeInner n x.1 (higherRankTranslation n a y.1) := by
  rw [shiftRepresentativeInner_encoded_eq_raw n M L F hM hF hx hy]
  exact encodedShiftL2_inner_eq_higherRank_inner_of_box n M L F hM hF hx hy ha

private def encodedShiftDifferenceFinset
    (n M : Nat) (x y : finitelySupportedHigherRankPoint n) : Finset Int :=
  x.2.1.biUnion fun k =>
    y.2.1.image fun l => mixedRadixMap n M k - mixedRadixMap n M l

private lemma mem_encodedShiftDifferenceFinset
    (n M : Nat) (x y : finitelySupportedHigherRankPoint n)
    {k l : Fin n -> Int} (hk : k ∈ x.2.1) (hl : l ∈ y.2.1) :
    mixedRadixMap n M k - mixedRadixMap n M l ∈ encodedShiftDifferenceFinset n M x y := by
  classical
  simp [encodedShiftDifferenceFinset]
  exact ⟨k, hk, l, hl, rfl⟩

private lemma shiftRepresentativeInner_encoded_eq_zero_of_not_mem
    (n M L : Nat) (F : Finset (finitelySupportedHigherRankPoint n))
    (hM : 2 * L + 1 < M) (hF : finiteSupportDifferenceBoxBound n L F)
    {x y : finitelySupportedHigherRankPoint n} (hx : x ∈ F) (hy : y ∈ F)
    {r : Int} (hr : r ∉ encodedShiftDifferenceFinset n M x y) :
    shiftRepresentativeInner (encodedShiftRepresentative n M x)
        (shiftAction r (encodedShiftRepresentative n M y)) = 0 := by
  rw [shiftRepresentativeInner_encoded_eq_raw n M L F hM hF hx hy,
    encodedShiftL2_inner_shift_sum]
  apply Finset.sum_eq_zero
  intro k hk
  apply Finset.sum_eq_zero
  intro l hl
  by_cases hcond : mixedRadixMap n M k = mixedRadixMap n M l + r
  · have hr_eq : r = mixedRadixMap n M k - mixedRadixMap n M l := by linarith
    have hmem := mem_encodedShiftDifferenceFinset n M x y hk hl
    exact (hr (hr_eq.symm ▸ hmem)).elim
  · simp [hcond]

private lemma higherRankRepresentativeInner_eq_zero_of_no_difference
    (n : Nat) (x y : finitelySupportedHigherRankPoint n) (a : Fin n -> Int)
    (hno : ¬ ∃ k, k ∈ x.2.1 ∧ ∃ l, l ∈ y.2.1 ∧ a = k - l) :
    higherRankRepresentativeInner n x.1 (higherRankTranslation n a y.1) = 0 := by
  rw [higherRank_inner_translation_sum]
  apply Finset.sum_eq_zero
  intro k hk
  apply Finset.sum_eq_zero
  intro l hl
  by_cases hcond : k = l + a
  · have ha : a = k - l := sub_eq_of_add_eq hcond
    exact (hno ⟨k, hk, l, hl, ha⟩).elim
  · simp [hcond]

private def farHigherRankShift (n L : Nat) (hn : 0 < n) : Fin n -> Int :=
  fun i => if i = ⟨0, hn⟩ then (L : Int) + 1 else 0

private lemma farHigherRankShift_no_difference
    (n L : Nat) (hn : 0 < n) (F : Finset (finitelySupportedHigherRankPoint n))
    (hF : finiteSupportDifferenceBoxBound n L F)
    {x y : finitelySupportedHigherRankPoint n} (hx : x ∈ F) (hy : y ∈ F) :
    ¬ ∃ k, k ∈ x.2.1 ∧ ∃ l, l ∈ y.2.1 ∧ farHigherRankShift n L hn = k - l := by
  intro h
  rcases h with ⟨k, hk, l, hl, ha⟩
  let i0 : Fin n := ⟨0, hn⟩
  have hcoord := congrFun ha i0
  have hbound := hF x hx y hy k hk l hl i0
  simp [farHigherRankShift, i0] at hcoord
  linarith

/-- Exact coding preserves the finite set of correlations for finitely supported data. -/
theorem codingPreservesCorrelations
    (n M L : Nat) (F : Finset (finitelySupportedHigherRankPoint n))
    (hn : 0 < n) (hM : 2 * L + 1 < M)
    (hF : finiteSupportDifferenceBoxBound n L F) :
    (letI : PseudoMetricSpace (higherRankSphereQuotient n) := higherRankChordalMetric n;
      letI : PseudoMetricSpace shiftSphereQuotient := shiftChordalMetric;
      (forall x, x ∈ F -> forall y, y ∈ F ->
        shiftCorrelationSet (encodedShiftRepresentative n M x)
            (encodedShiftRepresentative n M y) =
          finitelySupportedHigherRankCorrelationSet n x y) /\
        forall x, x ∈ F -> forall y, y ∈ F ->
          dist (shiftQuotientMk (encodedShiftRepresentative n M x))
              (shiftQuotientMk (encodedShiftRepresentative n M y)) =
            dist (finitelySupportedToHigherRankQuotient n x)
              (finitelySupportedToHigherRankQuotient n y)) := by
  classical
  letI : PseudoMetricSpace (higherRankSphereQuotient n) := higherRankChordalMetric n
  letI : PseudoMetricSpace shiftSphereQuotient := shiftChordalMetric
  let corrEq :
      ∀ x, x ∈ F -> ∀ y, y ∈ F ->
        shiftCorrelationSet (encodedShiftRepresentative n M x)
            (encodedShiftRepresentative n M y) =
          finitelySupportedHigherRankCorrelationSet n x y := by
    intro x hx y hy
    ext z
    constructor
    · rintro ⟨r, rfl⟩
      by_cases hr : r ∈ encodedShiftDifferenceFinset n M x y
      · simp [encodedShiftDifferenceFinset] at hr
        rcases hr with ⟨k, hk, l, hl, hrl⟩
        let a : Fin n -> Int := k - l
        have ha : boundedByBox n L a := hF x hx y hy k hk l hl
        have hrphi : r = mixedRadixMap n M a := by
          dsimp [a]
          rw [mixedRadixMap_sub]
          exact hrl.symm
        refine ⟨a, ?_⟩
        rw [hrphi]
        change higherRankRepresentativeInner n x.1 (higherRankTranslation n a y.1) =
          shiftRepresentativeInner (encodedShiftRepresentative n M x)
            (shiftAction (mixedRadixMap n M a) (encodedShiftRepresentative n M y))
        exact (shiftRepresentativeInner_encoded_mixedRadix_eq_higherRank
          n M L F hM hF hx hy ha).symm
      · let aFar := farHigherRankShift n L hn
        refine ⟨aFar, ?_⟩
        change higherRankRepresentativeInner n x.1 (higherRankTranslation n aFar y.1) =
          shiftRepresentativeInner (encodedShiftRepresentative n M x)
            (shiftAction r (encodedShiftRepresentative n M y))
        rw [higherRankRepresentativeInner_eq_zero_of_no_difference n x y aFar
          (farHigherRankShift_no_difference n L hn F hF hx hy)]
        rw [shiftRepresentativeInner_encoded_eq_zero_of_not_mem n M L F hM hF hx hy hr]
    · rintro ⟨a, rfl⟩
      by_cases haDiff : ∃ k, k ∈ x.2.1 ∧ ∃ l, l ∈ y.2.1 ∧ a = k - l
      · rcases haDiff with ⟨k, hk, l, hl, haeq⟩
        have ha : boundedByBox n L a := by
          rw [haeq]
          exact hF x hx y hy k hk l hl
        refine ⟨mixedRadixMap n M a, ?_⟩
        change shiftRepresentativeInner (encodedShiftRepresentative n M x)
            (shiftAction (mixedRadixMap n M a) (encodedShiftRepresentative n M y)) =
          higherRankRepresentativeInner n x.1 (higherRankTranslation n a y.1)
        exact shiftRepresentativeInner_encoded_mixedRadix_eq_higherRank
          n M L F hM hF hx hy ha
      · obtain ⟨rFar, hrFar⟩ :=
          Infinite.exists_notMem_finset (α := Int) (encodedShiftDifferenceFinset n M x y)
        refine ⟨rFar, ?_⟩
        change shiftRepresentativeInner (encodedShiftRepresentative n M x)
            (shiftAction rFar (encodedShiftRepresentative n M y)) =
          higherRankRepresentativeInner n x.1 (higherRankTranslation n a y.1)
        rw [shiftRepresentativeInner_encoded_eq_zero_of_not_mem n M L F hM hF hx hy hrFar]
        exact (higherRankRepresentativeInner_eq_zero_of_no_difference n x y a haDiff).symm
  refine ⟨corrEq, ?_⟩
  intro x hx y hy
  let sx := encodedShiftRepresentative n M x
  let sy := encodedShiftRepresentative n M y
  have hshiftSq :
      dist (shiftQuotientMk sx) (shiftQuotientMk sy) ^ 2 =
        2 - 2 * sSup (shiftCorrelationSet sx sy) := by
    simpa [sx, sy, shiftCorrelationSet] using shiftCorrelationFormula sx sy
  have hhighSq :
      dist (finitelySupportedToHigherRankQuotient n x)
          (finitelySupportedToHigherRankQuotient n y) ^ 2 =
        2 - 2 * sSup (finitelySupportedHigherRankCorrelationSet n x y) := by
    simpa [finitelySupportedToHigherRankQuotient, finitelySupportedHigherRankCorrelationSet,
      finitelySupportedHigherRankRepresentative, higherRankCorrelationSupFromRepresentatives]
      using higherRankCorrelationFormula n x.1 y.1
  have hsquares :
      dist (shiftQuotientMk sx) (shiftQuotientMk sy) ^ 2 =
        dist (finitelySupportedToHigherRankQuotient n x)
          (finitelySupportedToHigherRankQuotient n y) ^ 2 := by
    rw [hshiftSq, hhighSq, corrEq x hx y hy]
  have hshift_nonneg : 0 <= dist (shiftQuotientMk sx) (shiftQuotientMk sy) := dist_nonneg
  have hhigh_nonneg :
      0 <= dist (finitelySupportedToHigherRankQuotient n x)
        (finitelySupportedToHigherRankQuotient n y) := dist_nonneg
  have habs := (sq_eq_sq_iff_abs_eq_abs
    (dist (shiftQuotientMk sx) (shiftQuotientMk sy))
    (dist (finitelySupportedToHigherRankQuotient n x)
      (finitelySupportedToHigherRankQuotient n y))).mp hsquares
  simpa [sx, sy, abs_of_nonneg hshift_nonneg, abs_of_nonneg hhigh_nonneg] using habs

private lemma higherRankShiftL2Vector_norm
    (n : Nat) (a : Fin n -> Int) (f : codingHigherRankL2Space n) :
    ‖higherRankShiftL2Vector n a f‖ = ‖f‖ := by
  have hpos : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  apply Real.rpow_left_injOn hpos.ne' (lp.norm_nonneg' _) (lp.norm_nonneg' _)
  change ‖higherRankShiftL2Vector n a f‖ ^ (2 : ℝ≥0∞).toReal =
    ‖f‖ ^ (2 : ℝ≥0∞).toReal
  rw [lp.norm_rpow_eq_tsum hpos, lp.norm_rpow_eq_tsum hpos]
  change (∑' k : Fin n -> Int, ‖f (k - a)‖ ^ (2 : ℝ≥0∞).toReal) =
    ∑' k : Fin n -> Int, ‖f k‖ ^ (2 : ℝ≥0∞).toReal
  exact (Equiv.subRight a).tsum_eq
    (fun k : Fin n -> Int => ‖f k‖ ^ (2 : ℝ≥0∞).toReal)

private lemma higherRankShiftL2Vector_sub
    (n : Nat) (a : Fin n -> Int) (f g : codingHigherRankL2Space n) :
    higherRankShiftL2Vector n a (f - g) =
      higherRankShiftL2Vector n a f - higherRankShiftL2Vector n a g := by
  ext k
  rfl

private lemma higherRankTranslation_dist_eq
    (n : Nat) (a : Fin n -> Int) (x y : higherRankHilbertSphere n) :
    dist (higherRankTranslation n a x) (higherRankTranslation n a y) = dist x y := by
  rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
  rw [higherRankTranslation_l2_eq_shiftL2, higherRankTranslation_l2_eq_shiftL2,
    ← higherRankShiftL2Vector_sub, higherRankShiftL2Vector_norm]

private lemma higherRankTranslation_add_eq
    (n : Nat) (a b : Fin n -> Int) (x : higherRankHilbertSphere n) :
    higherRankTranslation n a (higherRankTranslation n b x) =
      higherRankTranslation n (a + b) x := by
  ext k
  change ((x : codingHigherRankL2Space n) (k - a - b)) =
    ((x : codingHigherRankL2Space n) (k - (a + b)))
  have harg : k - a - b = k - (a + b) := by
    ext i
    simp only [Pi.sub_apply, Pi.add_apply]
    omega
  rw [harg]

private lemma higherRankQuotientMk_dist_le_representativeNorm
    (n : Nat) (x y : higherRankHilbertSphere n) :
    (letI : PseudoMetricSpace (higherRankSphereQuotient n) := higherRankChordalMetric n;
      dist (higherRankQuotientMk n x) (higherRankQuotientMk n y) <=
        higherRankRepresentativeNorm n x y) := by
  letI : PseudoMetricSpace (higherRankSphereQuotient n) := higherRankChordalMetric n
  obtain ⟨p, hx⟩ := Quotient.exact (Quotient.out_eq (higherRankQuotientMk n x))
  obtain ⟨q, hy⟩ := Quotient.exact (Quotient.out_eq (higherRankQuotientMk n y))
  change x = higherRankTranslation n p (Quotient.out (higherRankQuotientMk n x)) at hx
  change y = higherRankTranslation n q (Quotient.out (higherRankQuotientMk n y)) at hy
  let a : Fin n -> Int := q - p
  change ((⨅ b : Fin n -> Int, edist (Quotient.out (higherRankQuotientMk n x))
      (higherRankTranslation n b (Quotient.out (higherRankQuotientMk n y)))).toReal) <=
    higherRankRepresentativeNorm n x y
  have htoReal :
      ((⨅ b : Fin n -> Int, edist (Quotient.out (higherRankQuotientMk n x))
        (higherRankTranslation n b (Quotient.out (higherRankQuotientMk n y)))).toReal) <=
        dist (Quotient.out (higherRankQuotientMk n x))
          (higherRankTranslation n a (Quotient.out (higherRankQuotientMk n y))) := by
    refine le_trans (ENNReal.toReal_mono (edist_ne_top _ _)
      (iInf_le (fun b : Fin n -> Int => edist (Quotient.out (higherRankQuotientMk n x))
        (higherRankTranslation n b (Quotient.out (higherRankQuotientMk n y)))) a)) ?_
    rw [edist_dist, ENNReal.toReal_ofReal dist_nonneg]
  have hadd : p + a = q := by
    dsimp [a]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply]
    omega
  have hdist :
      dist (Quotient.out (higherRankQuotientMk n x))
          (higherRankTranslation n a (Quotient.out (higherRankQuotientMk n y))) =
        dist x y := by
    calc
      dist (Quotient.out (higherRankQuotientMk n x))
          (higherRankTranslation n a (Quotient.out (higherRankQuotientMk n y))) =
          dist (higherRankTranslation n p (Quotient.out (higherRankQuotientMk n x)))
            (higherRankTranslation n p
              (higherRankTranslation n a (Quotient.out (higherRankQuotientMk n y)))) := by
        rw [higherRankTranslation_dist_eq]
      _ = dist x y := by
        rw [higherRankTranslation_add_eq, hadd, ← hx, ← hy]
  have hdistNorm : dist x y = higherRankRepresentativeNorm n x y := by
    rw [Subtype.dist_eq, dist_eq_norm]
    rfl
  exact htoReal.trans_eq (hdist.trans hdistNorm)

/-- Quotient distance is Lipschitz under changing Hilbert-sphere representatives. -/
theorem quotientDistanceLipschitzRepresentatives
    (n : Nat) (x y x' y' : higherRankHilbertSphere n) :
    (letI : PseudoMetricSpace (higherRankSphereQuotient n) := higherRankChordalMetric n;
      |dist (higherRankQuotientMk n x) (higherRankQuotientMk n y) -
          dist (higherRankQuotientMk n x') (higherRankQuotientMk n y')| <=
        higherRankRepresentativeNorm n x x' + higherRankRepresentativeNorm n y y') := by
  letI : PseudoMetricSpace (higherRankSphereQuotient n) := higherRankChordalMetric n
  refine abs_sub_le_iff.mpr ⟨?_, ?_⟩
  · have htri := dist_triangle4_right (higherRankQuotientMk n x) (higherRankQuotientMk n y)
      (higherRankQuotientMk n x') (higherRankQuotientMk n y')
    have hxle := higherRankQuotientMk_dist_le_representativeNorm n x x'
    have hyle := higherRankQuotientMk_dist_le_representativeNorm n y y'
    linarith
  · have htri := dist_triangle4_right (higherRankQuotientMk n x') (higherRankQuotientMk n y')
      (higherRankQuotientMk n x) (higherRankQuotientMk n y)
    have hxle := higherRankQuotientMk_dist_le_representativeNorm n x' x
    have hyle := higherRankQuotientMk_dist_le_representativeNorm n y' y
    have hxnorm :
        higherRankRepresentativeNorm n x' x = higherRankRepresentativeNorm n x x' := by
      have hleft : dist x' x = higherRankRepresentativeNorm n x' x := by
        rw [Subtype.dist_eq, dist_eq_norm]
        rfl
      have hright : dist x x' = higherRankRepresentativeNorm n x x' := by
        rw [Subtype.dist_eq, dist_eq_norm]
        rfl
      rw [← hleft, ← hright, dist_comm]
    have hynorm :
        higherRankRepresentativeNorm n y' y = higherRankRepresentativeNorm n y y' := by
      have hleft : dist y' y = higherRankRepresentativeNorm n y' y := by
        rw [Subtype.dist_eq, dist_eq_norm]
        rfl
      have hright : dist y y' = higherRankRepresentativeNorm n y y' := by
        rw [Subtype.dist_eq, dist_eq_norm]
        rfl
      rw [← hleft, ← hright, dist_comm]
    rw [hxnorm] at hxle
    rw [hynorm] at hyle
    linarith

private lemma norm_sub_normalized_lt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {x v : E} {η δ : Real} (hxnorm : ‖x‖ = 1)
    (hη1 : η < 1) (hηδ : 2 * η < δ) (hvclose : dist v x < η) :
    ‖x - (‖v‖)⁻¹ • v‖ < δ := by
  have hv_ne : v ≠ 0 := by
    intro hv0
    have hdist : dist v x = 1 := by
      rw [hv0, dist_zero_left, hxnorm]
    linarith
  have hvnorm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne
  have hdist_vw : dist v ((‖v‖)⁻¹ • v) = |‖v‖ - 1| := by
    rw [dist_eq_norm]
    have hsub : v - (‖v‖)⁻¹ • v = (1 - (‖v‖)⁻¹) • v := by
      rw [sub_smul, one_smul]
    rw [hsub, norm_smul]
    have habs : ‖(1 : Real) - (‖v‖)⁻¹‖ * ‖v‖ = |‖v‖ - 1| := by
      rw [Real.norm_eq_abs]
      calc
        |(1 : Real) - (‖v‖)⁻¹| * ‖v‖ =
            |(1 : Real) - (‖v‖)⁻¹| * |(‖v‖ : Real)| := by
          rw [abs_of_pos hvnorm_pos]
        _ = |((1 : Real) - (‖v‖)⁻¹) * ‖v‖| := by
          exact (abs_mul ((1 : Real) - (‖v‖)⁻¹) (‖v‖ : Real)).symm
        _ = |‖v‖ - 1| := by
          field_simp [hvnorm_pos.ne']
    exact habs
  have hnormdiff : |‖v‖ - 1| ≤ ‖v - x‖ := by
    simpa [hxnorm] using abs_norm_sub_norm_le v x
  have hvx_lt : ‖v - x‖ < η := by
    simpa [dist_eq_norm] using hvclose
  have hvw_le : dist v ((‖v‖)⁻¹ • v) ≤ η := by
    rw [hdist_vw]
    exact hnormdiff.trans hvx_lt.le
  have hxv_lt : dist x v < η := by simpa [dist_comm] using hvclose
  have htri := dist_triangle x v ((‖v‖)⁻¹ • v)
  have hxw_lt : dist x ((‖v‖)⁻¹ • v) < δ := by
    nlinarith
  simpa [dist_eq_norm] using hxw_lt

private lemma exists_finitelySupportedHigherRankPoint_near
    (n : Nat) (x : higherRankHilbertSphere n) {δ : Real} (hδ : 0 < δ) :
    ∃ z : finitelySupportedHigherRankPoint n,
      higherRankRepresentativeNorm n x (finitelySupportedHigherRankRepresentative n z) < δ := by
  classical
  let η : Real := min (δ / 4) (1 / 4)
  have hηpos : 0 < η := by
    dsimp [η]
    positivity
  have hη1 : η < 1 := by
    have hη_le : η ≤ (1 / 4 : Real) := min_le_right _ _
    norm_num at hη_le ⊢
    linarith
  have hηδ : 2 * η < δ := by
    have hη_le : η ≤ δ / 4 := min_le_left _ _
    nlinarith
  let f : codingHigherRankL2Space n := x
  have hsum :
      HasSum
        (fun k : Fin n -> Int =>
          lp.single (E := fun (_ : Fin n -> Int) => Real) 2 k (f k))
        f := by
    exact lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) f
  have htend :
      Filter.Tendsto
        (fun s : Finset (Fin n -> Int) =>
          ∑ k ∈ s, lp.single (E := fun (_ : Fin n -> Int) => Real) 2 k (f k))
        Filter.atTop (nhds f) := hsum
  obtain ⟨s, hs⟩ :=
    Filter.eventually_atTop.1 ((Metric.tendsto_nhds.mp htend) η hηpos)
  let v : codingHigherRankL2Space n :=
    ∑ k ∈ s, lp.single (E := fun (_ : Fin n -> Int) => Real) 2 k (f k)
  have hvclose : dist v f < η := by
    simpa [v] using hs s le_rfl
  have hfnorm : ‖f‖ = 1 := by
    rw [← dist_zero_right (x : codingHigherRankL2Space n)]
    exact x.2
  have hv_ne : v ≠ 0 := by
    intro hv0
    have hdist : dist v f = 1 := by
      rw [hv0, dist_zero_left, hfnorm]
    linarith
  let wL2 : codingHigherRankL2Space n := (‖v‖)⁻¹ • v
  have hwL2norm : ‖wL2‖ = 1 := by
    have hvnorm_ne : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv_ne
    simp [wL2, norm_smul, hvnorm_ne]
  let w : higherRankHilbertSphere n :=
    ⟨wL2, by
      rw [Metric.mem_sphere, dist_zero_right]
      exact hwL2norm⟩
  have hsupp : ∀ k : Fin n -> Int, k ∉ s -> ((w : codingHigherRankL2Space n) k) = 0 := by
    intro k hk
    have hvk : (v : codingHigherRankL2Space n) k = 0 := by
      simp only [v, lp.coeFn_sum, lp.coeFn_single, Finset.sum_apply]
      apply Finset.sum_eq_zero
      intro i hi
      have hki : k ≠ i := by
        intro hki
        exact hk (hki ▸ hi)
      simp [hki]
    simp [w, wL2, hvk]
  refine ⟨⟨w, ⟨s, hsupp⟩⟩, ?_⟩
  change ‖(x : codingHigherRankL2Space n) - (w : codingHigherRankL2Space n)‖ < δ
  simpa [f, v, w, wL2] using norm_sub_normalized_lt hfnorm hη1 hηδ hvclose

private lemma higherRankQuotient_dist_eq_zero_iff
    (n : Nat) (x y : higherRankSphereQuotient n) :
    (letI : PseudoMetricSpace (higherRankSphereQuotient n) := higherRankChordalMetric n;
      dist x y = 0 ↔ x = y) := by
  letI : PseudoMetricSpace (higherRankSphereQuotient n) := higherRankChordalMetric n
  constructor
  · intro hdist
    let orbit : Set (higherRankHilbertSphere n) :=
      Set.range fun a : Fin n -> Int => higherRankTranslation n a (Quotient.out y)
    have horbit_nonempty : orbit.Nonempty := Set.range_nonempty _
    have hdist_inf :
        dist x y = Metric.infDist (Quotient.out x) orbit := by
      change ((⨅ i : Fin n -> Int,
        edist (Quotient.out x) (higherRankTranslation n i (Quotient.out y))).toReal) =
          Metric.infDist (Quotient.out x) orbit
      dsimp [Metric.infDist, Metric.infEDist, orbit]
      rw [iInf_range]
    have hinf_zero : Metric.infDist (Quotient.out x) orbit = 0 := by
      rwa [← hdist_inf]
    have hx_closure : Quotient.out x ∈ closure orbit :=
      (Metric.mem_closure_iff_infDist_zero horbit_nonempty).mpr hinf_zero
    have horbit_closed : IsClosed orbit := by
      simpa [orbit, higherRankOrbit] using higherRankTranslationOrbitsClosed n (Quotient.out y)
    have hx_mem : Quotient.out x ∈ orbit := by
      simpa [horbit_closed.closure_eq] using hx_closure
    rcases hx_mem with ⟨a, ha⟩
    have hquot :
        (⟦Quotient.out y⟧ : higherRankSphereQuotient n) =
          (⟦Quotient.out x⟧ : higherRankSphereQuotient n) := by
      apply Quotient.sound
      change ∃ a : Fin n -> Int, Quotient.out x = higherRankTranslation n a (Quotient.out y)
      exact ⟨a, ha.symm⟩
    exact (Quotient.out_eq x).symm.trans (hquot.symm.trans (Quotient.out_eq y))
  · intro hxy
    subst hxy
    simp

/-- Finite subsets of a higher-rank quotient may be approximated by finitely supported data. -/
theorem finiteSupportApproximationInQuotient
    (n : Nat) (F : Finset (higherRankSphereQuotient n)) (eps : Real) (heps : 0 < eps) :
    (letI : PseudoMetricSpace (higherRankSphereQuotient n) := higherRankChordalMetric n;
      exists G : Finset (higherRankSphereQuotient n),
        (forall y, y ∈ G ->
          exists z : finitelySupportedHigherRankPoint n,
            higherRankQuotientMk n (finitelySupportedHigherRankRepresentative n z) = y) /\
          FiniteMetricApproximation F G (1 + eps)) := by
  classical
  letI : PseudoMetricSpace (higherRankSphereQuotient n) := higherRankChordalMetric n
  let points := {x : higherRankSphereQuotient n // x ∈ F}
  let pairFinset : Finset (points × points) := Finset.univ.filter fun p => p.1 ≠ p.2
  by_cases hpairs : pairFinset.Nonempty
  · let distFinset : Finset Real := pairFinset.image fun p => dist p.1.1 p.2.1
    have hdistFinset_nonempty : distFinset.Nonempty := by
      rcases hpairs with ⟨p, hp⟩
      exact ⟨dist p.1.1 p.2.1, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
    let d0 : Real := distFinset.min' hdistFinset_nonempty
    have hd0_pos : 0 < d0 := by
      rcases Finset.mem_image.mp (Finset.min'_mem distFinset hdistFinset_nonempty) with
        ⟨p, hp, hpdist⟩
      have hp_ne : p.1 ≠ p.2 := by
        simpa [pairFinset] using hp
      have hp_val_ne : p.1.1 ≠ p.2.1 := by
        intro hval
        exact hp_ne (Subtype.ext hval)
      have hdist_ne : dist p.1.1 p.2.1 ≠ 0 := by
        intro hdist_zero
        exact hp_val_ne ((higherRankQuotient_dist_eq_zero_iff n p.1.1 p.2.1).mp hdist_zero)
      have hdist_pos : 0 < dist p.1.1 p.2.1 :=
        lt_of_le_of_ne dist_nonneg (Ne.symm hdist_ne)
      have hmin_pos : 0 < distFinset.min' hdistFinset_nonempty := by
        rwa [← hpdist]
      simpa [d0] using hmin_pos
    let a : Real := min (eps / 4) (1 / 4)
    have ha_pos : 0 < a := by
      dsimp [a]
      positivity
    have ha_nonneg : 0 ≤ a := ha_pos.le
    have ha_le_quarter : a ≤ (1 / 4 : Real) := by
      dsimp [a]
      exact min_le_right _ _
    have ha_lt_one : a < 1 := by
      nlinarith
    have hscale_pos : 0 < 1 - a := by
      nlinarith
    have ha_eps : a * (2 + eps) ≤ eps := by
      by_cases heps_le_one : eps ≤ 1
      · have ha_le_eps : a ≤ eps / 4 := by
          dsimp [a]
          exact min_le_left _ _
        nlinarith
      · have hone_le_eps : 1 ≤ eps := le_of_not_ge heps_le_one
        nlinarith
    have hfactor : 1 + a ≤ (1 + eps) * (1 - a) := by
      nlinarith
    let errorRadius : Real := a * d0
    have herror_pos : 0 < errorRadius := by
      dsimp [errorRadius]
      positivity
    let δ : Real := errorRadius / 4
    have hδpos : 0 < δ := by
      dsimp [δ]
      positivity
    let approxData : points -> finitelySupportedHigherRankPoint n := fun q =>
      Classical.choose (exists_finitelySupportedHigherRankPoint_near n (Quotient.out q.1) hδpos)
    let approxPoint : points -> higherRankSphereQuotient n := fun q =>
      higherRankQuotientMk n (finitelySupportedHigherRankRepresentative n (approxData q))
    let G : Finset (higherRankSphereQuotient n) := Finset.univ.image approxPoint
    refine ⟨G, ?_, ?_⟩
    · intro y hy
      rcases Finset.mem_image.mp hy with ⟨q, _hq, rfl⟩
      exact ⟨approxData q, rfl⟩
    · refine ⟨fun q => ⟨approxPoint q, ?_⟩, 1 - a, hscale_pos, ?_⟩
      · exact Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩
      · intro x y
        by_cases hxy : x = y
        · subst hxy
          simp [approxPoint]
        · have hpair_mem : (x, y) ∈ pairFinset := by
            simp [pairFinset, hxy]
          have hdist_mem : dist x.1 y.1 ∈ distFinset :=
            Finset.mem_image.mpr ⟨(x, y), hpair_mem, rfl⟩
          have hd0_le_dist : d0 ≤ dist x.1 y.1 := by
            simpa [d0] using Finset.min'_le distFinset (dist x.1 y.1) hdist_mem
          have herror_le : errorRadius ≤ a * dist x.1 y.1 := by
            dsimp [errorRadius]
            exact mul_le_mul_of_nonneg_left hd0_le_dist ha_nonneg
          have hxclose :=
            Classical.choose_spec
              (exists_finitelySupportedHigherRankPoint_near n (Quotient.out x.1) hδpos)
          have hyclose :=
            Classical.choose_spec
              (exists_finitelySupportedHigherRankPoint_near n (Quotient.out y.1) hδpos)
          have habs :
              |dist x.1 y.1 - dist (approxPoint x) (approxPoint y)| ≤
                higherRankRepresentativeNorm n (Quotient.out x.1)
                    (finitelySupportedHigherRankRepresentative n (approxData x)) +
                  higherRankRepresentativeNorm n (Quotient.out y.1)
                    (finitelySupportedHigherRankRepresentative n (approxData y)) := by
            have h := quotientDistanceLipschitzRepresentatives n (Quotient.out x.1)
              (Quotient.out y.1)
              (finitelySupportedHigherRankRepresentative n (approxData x))
              (finitelySupportedHigherRankRepresentative n (approxData y))
            simpa [approxPoint, higherRankQuotientMk] using h
          have habs_error :
              |dist x.1 y.1 - dist (approxPoint x) (approxPoint y)| ≤ errorRadius := by
            dsimp [δ] at hxclose hyclose
            nlinarith
          have hlower : (1 - a) * dist x.1 y.1 ≤ dist (approxPoint x) (approxPoint y) := by
            have hsub_le_abs :
                dist x.1 y.1 - dist (approxPoint x) (approxPoint y) ≤
                  |dist x.1 y.1 - dist (approxPoint x) (approxPoint y)| :=
              le_abs_self _
            nlinarith
          have hupper :
              dist (approxPoint x) (approxPoint y) ≤
                (1 + eps) * (1 - a) * dist x.1 y.1 := by
            have hneg_le_abs :
                dist (approxPoint x) (approxPoint y) - dist x.1 y.1 ≤
                  |dist x.1 y.1 - dist (approxPoint x) (approxPoint y)| := by
              simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
                neg_le_abs (dist x.1 y.1 - dist (approxPoint x) (approxPoint y))
            have hdp_le : dist (approxPoint x) (approxPoint y) ≤
                (1 + a) * dist x.1 y.1 := by
              nlinarith
            have hfactor_dist :
                (1 + a) * dist x.1 y.1 ≤
                  ((1 + eps) * (1 - a)) * dist x.1 y.1 :=
              mul_le_mul_of_nonneg_right hfactor dist_nonneg
            nlinarith
          exact ⟨hlower, by simpa [mul_assoc] using hupper⟩
  · let δ : Real := 1
    have hδpos : 0 < δ := by
      norm_num [δ]
    let approxData : points -> finitelySupportedHigherRankPoint n := fun q =>
      Classical.choose (exists_finitelySupportedHigherRankPoint_near n (Quotient.out q.1) hδpos)
    let approxPoint : points -> higherRankSphereQuotient n := fun q =>
      higherRankQuotientMk n (finitelySupportedHigherRankRepresentative n (approxData q))
    let G : Finset (higherRankSphereQuotient n) := Finset.univ.image approxPoint
    refine ⟨G, ?_, ?_⟩
    · intro y hy
      rcases Finset.mem_image.mp hy with ⟨q, _hq, rfl⟩
      exact ⟨approxData q, rfl⟩
    · refine ⟨fun q => ⟨approxPoint q, ?_⟩, 1, by norm_num, ?_⟩
      · exact Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩
      · intro x y
        have hxy : x = y := by
          by_contra hne
          exact hpairs ⟨(x, y), by simp [pairFinset, hne]⟩
        subst hxy
        simp [approxPoint]

private lemma int_box_bound_of_natAbs_le {z : Int} {L : Nat} (h : z.natAbs ≤ L) :
    -(L : Int) ≤ z ∧ z ≤ (L : Int) := by
  have habsNat : (z.natAbs : Int) ≤ (L : Int) := by exact_mod_cast h
  have habs : |z| ≤ (L : Int) := by
    simpa [Int.natCast_natAbs] using habsNat
  exact abs_le.mp habs

private noncomputable def finiteSupportDifferenceRadius
    (n : Nat) (F : Finset (finitelySupportedHigherRankPoint n)) : Nat :=
  F.sup fun x => F.sup fun y => x.2.1.sup fun k => y.2.1.sup fun l =>
    Finset.univ.sup fun i : Fin n => Int.natAbs (k i - l i)

private lemma exists_finiteSupportDifferenceBoxBound
    (n : Nat) (F : Finset (finitelySupportedHigherRankPoint n)) :
    ∃ L : Nat, finiteSupportDifferenceBoxBound n L F := by
  classical
  refine ⟨finiteSupportDifferenceRadius n F, ?_⟩
  intro x hx y hy k hk l hl i
  apply int_box_bound_of_natAbs_le
  have hi_le : Int.natAbs (k i - l i) ≤
      Finset.univ.sup (fun j : Fin n => Int.natAbs (k j - l j)) :=
    Finset.le_sup (f := fun j : Fin n => Int.natAbs (k j - l j)) (Finset.mem_univ i)
  have hl_le : Finset.univ.sup (fun j : Fin n => Int.natAbs (k j - l j)) ≤
      y.2.1.sup (fun l' => Finset.univ.sup fun j : Fin n => Int.natAbs (k j - l' j)) :=
    Finset.le_sup
      (f := fun l' => Finset.univ.sup fun j : Fin n => Int.natAbs (k j - l' j)) hl
  have hk_le : y.2.1.sup (fun l' =>
        Finset.univ.sup fun j : Fin n => Int.natAbs (k j - l' j)) ≤
      x.2.1.sup (fun k' => y.2.1.sup fun l' =>
        Finset.univ.sup fun j : Fin n => Int.natAbs (k' j - l' j)) :=
    Finset.le_sup
      (f := fun k' => y.2.1.sup fun l' =>
        Finset.univ.sup fun j : Fin n => Int.natAbs (k' j - l' j)) hk
  have hy_le : x.2.1.sup (fun k' => y.2.1.sup fun l' =>
        Finset.univ.sup fun j : Fin n => Int.natAbs (k' j - l' j)) ≤
      F.sup (fun y' => x.2.1.sup fun k' => y'.2.1.sup fun l' =>
        Finset.univ.sup fun j : Fin n => Int.natAbs (k' j - l' j)) :=
    Finset.le_sup
      (f := fun y' => x.2.1.sup fun k' => y'.2.1.sup fun l' =>
        Finset.univ.sup fun j : Fin n => Int.natAbs (k' j - l' j)) hy
  have hx_le : F.sup (fun y' => x.2.1.sup fun k' => y'.2.1.sup fun l' =>
        Finset.univ.sup fun j : Fin n => Int.natAbs (k' j - l' j)) ≤
      finiteSupportDifferenceRadius n F :=
    Finset.le_sup
      (f := fun x' => F.sup fun y' => x'.2.1.sup fun k' => y'.2.1.sup fun l' =>
        Finset.univ.sup fun j : Fin n => Int.natAbs (k' j - l' j)) hx
  exact hi_le.trans (hl_le.trans (hk_le.trans (hy_le.trans hx_le)))

private lemma shiftQuotient_dist_eq_zero_iff (x y : shiftSphereQuotient) :
    (letI : PseudoMetricSpace shiftSphereQuotient := shiftChordalMetric;
      dist x y = 0 ↔ x = y) := by
  letI : PseudoMetricSpace shiftSphereQuotient := shiftChordalMetric
  constructor
  · intro hdist
    let orbit : Set shiftHilbertSphere := Set.range fun a : Int => shiftAction a (Quotient.out y)
    have horbit_nonempty : orbit.Nonempty := Set.range_nonempty _
    have hdist_inf : dist x y = Metric.infDist (Quotient.out x) orbit := by
      change ((⨅ i : Int, edist (Quotient.out x) (shiftAction i (Quotient.out y))).toReal) =
        Metric.infDist (Quotient.out x) orbit
      dsimp [Metric.infDist, Metric.infEDist, orbit]
      rw [iInf_range]
    have hinf_zero : Metric.infDist (Quotient.out x) orbit = 0 := by
      rwa [← hdist_inf]
    have hx_closure : Quotient.out x ∈ closure orbit :=
      (Metric.mem_closure_iff_infDist_zero horbit_nonempty).mpr hinf_zero
    have horbit_closed : IsClosed orbit := by
      simpa [orbit, shiftOrbit] using shiftOrbitsClosed (Quotient.out y)
    have hx_mem : Quotient.out x ∈ orbit := by
      simpa [horbit_closed.closure_eq] using hx_closure
    rcases hx_mem with ⟨a, ha⟩
    have hquot :
        (⟦Quotient.out y⟧ : shiftSphereQuotient) =
          (⟦Quotient.out x⟧ : shiftSphereQuotient) := by
      apply Quotient.sound
      change ∃ a : Int, Quotient.out x = shiftAction a (Quotient.out y)
      exact ⟨a, ha.symm⟩
    exact (Quotient.out_eq x).symm.trans (hquot.symm.trans (Quotient.out_eq y))
  · intro hxy
    subst hxy
    simp

private noncomputable def twoPointShiftRaw : codingShiftL2Space :=
  lp.single (E := fun (_ : Int) => Real) 2 0 1 +
    lp.single (E := fun (_ : Int) => Real) 2 1 1

private lemma twoPointShiftRaw_ne_zero : twoPointShiftRaw ≠ 0 := by
  intro h
  have h0 := congrArg (fun f : codingShiftL2Space => (f : Int -> Real) 0) h
  change
    (lp.single (E := fun (_ : Int) => Real) 2 0 1 : codingShiftL2Space) 0 +
        (lp.single (E := fun (_ : Int) => Real) 2 1 1 : codingShiftL2Space) 0 =
      (0 : Real) at h0
  norm_num at h0

private noncomputable def twoPointShiftSphereVector : shiftHilbertSphere :=
  normalizedShiftL2Vector twoPointShiftRaw twoPointShiftRaw_ne_zero

private lemma twoPointShiftSphereVector_apply_zero_ne_zero :
    (twoPointShiftSphereVector : codingShiftL2Space) 0 ≠ 0 := by
  have hnorm : ‖twoPointShiftRaw‖ ≠ 0 := norm_ne_zero_iff.mpr twoPointShiftRaw_ne_zero
  change ((‖twoPointShiftRaw‖)⁻¹ • twoPointShiftRaw : codingShiftL2Space) 0 ≠ 0
  have hnorm' :
      ‖(lp.single (E := fun (_ : Int) => Real) 2 0 1 : codingShiftL2Space) +
          lp.single (E := fun (_ : Int) => Real) 2 1 1‖ ≠ 0 := by
    simpa [twoPointShiftRaw] using hnorm
  dsimp [twoPointShiftRaw]
  change
    (‖(lp.single (E := fun (_ : Int) => Real) 2 0 1 : codingShiftL2Space) +
          lp.single (E := fun (_ : Int) => Real) 2 1 1‖)⁻¹ *
        ((lp.single (E := fun (_ : Int) => Real) 2 0 1 : codingShiftL2Space) 0 +
          (lp.single (E := fun (_ : Int) => Real) 2 1 1 : codingShiftL2Space) 0) ≠
      0
  simp [hnorm']

private lemma twoPointShiftSphereVector_apply_one_ne_zero :
    (twoPointShiftSphereVector : codingShiftL2Space) 1 ≠ 0 := by
  have hnorm : ‖twoPointShiftRaw‖ ≠ 0 := norm_ne_zero_iff.mpr twoPointShiftRaw_ne_zero
  change ((‖twoPointShiftRaw‖)⁻¹ • twoPointShiftRaw : codingShiftL2Space) 1 ≠ 0
  have hnorm' :
      ‖(lp.single (E := fun (_ : Int) => Real) 2 0 1 : codingShiftL2Space) +
          lp.single (E := fun (_ : Int) => Real) 2 1 1‖ ≠ 0 := by
    simpa [twoPointShiftRaw] using hnorm
  dsimp [twoPointShiftRaw]
  change
    (‖(lp.single (E := fun (_ : Int) => Real) 2 0 1 : codingShiftL2Space) +
          lp.single (E := fun (_ : Int) => Real) 2 1 1‖)⁻¹ *
        ((lp.single (E := fun (_ : Int) => Real) 2 0 1 : codingShiftL2Space) 1 +
          (lp.single (E := fun (_ : Int) => Real) 2 1 1 : codingShiftL2Space) 1) ≠
      0
  simp [hnorm']

private lemma defaultShiftQuotient_ne_twoPoint :
    shiftQuotientMk defaultShiftSphereVector ≠
      shiftQuotientMk twoPointShiftSphereVector := by
  intro h
  rcases Quotient.exact h with ⟨a, ha⟩
  change twoPointShiftSphereVector = shiftAction a defaultShiftSphereVector at ha
  by_cases ha0 : a = 0
  · have hval := congrArg (fun v : shiftHilbertSphere => (v : codingShiftL2Space) 1) ha
    have hright : (shiftAction a defaultShiftSphereVector : codingShiftL2Space) 1 = 0 := by
      change (defaultShiftSphereVector : codingShiftL2Space) (1 - a) = 0
      subst ha0
      simp [defaultShiftSphereVector, defaultShiftL2Vector]
    have hleft_ne := twoPointShiftSphereVector_apply_one_ne_zero
    have hval' : (twoPointShiftSphereVector : codingShiftL2Space) 1 =
        (shiftAction a defaultShiftSphereVector : codingShiftL2Space) 1 := by
      simpa using hval
    rw [hright] at hval'
    exact hleft_ne hval'
  · have hval := congrArg (fun v : shiftHilbertSphere => (v : codingShiftL2Space) 0) ha
    have hright : (shiftAction a defaultShiftSphereVector : codingShiftL2Space) 0 = 0 := by
      change (defaultShiftSphereVector : codingShiftL2Space) (0 - a) = 0
      simp [defaultShiftSphereVector, defaultShiftL2Vector, ha0]
    have hleft_ne := twoPointShiftSphereVector_apply_zero_ne_zero
    have hval' : (twoPointShiftSphereVector : codingShiftL2Space) 0 =
        (shiftAction a defaultShiftSphereVector : codingShiftL2Space) 0 := by
      simpa using hval
    rw [hright] at hval'
    exact hleft_ne hval'

private lemma fixedShiftPair_dist_pos :
    (letI : PseudoMetricSpace shiftSphereQuotient := shiftChordalMetric;
      0 < dist (shiftQuotientMk defaultShiftSphereVector)
        (shiftQuotientMk twoPointShiftSphereVector)) := by
  letI : PseudoMetricSpace shiftSphereQuotient := shiftChordalMetric
  have hdist_ne : dist (shiftQuotientMk defaultShiftSphereVector)
      (shiftQuotientMk twoPointShiftSphereVector) ≠ 0 := by
    intro hdist
    exact defaultShiftQuotient_ne_twoPoint ((shiftQuotient_dist_eq_zero_iff _ _).mp hdist)
  exact lt_of_le_of_ne dist_nonneg (Ne.symm hdist_ne)

private abbrev zeroRankIndex : Fin 0 -> Int := fun i => i.elim0

private lemma zeroRank_l2_eq_single (x : higherRankHilbertSphere 0) :
    (x : codingHigherRankL2Space 0) =
      lp.single (E := fun (_ : Fin 0 -> Int) => Real) 2 zeroRankIndex
        ((x : codingHigherRankL2Space 0) zeroRankIndex) := by
  ext k
  have hk : k = zeroRankIndex := by
    ext i
    exact i.elim0
  subst hk
  simp

private lemma zeroRank_coord_eq_or (x : higherRankHilbertSphere 0) :
    ((x : codingHigherRankL2Space 0) zeroRankIndex) = 1 ∨
      ((x : codingHigherRankL2Space 0) zeroRankIndex) = -1 := by
  have hxnorm : ‖(x : codingHigherRankL2Space 0)‖ = 1 := by
    rw [← dist_zero_right (x : codingHigherRankL2Space 0)]
    exact x.2
  rw [zeroRank_l2_eq_single x] at hxnorm
  have hcoord_norm : ‖((x : codingHigherRankL2Space 0) zeroRankIndex)‖ = 1 := by
    simpa using hxnorm
  rw [Real.norm_eq_abs] at hcoord_norm
  by_cases hnonneg : 0 ≤ ((x : codingHigherRankL2Space 0) zeroRankIndex)
  · left
    rw [abs_of_nonneg hnonneg] at hcoord_norm
    exact hcoord_norm
  · right
    have hnonpos : ((x : codingHigherRankL2Space 0) zeroRankIndex) ≤ 0 :=
      le_of_not_ge hnonneg
    rw [abs_of_nonpos hnonpos] at hcoord_norm
    linarith

private lemma zeroRankQuotient_eq_of_out_coord_eq
    {x y : higherRankSphereQuotient 0}
    (hcoord : ((Quotient.out x : higherRankHilbertSphere 0) : codingHigherRankL2Space 0)
        zeroRankIndex =
      ((Quotient.out y : higherRankHilbertSphere 0) : codingHigherRankL2Space 0)
        zeroRankIndex) :
    x = y := by
  have hvec : (Quotient.out x : higherRankHilbertSphere 0) = Quotient.out y := by
    apply Subtype.ext
    rw [zeroRank_l2_eq_single (Quotient.out x),
      zeroRank_l2_eq_single (Quotient.out y), hcoord]
  rw [← Quotient.out_eq x, ← Quotient.out_eq y, hvec]

private lemma zeroRankQuotient_eq_left_or_right
    {a b x : higherRankSphereQuotient 0} (hab : a ≠ b) :
    x = a ∨ x = b := by
  let coord : higherRankSphereQuotient 0 -> Real := fun q =>
    ((Quotient.out q : higherRankHilbertSphere 0) : codingHigherRankL2Space 0) zeroRankIndex
  have ha := zeroRank_coord_eq_or (Quotient.out a)
  have hb := zeroRank_coord_eq_or (Quotient.out b)
  have hx := zeroRank_coord_eq_or (Quotient.out x)
  change coord a = 1 ∨ coord a = -1 at ha
  change coord b = 1 ∨ coord b = -1 at hb
  change coord x = 1 ∨ coord x = -1 at hx
  rcases ha with ha | ha
  · rcases hb with hb | hb
    · exact (hab (zeroRankQuotient_eq_of_out_coord_eq (by simp [coord, ha, hb]))).elim
    · rcases hx with hx | hx
      · left
        exact zeroRankQuotient_eq_of_out_coord_eq (by simp [coord, ha, hx])
      · right
        exact zeroRankQuotient_eq_of_out_coord_eq (by simp [coord, hb, hx])
  · rcases hb with hb | hb
    · rcases hx with hx | hx
      · right
        exact zeroRankQuotient_eq_of_out_coord_eq (by simp [coord, hb, hx])
      · left
        exact zeroRankQuotient_eq_of_out_coord_eq (by simp [coord, ha, hx])
    · exact (hab (zeroRankQuotient_eq_of_out_coord_eq (by simp [coord, ha, hb]))).elim

private theorem zeroRankFiniteSubsetEmbedsInShiftQuotient
    (F : Finset (higherRankSphereQuotient 0)) (eps : Real) (heps : 0 < eps) :
    (letI : PseudoMetricSpace (higherRankSphereQuotient 0) := higherRankChordalMetric 0;
      letI : PseudoMetricSpace shiftSphereQuotient := shiftChordalMetric;
      FiniteMetricEmbedsWithDistortion shiftSphereQuotient F (1 + eps)) := by
  classical
  letI : PseudoMetricSpace (higherRankSphereQuotient 0) := higherRankChordalMetric 0
  letI : PseudoMetricSpace shiftSphereQuotient := shiftChordalMetric
  by_cases hpairs : ∃ a b : {x : higherRankSphereQuotient 0 // x ∈ F}, a ≠ b
  · rcases hpairs with ⟨a, b, hab⟩
    have hab_val : a.1 ≠ b.1 := by
      intro h
      exact hab (Subtype.ext h)
    let A : shiftSphereQuotient := shiftQuotientMk defaultShiftSphereVector
    let B : shiftSphereQuotient := shiftQuotientMk twoPointShiftSphereVector
    let dX : Real := dist a.1 b.1
    let dY : Real := dist A B
    have hdX_pos : 0 < dX := by
      have hdist_ne : dist a.1 b.1 ≠ 0 := by
        intro hdist
        exact hab_val ((higherRankQuotient_dist_eq_zero_iff 0 a.1 b.1).mp hdist)
      exact lt_of_le_of_ne dist_nonneg (Ne.symm hdist_ne)
    have hdY_pos : 0 < dY := by
      simpa [A, B, dY] using fixedShiftPair_dist_pos
    let scale : Real := dY / dX
    have hscale_pos : 0 < scale := div_pos hdY_pos hdX_pos
    have hscale_dX : scale * dX = dY := by
      dsimp [scale]
      field_simp [ne_of_gt hdX_pos]
    let embed : {x : higherRankSphereQuotient 0 // x ∈ F} -> shiftSphereQuotient :=
      fun x => if x = a then A else B
    refine ⟨embed, scale, hscale_pos, ?_⟩
    intro x y
    have hx_cases : x = a ∨ x = b := by
      rcases zeroRankQuotient_eq_left_or_right (a := a.1) (b := b.1) (x := x.1)
          hab_val with hx | hx
      · exact Or.inl (Subtype.ext hx)
      · exact Or.inr (Subtype.ext hx)
    have hy_cases : y = a ∨ y = b := by
      rcases zeroRankQuotient_eq_left_or_right (a := a.1) (b := b.1) (x := y.1)
          hab_val with hy | hy
      · exact Or.inl (Subtype.ext hy)
      · exact Or.inr (Subtype.ext hy)
    have hK : 1 ≤ 1 + eps := by linarith
    rcases hx_cases with hx | hx <;> rcases hy_cases with hy | hy
    · have hxy : x = y := hx.trans hy.symm
      subst y
      simp [embed, hx]
    · have hsource : scale * dist x.1 y.1 = dY := by
        rw [hx, hy]
        simpa [dX] using hscale_dX
      have htarget : dist (embed x) (embed y) = dY := by
        rw [hx, hy]
        simp [embed, A, B, dY, hab.symm]
      constructor
      · rw [hsource, htarget]
      · have hsource' : (1 + eps) * scale * dist x.1 y.1 = (1 + eps) * dY := by
          rw [mul_assoc, hsource]
        rw [htarget, hsource']
        nlinarith [hdY_pos.le, hK]
    · have hsource : scale * dist x.1 y.1 = dY := by
        rw [hx, hy, dist_comm]
        simpa [dX] using hscale_dX
      have htarget : dist (embed x) (embed y) = dY := by
        rw [hx, hy]
        simp [embed, A, B, dY, dist_comm, hab.symm]
      constructor
      · rw [hsource, htarget]
      · have hsource' : (1 + eps) * scale * dist x.1 y.1 = (1 + eps) * dY := by
          rw [mul_assoc, hsource]
        rw [htarget, hsource']
        nlinarith [hdY_pos.le, hK]
    · have hxy : x = y := hx.trans hy.symm
      subst y
      simp [embed, hx, hab.symm]
  · refine ⟨fun _ => shiftQuotientMk defaultShiftSphereVector, 1, by norm_num, ?_⟩
    intro x y
    have hxy : x = y := by
      by_contra hne
      exact hpairs ⟨x, y, hne⟩
    subst hxy
    simp

private theorem positiveRankFiniteSubsetEmbedsInShiftQuotient
    (n : Nat) (hn : 0 < n) (F : Finset (higherRankSphereQuotient n))
    (eps : Real) (heps : 0 < eps) :
    (letI : PseudoMetricSpace (higherRankSphereQuotient n) := higherRankChordalMetric n;
      letI : PseudoMetricSpace shiftSphereQuotient := shiftChordalMetric;
      FiniteMetricEmbedsWithDistortion shiftSphereQuotient F (1 + eps)) := by
  classical
  letI : PseudoMetricSpace (higherRankSphereQuotient n) := higherRankChordalMetric n
  letI : PseudoMetricSpace shiftSphereQuotient := shiftChordalMetric
  obtain ⟨G, hGrepr, hApprox⟩ := finiteSupportApproximationInQuotient n F eps heps
  obtain ⟨approx, scale, hscale, hApproxDist⟩ := hApprox
  let reprData : {y : higherRankSphereQuotient n // y ∈ G} ->
      finitelySupportedHigherRankPoint n :=
    fun y => Classical.choose (hGrepr y.1 y.2)
  have hrepr : ∀ y : {y : higherRankSphereQuotient n // y ∈ G},
      finitelySupportedToHigherRankQuotient n (reprData y) = y.1 := by
    intro y
    simpa [reprData, finitelySupportedToHigherRankQuotient] using
      Classical.choose_spec (hGrepr y.1 y.2)
  let dataFinset : Finset (finitelySupportedHigherRankPoint n) := Finset.univ.image reprData
  have hrepr_mem : ∀ y : {y : higherRankSphereQuotient n // y ∈ G},
      reprData y ∈ dataFinset := by
    intro y
    exact Finset.mem_image.mpr ⟨y, Finset.mem_univ y, rfl⟩
  obtain ⟨L, hL⟩ := exists_finiteSupportDifferenceBoxBound n dataFinset
  let M : Nat := 2 * L + 2
  have hM : 2 * L + 1 < M := by
    dsimp [M]
    omega
  have hCode := codingPreservesCorrelations n M L dataFinset hn hM hL
  let embedG : {y : higherRankSphereQuotient n // y ∈ G} -> shiftSphereQuotient :=
    fun y => shiftQuotientMk (encodedShiftRepresentative n M (reprData y))
  refine ⟨fun x => embedG (approx x), scale, hscale, ?_⟩
  intro x y
  have hxmem : reprData (approx x) ∈ dataFinset := hrepr_mem (approx x)
  have hymem : reprData (approx y) ∈ dataFinset := hrepr_mem (approx y)
  have hdistCode : dist (embedG (approx x)) (embedG (approx y)) =
      dist (finitelySupportedToHigherRankQuotient n (reprData (approx x)))
        (finitelySupportedToHigherRankQuotient n (reprData (approx y))) := by
    simpa [embedG] using hCode.2 (reprData (approx x)) hxmem (reprData (approx y)) hymem
  have hdistCode' : dist (embedG (approx x)) (embedG (approx y)) =
      dist (approx x).1 (approx y).1 := by
    rw [hdistCode, hrepr (approx x), hrepr (approx y)]
  simpa [hdistCode'] using hApproxDist x y

/-- Every finite subset of a higher-rank quotient embeds into the shift quotient. -/
theorem higherRankFiniteSubsetEmbedsInShiftQuotient
    (n : Nat) (F : Finset (higherRankSphereQuotient n)) (eps : Real) (heps : 0 < eps) :
    (letI : PseudoMetricSpace (higherRankSphereQuotient n) := higherRankChordalMetric n;
      letI : PseudoMetricSpace shiftSphereQuotient := shiftChordalMetric;
      FiniteMetricEmbedsWithDistortion shiftSphereQuotient F (1 + eps)) := by
  by_cases hn : 0 < n
  · exact positiveRankFiniteSubsetEmbedsInShiftQuotient n hn F eps heps
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    exact zeroRankFiniteSubsetEmbedsInShiftQuotient F eps heps

end

end SphereObstructionHilbertShiftQuotient
