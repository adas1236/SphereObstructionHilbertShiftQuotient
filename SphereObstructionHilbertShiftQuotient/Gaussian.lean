import SphereObstructionHilbertShiftQuotient.SphereQuotient
import SphereObstructionHilbertShiftQuotient.FlatTori
import SphereObstructionHilbertShiftQuotient.Summation

set_option linter.style.header false
open scoped ENNReal

/-!
Gaussian lattice vectors and finite flat-torus realizations.

This file connects the flat torus metric to higher-rank sphere quotients through
Gaussian lattice representatives.
-/

namespace SphereObstructionHilbertShiftQuotient

noncomputable section

private abbrev gaussianL2Space (n : Nat) : Type :=
  ↥(lp (fun (_ : Fin n -> Int) => Real) 2)

private noncomputable def gaussianIntegerPoint
    (n : Nat) (k : Fin n -> Int) : RealEuclideanSpace n :=
  WithLp.toLp 2 (fun i : Fin n => (k i : Real))

private noncomputable def gaussianIntegerAddSubgroup
    (n : Nat) : AddSubgroup (RealEuclideanSpace n) where
  carrier := {x | exists k : Fin n -> Int, x = gaussianIntegerPoint n k}
  zero_mem' := by
    refine ⟨0, ?_⟩
    ext i
    simp [gaussianIntegerPoint]
  add_mem' := by
    intro x y hx hy
    rcases hx with ⟨kx, rfl⟩
    rcases hy with ⟨ky, rfl⟩
    refine ⟨kx + ky, ?_⟩
    ext i
    simp [gaussianIntegerPoint]
  neg_mem' := by
    intro x hx
    rcases hx with ⟨kx, rfl⟩
    refine ⟨-kx, ?_⟩
    ext i
    simp [gaussianIntegerPoint]

private noncomputable def gaussianEuclideanStdBasis (n : Nat) :
    Module.Basis (Fin n) ℝ (RealEuclideanSpace n) :=
  (Pi.basisFun ℝ (Fin n)).map (WithLp.linearEquiv 2 ℝ (Fin n -> ℝ)).symm

private noncomputable def gaussianStandardIntegerLattice (n : Nat) :
    Submodule ℤ (RealEuclideanSpace n) :=
  Submodule.span ℤ (Set.range (gaussianEuclideanStdBasis n))

private lemma gaussianStandardIntegerLattice_finrank (n : Nat) :
    Module.finrank ℤ (gaussianStandardIntegerLattice n) = n := by
  rw [gaussianStandardIntegerLattice]
  rw [ZLattice.rank ℝ]
  simp

private lemma gaussianIntegerPoint_mem_standardIntegerLattice
    (n : Nat) (k : Fin n -> Int) :
    gaussianIntegerPoint n k ∈ gaussianStandardIntegerLattice n := by
  classical
  rw [gaussianStandardIntegerLattice]
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨k, ?_⟩
  ext i
  simp only [gaussianIntegerPoint, gaussianEuclideanStdBasis, ← PiLp.basisFun_eq_pi_basisFun,
    PiLp.basisFun_apply, WithLp.ofLp_sum, WithLp.ofLp_smul, zsmul_eq_mul,
    Finset.sum_apply, Pi.mul_apply, Pi.intCast_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [PiLp.single_eq_of_ne]
    · simp
    · exact fun h => hj h.symm
  · intro hi
    simp at hi

private lemma gaussianIntegerAddSubgroup_eq_standardIntegerLattice
    (n : Nat) :
    gaussianIntegerAddSubgroup n = (gaussianStandardIntegerLattice n).toAddSubgroup := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    exact gaussianIntegerPoint_mem_standardIntegerLattice n k
  · intro hx
    change x ∈ gaussianStandardIntegerLattice n at hx
    rw [gaussianStandardIntegerLattice] at hx
    rw [Submodule.mem_span_range_iff_exists_fun] at hx
    rcases hx with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← hk]
    ext i
    simp only [gaussianIntegerPoint, gaussianEuclideanStdBasis,
      ← PiLp.basisFun_eq_pi_basisFun, PiLp.basisFun_apply, WithLp.ofLp_sum,
      WithLp.ofLp_smul, zsmul_eq_mul, Finset.sum_apply, Pi.mul_apply, Pi.intCast_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [PiLp.single_eq_of_ne]
      · simp
      · exact fun h => hj h.symm
    · intro hi
      simp at hi

private lemma gaussianIntegerAddSubgroup_isClosed_default
    (n : Nat) :
    IsClosed (gaussianIntegerAddSubgroup n : Set (RealEuclideanSpace n)) := by
  rw [gaussianIntegerAddSubgroup_eq_standardIntegerLattice n]
  haveI : DiscreteTopology (gaussianStandardIntegerLattice n) := by
    change DiscreteTopology (Submodule.span ℤ (Set.range (gaussianEuclideanStdBasis n)))
    infer_instance
  letI : DiscreteTopology ↥(gaussianStandardIntegerLattice n).toAddSubgroup := by
    change DiscreteTopology (gaussianStandardIntegerLattice n)
    infer_instance
  exact @AddSubgroup.isClosed_of_discrete (RealEuclideanSpace n) _ _ _ _
    (gaussianStandardIntegerLattice n).toAddSubgroup inferInstance

private lemma gaussianIntegerPoint_add
    (n : Nat) (k a : Fin n -> Int) :
    gaussianIntegerPoint n (k + a) =
      gaussianIntegerPoint n k + gaussianIntegerPoint n a := by
  ext i
  simp [gaussianIntegerPoint]

private lemma gaussianIntegerPoint_sub
    (n : Nat) (k a : Fin n -> Int) :
    gaussianIntegerPoint n (k - a) =
      gaussianIntegerPoint n k - gaussianIntegerPoint n a := by
  ext i
  simp [gaussianIntegerPoint]

private lemma gaussianIntegerPoint_latticeMap_injective (n : Nat) :
    Function.Injective
      (fun k : Fin n -> Int =>
        (⟨gaussianIntegerPoint n k,
          gaussianIntegerPoint_mem_standardIntegerLattice n k⟩ :
            gaussianStandardIntegerLattice n)) := by
  intro k l h
  funext i
  have hp : gaussianIntegerPoint n k = gaussianIntegerPoint n l := congrArg Subtype.val h
  have hi := congrArg (fun x : RealEuclideanSpace n => (x : Fin n -> Real) i) hp
  exact Int.cast_injective (by simpa [gaussianIntegerPoint] using hi)

private lemma finite_gaussianIntegerPoint_norm_le (n : Nat) (A : ℝ) :
    Set.Finite {k : Fin n -> Int | ‖gaussianIntegerPoint n k‖ ≤ A} := by
  let i : (Fin n -> Int) -> gaussianStandardIntegerLattice n := fun k =>
    ⟨gaussianIntegerPoint n k, gaussianIntegerPoint_mem_standardIntegerLattice n k⟩
  have hi : Function.Injective i := gaussianIntegerPoint_latticeMap_injective n
  refine Set.Finite.of_finite_image (f := i) ?_ hi.injOn
  have hfiniteTarget : Set.Finite
      {z : gaussianStandardIntegerLattice n | ‖(z : RealEuclideanSpace n)‖ ≤ A} := by
    haveI : DiscreteTopology (gaussianStandardIntegerLattice n) := by
      change DiscreteTopology (Submodule.span ℤ (Set.range (gaussianEuclideanStdBasis n)))
      infer_instance
    by_cases hA : A < 0
    · rw [show {z : gaussianStandardIntegerLattice n | ‖(z : RealEuclideanSpace n)‖ ≤ A} =
          ∅ by
        ext z
        simp [not_le.mpr (lt_of_lt_of_le hA (norm_nonneg (z : RealEuclideanSpace n)))]]
      exact Set.finite_empty
    · have hclosed : IsClosed (gaussianStandardIntegerLattice n :
          Set (RealEuclideanSpace n)) := by
        exact @AddSubgroup.isClosed_of_discrete (RealEuclideanSpace n) _ _ _ _
          (gaussianStandardIntegerLattice n).toAddSubgroup inferInstance
      have hfiniteInter : Set.Finite
          (Metric.closedBall (0 : RealEuclideanSpace n) A ∩
            (gaussianStandardIntegerLattice n : Set (RealEuclideanSpace n))) := by
        exact Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
          Metric.isBounded_closedBall hclosed
      refine Set.Finite.of_finite_image
        (f := fun z : gaussianStandardIntegerLattice n => (z : RealEuclideanSpace n)) ?_
        Subtype.val_injective.injOn
      refine hfiniteInter.subset ?_
      rintro y ⟨z, hz, rfl⟩
      exact ⟨by simpa [Metric.mem_closedBall, dist_eq_norm] using hz, z.2⟩
  refine hfiniteTarget.subset ?_
  rintro z ⟨k, hk, rfl⟩
  exact hk

private lemma summable_gaussianIntegerPoint_norm_inv_pow {n M : Nat} (hM : n < M) :
    Summable fun k : Fin n -> Int => ‖gaussianIntegerPoint n k‖⁻¹ ^ M := by
  haveI : DiscreteTopology (gaussianStandardIntegerLattice n) := by
    change DiscreteTopology (Submodule.span ℤ (Set.range (gaussianEuclideanStdBasis n)))
    infer_instance
  have hrank : Module.finrank ℤ (gaussianStandardIntegerLattice n) < M := by
    simpa [gaussianStandardIntegerLattice_finrank n] using hM
  have hsL : Summable fun z : gaussianStandardIntegerLattice n =>
      ‖(z : RealEuclideanSpace n)‖⁻¹ ^ M := by
    exact ZLattice.summable_norm_pow_inv (gaussianStandardIntegerLattice n) M hrank
  let i : (Fin n -> Int) -> gaussianStandardIntegerLattice n := fun k =>
    ⟨gaussianIntegerPoint n k, gaussianIntegerPoint_mem_standardIntegerLattice n k⟩
  have hi : Function.Injective i := gaussianIntegerPoint_latticeMap_injective n
  simpa [i] using hsL.comp_injective hi

private lemma tendsto_gaussianIntegerPoint_norm_atTop (n : Nat) :
    Filter.Tendsto (fun k : Fin n -> Int => ‖gaussianIntegerPoint n k‖)
      Filter.cofinite Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro A
  filter_upwards [(finite_gaussianIntegerPoint_norm_le n A).compl_mem_cofinite] with k hk
  exact le_of_not_ge hk

private lemma eventually_exp_neg_mul_sq_le_inv_pow {b : Real} (hb : 0 < b) (M : Nat) :
    ∀ᶠ r in Filter.atTop, Real.exp (-b * r ^ 2) <= r⁻¹ ^ M := by
  have ho := (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg hb (M : Real)).bound zero_lt_one
  filter_upwards [ho, Filter.eventually_ge_atTop (1 : Real)] with r hr h1
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one h1
  have hexp_le_one : Real.exp (-(1 / 2) * r) <= 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [h1]
  have hnorm_nonneg : 0 <= r ^ (M : Real) * Real.exp (-b * r ^ 2) := by
    positivity
  have hmul_le : r ^ (M : Real) * Real.exp (-b * r ^ 2) <= 1 := by
    calc
      r ^ (M : Real) * Real.exp (-b * r ^ 2) =
          ‖r ^ (M : Real) * Real.exp (-b * r ^ 2)‖ := by
            rw [Real.norm_of_nonneg hnorm_nonneg]
      _ <= 1 * ‖Real.exp (-(1 / 2) * r)‖ := hr
      _ <= 1 := by
            rw [one_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
            exact hexp_le_one
  have hmul_le_nat : r ^ M * Real.exp (-b * r ^ 2) <= 1 := by
    simpa [Real.rpow_natCast] using hmul_le
  have hpow_pos : 0 < r ^ M := pow_pos hrpos M
  have hprod : Real.exp (-b * r ^ 2) * r ^ M <= 1 := by
    simpa [mul_comm] using hmul_le_nat
  have hdiv : Real.exp (-b * r ^ 2) <= 1 / r ^ M :=
    (le_div_iff₀ hpow_pos).mpr hprod
  simpa [one_div, inv_pow] using hdiv

private lemma exp_neg_iteratedFDeriv_norm_le (m : Nat) (t : Real) :
    ‖iteratedFDeriv Real m (fun s : Real => Real.exp (-s)) t‖ <= Real.exp (-t) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  rw [show (fun s : Real => Real.exp (-s)) =
      (fun s : Real => Real.exp ((-1 : Real) * s)) by
    ext s
    ring_nf]
  rw [iteratedDeriv_exp_const_mul]
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hpow : ‖(-1 : Real) ^ m‖ = 1 := by
    rw [norm_pow]
    norm_num
  rw [hpow, one_mul]
  ring_nf
  exact le_rfl

private lemma polynomial_mul_exp_neg_sq_bounded
    {b : Real} (hb : 0 < b) (k p : Nat) :
    ∃ C : Real, 0 <= C ∧
      ∀ r : Real, 0 <= r ->
        r ^ k * (1 + r) ^ p * Real.exp (-b * r ^ 2) <= C := by
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp
    (eventually_exp_neg_mul_sq_le_inv_pow hb (k + p))
  let T : Real := max 1 a
  let C : Real := max (T ^ k * (1 + T) ^ p) (2 ^ p)
  refine ⟨C, ?_, ?_⟩
  · dsimp [C, T]
    positivity
  intro r hr
  by_cases hlarge : T <= r
  · have hT_ge_a : a <= T := le_max_right 1 a
    have hT_ge_one : 1 <= T := le_max_left 1 a
    have hR_ge_a : a <= r := le_trans hT_ge_a hlarge
    have hR_ge_one : 1 <= r := le_trans hT_ge_one hlarge
    have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hR_ge_one
    have hexp := ha r hR_ge_a
    have hone_add : 1 + r <= 2 * r := by linarith
    have hpoly : (1 + r) ^ p <= (2 * r) ^ p := by
      exact pow_le_pow_left₀ (by positivity) hone_add p
    have hbound :
        r ^ k * (1 + r) ^ p * Real.exp (-b * r ^ 2) <= 2 ^ p := by
      calc
        r ^ k * (1 + r) ^ p * Real.exp (-b * r ^ 2)
            <= r ^ k * (2 * r) ^ p * (r⁻¹ ^ (k + p)) := by
              gcongr
        _ = 2 ^ p := by
              have hcancel : r ^ k * r ^ p * r⁻¹ ^ k * r⁻¹ ^ p = 1 := by
                calc
                  r ^ k * r ^ p * r⁻¹ ^ k * r⁻¹ ^ p
                      = r ^ (k + p) * r⁻¹ ^ (k + p) := by
                        rw [pow_add, pow_add]
                        ring
                  _ = 1 := by
                        rw [inv_pow]
                        field_simp [hrpos.ne']
              calc
                r ^ k * (2 * r) ^ p * (r⁻¹ ^ (k + p))
                    = 2 ^ p * (r ^ k * r ^ p * r⁻¹ ^ k * r⁻¹ ^ p) := by
                      rw [mul_pow, pow_add]
                      ring
                _ = 2 ^ p := by rw [hcancel, mul_one]
    exact hbound.trans (le_max_right _ _)
  · have hleT : r <= T := le_of_not_ge hlarge
    have hexp_le_one : Real.exp (-b * r ^ 2) <= 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [hb, sq_nonneg r]
    have hsmall :
        r ^ k * (1 + r) ^ p * Real.exp (-b * r ^ 2) <=
          T ^ k * (1 + T) ^ p := by
      have hT_nonneg : 0 <= T := le_trans hr hleT
      have hrk : r ^ k <= T ^ k := pow_le_pow_left₀ hr hleT k
      have hone_nonneg : 0 <= 1 + r := by positivity
      have hone_le : 1 + r <= 1 + T := by linarith
      have hp_le : (1 + r) ^ p <= (1 + T) ^ p :=
        pow_le_pow_left₀ hone_nonneg hone_le p
      have hpoly :
          r ^ k * (1 + r) ^ p <= T ^ k * (1 + T) ^ p := by
        exact mul_le_mul hrk hp_le (pow_nonneg hone_nonneg p) (pow_nonneg hT_nonneg k)
      calc
        r ^ k * (1 + r) ^ p * Real.exp (-b * r ^ 2)
            <= r ^ k * (1 + r) ^ p * 1 := by
              gcongr
        _ = r ^ k * (1 + r) ^ p := by ring
        _ <= T ^ k * (1 + T) ^ p := hpoly
    exact hsmall.trans (le_max_left _ _)

private lemma summable_exp_neg_mul_gaussianIntegerPoint_norm_sq
    {n : Nat} {b : Real} (hb : 0 < b) :
    Summable fun k : Fin n -> Int => Real.exp (-b * ‖gaussianIntegerPoint n k‖ ^ 2) := by
  let M : Nat := n + 1
  have hM : n < M := by
    dsimp [M]
    omega
  have hs : Summable fun k : Fin n -> Int => ‖gaussianIntegerPoint n k‖⁻¹ ^ M :=
    summable_gaussianIntegerPoint_norm_inv_pow hM
  refine Summable.of_norm_bounded_eventually hs ?_
  have hev_atTop := eventually_exp_neg_mul_sq_le_inv_pow hb M
  have hev := (tendsto_gaussianIntegerPoint_norm_atTop n).eventually hev_atTop
  filter_upwards [hev] with k hk
  simpa [Real.norm_of_nonneg (Real.exp_pos _).le] using hk

private lemma matrixNormSq_lower_bound
    (n : Nat) (A : LatticeBasis n) :
    ∃ c : Real, 0 < c ∧
      ∀ x : RealEuclideanSpace n, c * ‖x‖ <= ‖Matrix.toEuclideanLin A.matrix x‖ := by
  classical
  let b : Module.Basis (Fin n) Real (RealEuclideanSpace n) :=
    (EuclideanSpace.basisFun (Fin n) Real).toBasis
  let eLin : RealEuclideanSpace n ≃ₗ[Real] RealEuclideanSpace n :=
    Matrix.toLinearEquiv b A.matrix A.invertible
  have hLin : (eLin : RealEuclideanSpace n →ₗ[Real] RealEuclideanSpace n) =
      Matrix.toEuclideanLin A.matrix := by
    change (eLin : RealEuclideanSpace n →ₗ[Real] RealEuclideanSpace n) =
      Matrix.toEuclideanLin A.matrix
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    rfl
  obtain ⟨C, hCpos, hC⟩ :=
    SemilinearMapClass.bound_of_continuous
      (eLin.symm : RealEuclideanSpace n →ₗ[Real] RealEuclideanSpace n) (by fun_prop)
  refine ⟨C⁻¹, inv_pos.mpr hCpos, ?_⟩
  intro x
  have hx := hC (eLin x)
  have hxnorm : ‖x‖ <= C * ‖eLin x‖ := by
    simpa using hx
  have hCnn : 0 <= C := hCpos.le
  have hmul := mul_le_mul_of_nonneg_left hxnorm (inv_nonneg.mpr hCnn)
  have htmp : C⁻¹ * ‖x‖ <= ‖eLin x‖ := by
    calc
      C⁻¹ * ‖x‖ <= C⁻¹ * (C * ‖eLin x‖) := hmul
      _ = ‖eLin x‖ := by field_simp [hCpos.ne']
  simpa [hLin] using htmp

private lemma matrixNormSq_eq_inner
    (n : Nat) (A : LatticeBasis n) (x : RealEuclideanSpace n) :
    matrixNormSq n A x =
      inner Real (Matrix.toEuclideanLin A.matrix x) (Matrix.toEuclideanLin A.matrix x) := by
  rw [matrixNormSq]
  exact (real_inner_self_eq_norm_sq (Matrix.toEuclideanLin A.matrix x)).symm

private lemma matrixNormSq_smul
    (n : Nat) (A : LatticeBasis n) (a : Real) (x : RealEuclideanSpace n) :
    matrixNormSq n A (a • x) = a ^ 2 * matrixNormSq n A x := by
  rw [matrixNormSq, matrixNormSq, map_smul, norm_smul]
  rw [mul_pow]
  rw [show ‖a‖ ^ 2 = a ^ 2 by simp [Real.norm_eq_abs]]

private lemma matrixNormSq_sub_add_half
    (n : Nat) (A : LatticeBasis n) (z d : RealEuclideanSpace n) :
    matrixNormSq n A (z - d) / 2 + matrixNormSq n A (z + d) / 2 =
      matrixNormSq n A z + matrixNormSq n A d := by
  simp only [matrixNormSq]
  rw [map_sub, map_add]
  rw [norm_sub_sq_real, norm_add_sq_real]
  ring

private lemma matrixQuadratic_temperate
    (n : Nat) (A : LatticeBasis n) :
    Function.HasTemperateGrowth
      (fun x : RealEuclideanSpace n =>
        inner Real (Matrix.toEuclideanLin A.matrix x) (Matrix.toEuclideanLin A.matrix x)) := by
  let L : RealEuclideanSpace n →L[Real] RealEuclideanSpace n :=
    (Matrix.toEuclideanLin A.matrix).toContinuousLinearMap
  have h :
      Function.HasTemperateGrowth
        (fun x : RealEuclideanSpace n => (innerSL Real (L x)) (L x)) := by
    exact ContinuousLinearMap.bilinear_hasTemperateGrowth (innerSL Real)
      L.hasTemperateGrowth L.hasTemperateGrowth
  convert h using 1

private noncomputable def gaussianSchwartz
    (n : Nat) (A : LatticeBasis n) : SchwartzMap (RealEuclideanSpace n) Real where
  toFun := fun x =>
    Real.exp
      (-(inner Real (Matrix.toEuclideanLin A.matrix x) (Matrix.toEuclideanLin A.matrix x)))
  smooth' := by
    let L : RealEuclideanSpace n →L[Real] RealEuclideanSpace n :=
      (Matrix.toEuclideanLin A.matrix).toContinuousLinearMap
    have hquad :
        ContDiff Real ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : RealEuclideanSpace n => inner Real (L x) (L x)) :=
      (contDiff_inner (𝕜 := Real)).comp (ContDiff.prodMk L.contDiff L.contDiff)
    have htarget :
        ContDiff Real ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : RealEuclideanSpace n =>
          Real.exp (-(inner Real (L x) (L x)))) :=
      Real.contDiff_exp.comp hquad.neg
    simpa [L] using htarget
  decay' := by
    intro k m
    let q : RealEuclideanSpace n → Real := fun x =>
      inner Real (Matrix.toEuclideanLin A.matrix x) (Matrix.toEuclideanLin A.matrix x)
    have hqTemp : Function.HasTemperateGrowth q := matrixQuadratic_temperate n A
    obtain ⟨ell, Cq, hCq_nonneg, hq_deriv⟩ :=
      hqTemp.norm_iteratedFDeriv_le_uniform m
    obtain ⟨c, hc_pos, hc⟩ := matrixNormSq_lower_bound n A
    let b : Real := c ^ 2
    have hb : 0 < b := by
      dsimp [b]
      positivity
    obtain ⟨B, _hB_nonneg, hB⟩ :=
      polynomial_mul_exp_neg_sq_bounded hb k (ell * m)
    refine ⟨(m.factorial : Real) * (Cq + 1) ^ m * B, ?_⟩
    intro x
    have hq_smooth := hqTemp.1
    let D : Real := (Cq + 1) * (1 + ‖x‖) ^ ell
    have hD_bound :
        ∀ i : Nat, 1 <= i -> i <= m -> ‖iteratedFDeriv Real i q x‖ <= D ^ i := by
      intro i hi him
      have hbase := hq_deriv i him x
      have hD_nonneg : 0 <= D := by
        dsimp [D]
        positivity
      calc
        ‖iteratedFDeriv Real i q x‖ <= Cq * (1 + ‖x‖) ^ ell := hbase
        _ <= (Cq + 1) * (1 + ‖x‖) ^ ell := by
              gcongr
              linarith
        _ <= D ^ i := by
              dsimp [D]
              apply le_self_pow₀
              · exact one_le_mul_of_one_le_of_one_le (by linarith)
                  (one_le_pow₀ (by nlinarith [norm_nonneg x]))
              · exact (lt_of_lt_of_le zero_lt_one hi).ne'
    have hExp_bound :
        ∀ i, i <= m ->
          ‖iteratedFDeriv Real i (fun s : Real => Real.exp (-s)) (q x)‖ <=
            Real.exp (-(q x)) := by
      intro i _hi
      exact exp_neg_iteratedFDeriv_norm_le i (q x)
    have hcomp :
        ‖iteratedFDeriv Real m ((fun s : Real => Real.exp (-s)) ∘ q) x‖ <=
          (m.factorial : Real) * Real.exp (-(q x)) * D ^ m := by
      have hExpSmooth :
          ContDiff Real ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun s : Real => Real.exp (-s)) := by
        rw [show (fun s : Real => Real.exp (-s)) =
            (fun s : Real => Real.exp ((-1 : Real) * s)) by
          ext s
          ring_nf]
        have hlin :
            ContDiff Real ((⊤ : ℕ∞) : WithTop ℕ∞)
              (fun s : Real => (-1 : Real) * s) := by
          fun_prop
        exact Real.contDiff_exp.comp hlin
      exact norm_iteratedFDeriv_comp_le
        (g := fun s : Real => Real.exp (-s)) (f := q)
        hExpSmooth hq_smooth (by exact_mod_cast le_top) x hExp_bound hD_bound
    have hq_lower : b * ‖x‖ ^ 2 <= q x := by
      have hlin := hc x
      have hsq :
          (c * ‖x‖) ^ 2 <= ‖Matrix.toEuclideanLin A.matrix x‖ ^ 2 := by
        exact sq_le_sq.mpr (by
          rw [abs_of_nonneg (by positivity : 0 <= c * ‖x‖),
            abs_of_nonneg (norm_nonneg _)]
          exact hlin)
      calc
        b * ‖x‖ ^ 2 = (c * ‖x‖) ^ 2 := by
          dsimp [b]
          ring
        _ <= ‖Matrix.toEuclideanLin A.matrix x‖ ^ 2 := hsq
        _ = q x := by
          dsimp [q]
          rw [← real_inner_self_eq_norm_sq]
    have hexp_le : Real.exp (-(q x)) <= Real.exp (-b * ‖x‖ ^ 2) := by
      exact Real.exp_le_exp.mpr (by linarith)
    have htail := hB ‖x‖ (norm_nonneg x)
    have hnonneg_poly : 0 <= ‖x‖ ^ k * (1 + ‖x‖) ^ (ell * m) := by positivity
    have hmain :
        ‖x‖ ^ k * ‖iteratedFDeriv Real m ((fun s : Real => Real.exp (-s)) ∘ q) x‖ <=
          (m.factorial : Real) * (Cq + 1) ^ m * B := by
      calc
        ‖x‖ ^ k *
            ‖iteratedFDeriv Real m ((fun s : Real => Real.exp (-s)) ∘ q) x‖
            <= ‖x‖ ^ k * ((m.factorial : Real) * Real.exp (-(q x)) * D ^ m) := by
              gcongr
        _ = (m.factorial : Real) * (Cq + 1) ^ m *
              (‖x‖ ^ k * (1 + ‖x‖) ^ (ell * m) * Real.exp (-(q x))) := by
              dsimp [D]
              rw [mul_pow, pow_mul]
              ring
        _ <= (m.factorial : Real) * (Cq + 1) ^ m *
              (‖x‖ ^ k * (1 + ‖x‖) ^ (ell * m) *
                Real.exp (-b * ‖x‖ ^ 2)) := by
              gcongr
        _ <= (m.factorial : Real) * (Cq + 1) ^ m * B := by
              gcongr
    simpa [q, Function.comp_def] using hmain

private lemma gaussianSchwartz_apply
    (n : Nat) (A : LatticeBasis n) (x : RealEuclideanSpace n) :
    gaussianSchwartz n A x = Real.exp (-(matrixNormSq n A x)) := by
  change Real.exp
      (-(inner Real (Matrix.toEuclideanLin A.matrix x) (Matrix.toEuclideanLin A.matrix x))) =
    Real.exp (-(matrixNormSq n A x))
  rw [matrixNormSq_eq_inner]

private noncomputable def gaussianSample
    (n : Nat) (A : LatticeBasis n) (R : Real) (u : RealEuclideanSpace n)
    (k : Fin n -> Int) : Real :=
  Real.exp (-(matrixNormSq n A ((R⁻¹ : Real) • (gaussianIntegerPoint n k - u)) / 2))

private noncomputable def gaussianRawFunction
    (n : Nat) (A : LatticeBasis n) (R : Real) (u : RealEuclideanSpace n) :
    (Fin n -> Int) -> Real :=
  gaussianSample n A R u

private lemma gaussianRawFunction_translate_center
    (n : Nat) (A : LatticeBasis n) (R : Real)
    (u : RealEuclideanSpace n) (a k : Fin n -> Int) :
    gaussianRawFunction n A R (u + gaussianIntegerPoint n a) k =
      gaussianRawFunction n A R u (k - a) := by
  unfold gaussianRawFunction gaussianSample
  congr 1
  congr 1
  have hpoint := gaussianIntegerPoint_sub n k a
  rw [hpoint]
  abel_nf

private noncomputable def gaussianRawL2Vector
    (n : Nat) (A : LatticeBasis n) (R : Real) (u : RealEuclideanSpace n)
    (hmem : Memℓp (gaussianRawFunction n A R u) (2 : ℝ≥0∞)) :
    gaussianL2Space n :=
  ⟨gaussianRawFunction n A R u, hmem⟩

private def gaussianRawAdmissible
    (n : Nat) (A : LatticeBasis n) (R : Real) (u : RealEuclideanSpace n) : Prop :=
  ∃ hmem : Memℓp (gaussianRawFunction n A R u) (2 : ℝ≥0∞),
    gaussianRawL2Vector n A R u hmem ≠ 0

private noncomputable def gaussianRawNorm
    (n : Nat) (A : LatticeBasis n) (R : Real) (u : RealEuclideanSpace n)
    (hmem : Memℓp (gaussianRawFunction n A R u) (2 : ℝ≥0∞)) : Real :=
  ‖gaussianRawL2Vector n A R u hmem‖

private noncomputable def gaussianRawL2Inner
    (n : Nat) (A : LatticeBasis n) (R : Real) (u w : RealEuclideanSpace n)
    (hu : Memℓp (gaussianRawFunction n A R u) (2 : ℝ≥0∞))
    (hw : Memℓp (gaussianRawFunction n A R w) (2 : ℝ≥0∞)) : Real :=
  inner Real (gaussianRawL2Vector n A R u hu) (gaussianRawL2Vector n A R w hw)

private noncomputable def gaussianRawInnerSum
    (n : Nat) (A : LatticeBasis n) (R : Real) (u w : RealEuclideanSpace n) : Real :=
  ∑' k : Fin n -> Int, gaussianRawFunction n A R u k * gaussianRawFunction n A R w k

private noncomputable def gaussianPeriodizedMass
    (n : Nat) (A : LatticeBasis n) (R : Real) (c : RealEuclideanSpace n) : Real :=
  (R ^ n)⁻¹ * ∑' k : Fin n -> Int, gaussianRawFunction n A R c k ^ 2

private lemma gaussianPeriodizedMass_eq_scaledLatticeSum
    (n : Nat) (A : LatticeBasis n) (R : Real) (c : RealEuclideanSpace n) :
    gaussianPeriodizedMass n A R c =
      scaledLatticeSum n (gaussianSchwartz n A) R c := by
  unfold gaussianPeriodizedMass scaledLatticeSum gaussianRawFunction gaussianSample
  congr 1
  congr with k
  rw [gaussianSchwartz_apply]
  change
    Real.exp (-(matrixNormSq n A (R⁻¹ • (gaussianIntegerPoint n k - c)) / 2)) ^ 2 =
      Real.exp (-(matrixNormSq n A (R⁻¹ • (gaussianIntegerPoint n k - c))))
  rw [sq, ← Real.exp_add]
  congr 1
  ring

private noncomputable def gaussianCorrelationCenter
    {n : Nat} (u w : RealEuclideanSpace n) : RealEuclideanSpace n :=
  ((2 : Real)⁻¹) • (u + w)

private noncomputable def gaussianCorrelationKernel
    (n : Nat) (A : LatticeBasis n) (R : Real) (u w : RealEuclideanSpace n) : Real :=
  Real.exp (-(matrixNormSq n A (u - w)) / (4 * R ^ 2))

private lemma gaussianRawFunction_mul_eq_kernel_mul_center_sq
    (n : Nat) (A : LatticeBasis n) (R : Real) (u w : RealEuclideanSpace n)
    (k : Fin n -> Int) :
    gaussianRawFunction n A R u k * gaussianRawFunction n A R w k =
      gaussianCorrelationKernel n A R u w *
        gaussianRawFunction n A R (gaussianCorrelationCenter u w) k ^ 2 := by
  let v : RealEuclideanSpace n := gaussianIntegerPoint n k
  let z : RealEuclideanSpace n := R⁻¹ • (v - gaussianCorrelationCenter u w)
  let d : RealEuclideanSpace n := R⁻¹ • (((2 : Real)⁻¹) • (u - w))
  have hu_arg : R⁻¹ • (v - u) = z - d := by
    dsimp [z, d, gaussianCorrelationCenter]
    module
  have hw_arg : R⁻¹ • (v - w) = z + d := by
    dsimp [z, d, gaussianCorrelationCenter]
    module
  have hd :
      matrixNormSq n A d = matrixNormSq n A (u - w) / (4 * R ^ 2) := by
    dsimp [d]
    rw [matrixNormSq_smul, matrixNormSq_smul]
    by_cases hR : R = 0
    · subst R
      simp
    · field_simp [hR]
      ring
  have hquad :
      matrixNormSq n A (R⁻¹ • (v - u)) / 2 +
          matrixNormSq n A (R⁻¹ • (v - w)) / 2 =
        matrixNormSq n A (R⁻¹ • (v - gaussianCorrelationCenter u w)) +
          matrixNormSq n A (u - w) / (4 * R ^ 2) := by
    rw [hu_arg, hw_arg, matrixNormSq_sub_add_half, hd]
  dsimp [v] at hquad
  unfold gaussianRawFunction gaussianSample gaussianCorrelationKernel
  rw [show
      Real.exp
          (-(matrixNormSq n A
            (R⁻¹ • (gaussianIntegerPoint n k - gaussianCorrelationCenter u w)) / 2)) ^ 2 =
        Real.exp
          (-(matrixNormSq n A
            (R⁻¹ • (gaussianIntegerPoint n k - gaussianCorrelationCenter u w)))) by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  calc
    -(matrixNormSq n A (R⁻¹ • (gaussianIntegerPoint n k - u)) / 2) +
        -(matrixNormSq n A (R⁻¹ • (gaussianIntegerPoint n k - w)) / 2)
        = -(matrixNormSq n A (R⁻¹ • (gaussianIntegerPoint n k - u)) / 2 +
            matrixNormSq n A (R⁻¹ • (gaussianIntegerPoint n k - w)) / 2) := by
          ring
    _ = -(matrixNormSq n A
          (R⁻¹ • (gaussianIntegerPoint n k - gaussianCorrelationCenter u w)) +
            matrixNormSq n A (u - w) / (4 * R ^ 2)) := by
          rw [hquad]
    _ = -matrixNormSq n A (u - w) / (4 * R ^ 2) +
          -matrixNormSq n A
            (R⁻¹ • (gaussianIntegerPoint n k - gaussianCorrelationCenter u w)) := by
          ring

private def gaussianCompletedSquareFormula
    (n : Nat) (A : LatticeBasis n) (R : Real) (u w : RealEuclideanSpace n) : Prop :=
  gaussianRawInnerSum n A R u w =
    gaussianCorrelationKernel n A R u w *
      (R ^ n * gaussianPeriodizedMass n A R (gaussianCorrelationCenter u w))

private lemma gaussianCompletedSquareFormula_of_ne_zero
    (n : Nat) (A : LatticeBasis n) {R : Real} (hR : R ≠ 0)
    (u w : RealEuclideanSpace n) :
    gaussianCompletedSquareFormula n A R u w := by
  unfold gaussianCompletedSquareFormula gaussianRawInnerSum gaussianPeriodizedMass
  calc
    (∑' k : Fin n -> Int, gaussianRawFunction n A R u k * gaussianRawFunction n A R w k)
        = ∑' k : Fin n -> Int,
            gaussianCorrelationKernel n A R u w *
              gaussianRawFunction n A R (gaussianCorrelationCenter u w) k ^ 2 := by
          congr with k
          exact gaussianRawFunction_mul_eq_kernel_mul_center_sq n A R u w k
    _ = gaussianCorrelationKernel n A R u w *
          ∑' k : Fin n -> Int,
            gaussianRawFunction n A R (gaussianCorrelationCenter u w) k ^ 2 := by
          rw [tsum_mul_left]
    _ = gaussianCorrelationKernel n A R u w *
          (R ^ n *
            ((R ^ n)⁻¹ *
              ∑' k : Fin n -> Int,
                gaussianRawFunction n A R (gaussianCorrelationCenter u w) k ^ 2)) := by
          field_simp [pow_ne_zero n hR]

private def gaussianPeriodizedMassAsymptotic
    (n : Nat) (A : LatticeBasis n) (N : Nat) : Prop :=
  ∃ μ C : Real, 0 < μ /\ 0 <= C /\
    forall R : Real, 1 <= R -> forall c : RealEuclideanSpace n,
      |gaussianPeriodizedMass n A R c - μ| <= C / R ^ N

private noncomputable def defaultGaussianL2Vector (n : Nat) : gaussianL2Space n :=
  lp.single (E := fun (_ : Fin n -> Int) => Real) 2 0 1

private lemma defaultGaussianL2Vector_norm (n : Nat) :
    ‖defaultGaussianL2Vector n‖ = 1 := by
  simp [defaultGaussianL2Vector]

private noncomputable def defaultGaussianSphereVector (n : Nat) : higherRankHilbertSphere n :=
  ⟨defaultGaussianL2Vector n, by
    rw [Metric.mem_sphere, dist_zero_right]
    exact defaultGaussianL2Vector_norm n⟩

private noncomputable def normalizedGaussianL2Vector
    (n : Nat) (f : gaussianL2Space n) (hf : f ≠ 0) : higherRankHilbertSphere n :=
  ⟨(‖f‖)⁻¹ • f, by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul]
    have hnorm : ‖f‖ ≠ 0 := norm_ne_zero_iff.mpr hf
    simp [hnorm]⟩

private noncomputable def gaussianNormalizedRawVector
    (n : Nat) (A : LatticeBasis n) (R : Real) (u : RealEuclideanSpace n)
    (h : gaussianRawAdmissible n A R u) : higherRankHilbertSphere n :=
  normalizedGaussianL2Vector n
    (gaussianRawL2Vector n A R u (Classical.choose h)) (Classical.choose_spec h)

private noncomputable def gaussianNormalizedRawCorrelation
    (n : Nat) (A : LatticeBasis n) (R : Real) (u w : RealEuclideanSpace n)
    (hu : gaussianRawAdmissible n A R u) (hw : gaussianRawAdmissible n A R w) : Real :=
  higherRankRepresentativeInner n (gaussianNormalizedRawVector n A R u hu)
    (gaussianNormalizedRawVector n A R w hw)

/-- The normalized Gaussian lattice vector, viewed as a point of the quotient. -/
noncomputable def gaussianLatticeVector
    (n : Nat) (A : LatticeBasis n) (R : Real) (u : RealEuclideanSpace n) :
    higherRankHilbertSphere n := by
  classical
  exact
    if h : gaussianRawAdmissible n A R u then
      gaussianNormalizedRawVector n A R u h
    else
      defaultGaussianSphereVector n

private lemma gaussianLatticeVector_of_admissible
    (n : Nat) (A : LatticeBasis n) (R : Real) (u : RealEuclideanSpace n)
    (h : gaussianRawAdmissible n A R u) :
    gaussianLatticeVector n A R u = gaussianNormalizedRawVector n A R u h := by
  simp [gaussianLatticeVector, h]

private lemma gaussianRawL2Vector_ne_zero
    (n : Nat) (A : LatticeBasis n) (R : Real) (u : RealEuclideanSpace n)
    (hmem : Memℓp (gaussianRawFunction n A R u) (2 : ℝ≥0∞)) :
    gaussianRawL2Vector n A R u hmem ≠ 0 := by
  intro hzero
  have hcoord : gaussianRawFunction n A R u 0 = (0 : Real) := by
    have hfun :=
      congrArg (fun f : gaussianL2Space n => (f : (Fin n -> Int) -> Real)) hzero
    simpa [gaussianRawL2Vector] using congrFun hfun 0
  have hpos : 0 < gaussianRawFunction n A R u 0 := by
    have h :=
      Real.exp_pos (-(matrixNormSq n A
        ((R⁻¹ : Real) • (gaussianIntegerPoint n 0 - u)) / 2))
    simpa [gaussianRawFunction, gaussianSample] using h
  exact (ne_of_gt hpos) hcoord

private theorem gaussianRawMemℓp_of_one_le
    (n : Nat) (A : LatticeBasis n) (R : Real) (u : RealEuclideanSpace n) (hR : 1 <= R) :
    Memℓp (gaussianRawFunction n A R u) (2 : ℝ≥0∞) := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  norm_num
  obtain ⟨c, hcpos, hc⟩ := matrixNormSq_lower_bound n A
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hRinv_pos : 0 < R⁻¹ := inv_pos.mpr hRpos
  let b : Real := (c * R⁻¹ / 2) ^ 2
  have hb : 0 < b := by
    dsimp [b]
    positivity
  refine Summable.of_norm_bounded_eventually
    (summable_exp_neg_mul_gaussianIntegerPoint_norm_sq (n := n) hb) ?_
  have hlarge :
      ∀ᶠ k : Fin n -> Int in Filter.cofinite,
        2 * ‖u‖ <= ‖gaussianIntegerPoint n k‖ :=
    (tendsto_gaussianIntegerPoint_norm_atTop n).eventually
      (Filter.eventually_ge_atTop (2 * ‖u‖))
  filter_upwards [hlarge] with k hk
  have hsample_nonneg : 0 <= gaussianRawFunction n A R u k := by
    exact (Real.exp_pos _).le
  have hsample_sq :
      ‖gaussianRawFunction n A R u k‖ ^ 2 =
        Real.exp (-(matrixNormSq n A
          ((R⁻¹ : Real) • (gaussianIntegerPoint n k - u)))) := by
    rw [Real.norm_of_nonneg hsample_nonneg]
    simp only [gaussianRawFunction, gaussianSample]
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hhalf : ‖gaussianIntegerPoint n k‖ / 2 <= ‖gaussianIntegerPoint n k - u‖ := by
    have htri :
        ‖gaussianIntegerPoint n k‖ <= ‖gaussianIntegerPoint n k - u‖ + ‖u‖ := by
      calc
        ‖gaussianIntegerPoint n k‖ =
            ‖(gaussianIntegerPoint n k - u) + u‖ := by
              congr 1
              abel
        _ <= ‖gaussianIntegerPoint n k - u‖ + ‖u‖ := norm_add_le _ _
    linarith
  have hmatrix_linear :
      c * R⁻¹ * ‖gaussianIntegerPoint n k - u‖ <=
        ‖Matrix.toEuclideanLin A.matrix
          ((R⁻¹ : Real) • (gaussianIntegerPoint n k - u))‖ := by
    have h := hc ((R⁻¹ : Real) • (gaussianIntegerPoint n k - u))
    rw [norm_smul, Real.norm_of_nonneg hRinv_pos.le] at h
    nlinarith [h]
  have hmatrix_lower :
      c * R⁻¹ / 2 * ‖gaussianIntegerPoint n k‖ <=
        ‖Matrix.toEuclideanLin A.matrix
          ((R⁻¹ : Real) • (gaussianIntegerPoint n k - u))‖ := by
    have hmul := mul_le_mul_of_nonneg_left hhalf (mul_nonneg hcpos.le hRinv_pos.le)
    nlinarith [hmatrix_linear, hmul]
  have hmatrix_lower_sq :
      b * ‖gaussianIntegerPoint n k‖ ^ 2 <=
        matrixNormSq n A ((R⁻¹ : Real) • (gaussianIntegerPoint n k - u)) := by
    dsimp [b, matrixNormSq]
    have hleft_nonneg : 0 <= c * R⁻¹ / 2 * ‖gaussianIntegerPoint n k‖ := by
      positivity
    have habs :
        |c * R⁻¹ / 2 * ‖gaussianIntegerPoint n k‖| <=
          |‖Matrix.toEuclideanLin A.matrix
            ((R⁻¹ : Real) • (gaussianIntegerPoint n k - u))‖| := by
      rw [abs_of_nonneg hleft_nonneg, abs_of_nonneg (norm_nonneg _)]
      exact hmatrix_lower
    calc
      (c * R⁻¹ / 2) ^ 2 * ‖gaussianIntegerPoint n k‖ ^ 2 =
          (c * R⁻¹ / 2 * ‖gaussianIntegerPoint n k‖) ^ 2 := by ring
      _ <= ‖Matrix.toEuclideanLin A.matrix
            ((R⁻¹ : Real) • (gaussianIntegerPoint n k - u))‖ ^ 2 :=
          sq_le_sq.mpr habs
  have hexp :
      Real.exp (-(matrixNormSq n A
          ((R⁻¹ : Real) • (gaussianIntegerPoint n k - u)))) <=
        Real.exp (-b * ‖gaussianIntegerPoint n k‖ ^ 2) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hrawsq :
      ‖gaussianRawFunction n A R u k ^ 2‖ =
        ‖gaussianRawFunction n A R u k‖ ^ 2 := by
    rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg hsample_nonneg]
  rw [hrawsq, hsample_sq]
  exact hexp

private theorem gaussianRawAdmissible_of_one_le
    (n : Nat) (A : LatticeBasis n) (R : Real) (u : RealEuclideanSpace n) (hR : 1 <= R) :
    gaussianRawAdmissible n A R u := by
  let hmem := gaussianRawMemℓp_of_one_le n A R u hR
  exact ⟨hmem, gaussianRawL2Vector_ne_zero n A R u hmem⟩

private lemma gaussianRawL2Inner_eq_sum
    (n : Nat) (A : LatticeBasis n) (R : Real) (u w : RealEuclideanSpace n)
    (hu : Memℓp (gaussianRawFunction n A R u) (2 : ℝ≥0∞))
    (hw : Memℓp (gaussianRawFunction n A R w) (2 : ℝ≥0∞)) :
    gaussianRawL2Inner n A R u w hu hw = gaussianRawInnerSum n A R u w := by
  rw [gaussianRawL2Inner, gaussianRawInnerSum, gaussianRawL2Vector]
  rw [lp.inner_eq_tsum]
  congr with k
  change gaussianRawFunction n A R w k * gaussianRawFunction n A R u k =
    gaussianRawFunction n A R u k * gaussianRawFunction n A R w k
  ring

private lemma gaussianRawNorm_sq_eq_sum
    (n : Nat) (A : LatticeBasis n) (R : Real) (u : RealEuclideanSpace n)
    (hu : Memℓp (gaussianRawFunction n A R u) (2 : ℝ≥0∞)) :
    ‖gaussianRawL2Vector n A R u hu‖ ^ 2 =
      ∑' k : Fin n -> Int, gaussianRawFunction n A R u k ^ 2 := by
  have hpos : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  have hnorm :=
    lp.norm_rpow_eq_tsum (f := gaussianRawL2Vector n A R u hu) hpos
  change ‖gaussianRawL2Vector n A R u hu‖ ^ (2 : Real) =
      ∑' k : Fin n -> Int, ‖gaussianRawL2Vector n A R u hu k‖ ^ (2 : Real) at hnorm
  rw [show ‖gaussianRawL2Vector n A R u hu‖ ^ (2 : Real) =
      ‖gaussianRawL2Vector n A R u hu‖ ^ 2 by norm_num] at hnorm
  rw [hnorm]
  congr with k
  have hnonneg : 0 <= gaussianRawFunction n A R u k := by
    exact (Real.exp_pos _).le
  change ‖gaussianRawFunction n A R u k‖ ^ (2 : Real) =
    gaussianRawFunction n A R u k ^ 2
  rw [Real.norm_of_nonneg hnonneg]
  norm_num

private lemma gaussianRawL2Vector_norm_translate_center
    (n : Nat) (A : LatticeBasis n) (R : Real)
    (u : RealEuclideanSpace n) (a : Fin n -> Int)
    (hu : Memℓp (gaussianRawFunction n A R u) (2 : ℝ≥0∞))
    (hshift : Memℓp
      (gaussianRawFunction n A R (u + gaussianIntegerPoint n a)) (2 : ℝ≥0∞)) :
    ‖gaussianRawL2Vector n A R (u + gaussianIntegerPoint n a) hshift‖ =
      ‖gaussianRawL2Vector n A R u hu‖ := by
  have hsums :
      (∑' k : Fin n -> Int,
          gaussianRawFunction n A R (u + gaussianIntegerPoint n a) k ^ 2) =
        ∑' k : Fin n -> Int, gaussianRawFunction n A R u k ^ 2 := by
    calc
      (∑' k : Fin n -> Int,
          gaussianRawFunction n A R (u + gaussianIntegerPoint n a) k ^ 2)
          = ∑' k : Fin n -> Int, gaussianRawFunction n A R u (k - a) ^ 2 := by
              congr with k
              rw [gaussianRawFunction_translate_center]
      _ = ∑' k : Fin n -> Int, gaussianRawFunction n A R u k ^ 2 := by
              exact (Equiv.subRight a).tsum_eq
                (fun k : Fin n -> Int => gaussianRawFunction n A R u k ^ 2)
  have hsquare :
      ‖gaussianRawL2Vector n A R (u + gaussianIntegerPoint n a) hshift‖ ^ 2 =
        ‖gaussianRawL2Vector n A R u hu‖ ^ 2 := by
    rw [gaussianRawNorm_sq_eq_sum n A R (u + gaussianIntegerPoint n a) hshift,
      gaussianRawNorm_sq_eq_sum n A R u hu, hsums]
  have habs := (sq_eq_sq_iff_abs_eq_abs
    (‖gaussianRawL2Vector n A R (u + gaussianIntegerPoint n a) hshift‖)
    (‖gaussianRawL2Vector n A R u hu‖)).mp hsquare
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at habs

private lemma higherRankTranslation_gaussianLatticeVector
    (n : Nat) (A : LatticeBasis n) {R : Real} (hR : 1 <= R)
    (u : RealEuclideanSpace n) (a : Fin n -> Int) :
    higherRankTranslation n a (gaussianLatticeVector n A R u) =
      gaussianLatticeVector n A R (u + gaussianIntegerPoint n a) := by
  classical
  let hu : gaussianRawAdmissible n A R u := gaussianRawAdmissible_of_one_le n A R u hR
  let hshift : gaussianRawAdmissible n A R (u + gaussianIntegerPoint n a) :=
    gaussianRawAdmissible_of_one_le n A R (u + gaussianIntegerPoint n a) hR
  rw [gaussianLatticeVector_of_admissible n A R u hu,
    gaussianLatticeVector_of_admissible n A R (u + gaussianIntegerPoint n a) hshift]
  ext k
  have hnorm := gaussianRawL2Vector_norm_translate_center n A R u a
    (Classical.choose hu) (Classical.choose hshift)
  change (‖gaussianRawL2Vector n A R u (Classical.choose hu)‖)⁻¹ *
      gaussianRawFunction n A R u (k - a) =
    (‖gaussianRawL2Vector n A R (u + gaussianIntegerPoint n a)
        (Classical.choose hshift)‖)⁻¹ *
      gaussianRawFunction n A R (u + gaussianIntegerPoint n a) k
  rw [hnorm, gaussianRawFunction_translate_center]

private lemma gaussianRawNorm_sq_eq_Rpow_mul_mass
    (n : Nat) (A : LatticeBasis n) {R : Real} (hR : R ≠ 0)
    (u : RealEuclideanSpace n)
    (hu : Memℓp (gaussianRawFunction n A R u) (2 : ℝ≥0∞)) :
    ‖gaussianRawL2Vector n A R u hu‖ ^ 2 =
      R ^ n * gaussianPeriodizedMass n A R u := by
  rw [gaussianRawNorm_sq_eq_sum n A R u hu, gaussianPeriodizedMass]
  field_simp [pow_ne_zero n hR]

private lemma gaussianNormalizedRawCorrelation_eq_kernel_mul_raw_norm_factors
    (n : Nat) (A : LatticeBasis n) {R : Real} (hR : R ≠ 0)
    (u w : RealEuclideanSpace n)
    (hu : gaussianRawAdmissible n A R u) (hw : gaussianRawAdmissible n A R w) :
    gaussianNormalizedRawCorrelation n A R u w hu hw =
      gaussianCorrelationKernel n A R u w *
        (R ^ n * gaussianPeriodizedMass n A R (gaussianCorrelationCenter u w)) *
          ((‖gaussianRawL2Vector n A R u (Classical.choose hu)‖)⁻¹ *
            (‖gaussianRawL2Vector n A R w (Classical.choose hw)‖)⁻¹) := by
  let fu : gaussianL2Space n := gaussianRawL2Vector n A R u (Classical.choose hu)
  let fw : gaussianL2Space n := gaussianRawL2Vector n A R w (Classical.choose hw)
  have hinner :
      inner Real fu fw =
        gaussianCorrelationKernel n A R u w *
          (R ^ n * gaussianPeriodizedMass n A R (gaussianCorrelationCenter u w)) := by
    calc
      inner Real fu fw =
          gaussianRawL2Inner n A R u w (Classical.choose hu) (Classical.choose hw) := by
            rfl
      _ = gaussianRawInnerSum n A R u w :=
            gaussianRawL2Inner_eq_sum n A R u w (Classical.choose hu) (Classical.choose hw)
      _ = gaussianCorrelationKernel n A R u w *
          (R ^ n * gaussianPeriodizedMass n A R (gaussianCorrelationCenter u w)) :=
            gaussianCompletedSquareFormula_of_ne_zero n A hR u w
  unfold gaussianNormalizedRawCorrelation gaussianNormalizedRawVector normalizedGaussianL2Vector
    higherRankRepresentativeInner
  change inner Real ((‖fu‖)⁻¹ • fu) ((‖fw‖)⁻¹ • fw) =
    gaussianCorrelationKernel n A R u w *
      (R ^ n * gaussianPeriodizedMass n A R (gaussianCorrelationCenter u w)) *
        ((‖fu‖)⁻¹ * (‖fw‖)⁻¹)
  rw [inner_smul_left, inner_smul_right, hinner]
  simp
  ring

private lemma gaussianSchwartz_integral_pos
    (n : Nat) (A : LatticeBasis n) :
    0 < euclideanIntegral n (gaussianSchwartz n A) := by
  unfold euclideanIntegral
  refine MeasureTheory.integral_pos_of_integrable_nonneg_nonzero
    (x := (0 : RealEuclideanSpace n))
    (SchwartzMap.continuous (gaussianSchwartz n A))
    (SchwartzMap.integrable (gaussianSchwartz n A)) ?_ ?_
  · intro x
    rw [gaussianSchwartz_apply]
    exact (Real.exp_pos _).le
  · rw [gaussianSchwartz_apply]
    exact (Real.exp_pos _).ne'

private theorem gaussianPeriodizedMassAsymptotic_of_uniformSummationEstimate
    (n : Nat) (A : LatticeBasis n) (N : Nat) (hN : 1 <= N) :
    gaussianPeriodizedMassAsymptotic n A N := by
  obtain ⟨C, hC_nonneg, hC⟩ := uniformSummationEstimate n (gaussianSchwartz n A) N hN
  refine ⟨euclideanIntegral n (gaussianSchwartz n A), C,
    gaussianSchwartz_integral_pos n A, hC_nonneg, ?_⟩
  intro R hR c
  simpa [gaussianPeriodizedMass_eq_scaledLatticeSum n A R c] using hC R hR c

private lemma abs_sub_one_le_abs_sq_sub_one {a : Real} (ha : 0 <= a) :
    |a - 1| <= |a ^ 2 - 1| := by
  have hfactor : |a ^ 2 - 1| = |a - 1| * |a + 1| := by
    rw [show a ^ 2 - 1 = (a - 1) * (a + 1) by ring]
    rw [abs_mul]
  have hone : 1 <= |a + 1| := by
    rw [abs_of_nonneg]
    · linarith
    · linarith
  calc
    |a - 1| = |a - 1| * 1 := by ring
    _ <= |a - 1| * |a + 1| := by gcongr
    _ = |a ^ 2 - 1| := hfactor.symm

private lemma mass_ratio_sq_error_bound
    {μ C δ B pc pu pw : Real}
    (hμ : 0 < μ) (hC : 0 <= C) (hδ_nonneg : 0 <= δ) (hδC : δ <= C)
    (hB : 0 < B) (hpc_nonneg : 0 <= pc) (hpw_nonneg : 0 <= pw)
    (hpuB : B <= pu) (hpwB : B <= pw)
    (hpc : |pc - μ| <= δ) (hpu : |pu - μ| <= δ) (hpw : |pw - μ| <= δ) :
    |pc ^ 2 / (pu * pw) - 1| <= ((4 * μ + 2 * C) / B ^ 2) * δ := by
  have hpc_upper : pc <= μ + C := by
    have hle : pc - μ <= δ := le_trans (le_abs_self (pc - μ)) hpc
    linarith
  have hpw_upper : pw <= μ + C := by
    have hle : pw - μ <= δ := le_trans (le_abs_self (pw - μ)) hpw
    linarith
  have hpc_plus : |pc + μ| <= 2 * μ + C := by
    rw [abs_of_nonneg]
    · linarith
    · linarith
  have hμ_abs : |μ| = μ := abs_of_pos hμ
  have hpw_abs : |pw| = pw := abs_of_nonneg hpw_nonneg
  have hnum : |pc ^ 2 - pu * pw| <= (4 * μ + 2 * C) * δ := by
    have h1 : |(pc - μ) * (pc + μ)| <= δ * (2 * μ + C) := by
      rw [abs_mul]
      exact mul_le_mul hpc hpc_plus (abs_nonneg _) hδ_nonneg
    have h2 : |μ * (μ - pw)| <= μ * δ := by
      rw [abs_mul, hμ_abs]
      exact mul_le_mul_of_nonneg_left (by simpa [abs_sub_comm] using hpw) hμ.le
    have h3 : |pw * (μ - pu)| <= (μ + C) * δ := by
      rw [abs_mul, hpw_abs]
      exact mul_le_mul (by linarith) (by simpa [abs_sub_comm] using hpu)
        (abs_nonneg _) (by linarith)
    calc
      |pc ^ 2 - pu * pw|
          = |(pc - μ) * (pc + μ) + (μ * (μ - pw) + pw * (μ - pu))| := by
              congr 1
              ring
      _ <= |(pc - μ) * (pc + μ)| + |μ * (μ - pw) + pw * (μ - pu)| :=
            abs_add_le _ _
      _ <= |(pc - μ) * (pc + μ)| +
            (|μ * (μ - pw)| + |pw * (μ - pu)|) := by
              gcongr
              exact abs_add_le _ _
      _ <= δ * (2 * μ + C) + (μ * δ + (μ + C) * δ) := by
              gcongr
      _ = (4 * μ + 2 * C) * δ := by ring
  have hpu_pos : 0 < pu := lt_of_lt_of_le hB hpuB
  have hpw_pos : 0 < pw := lt_of_lt_of_le hB hpwB
  have hden_pos : 0 < pu * pw := mul_pos hpu_pos hpw_pos
  have hBsq_pos : 0 < B ^ 2 := sq_pos_of_pos hB
  have hden_ge : B ^ 2 <= pu * pw := by nlinarith
  have hnum_nonneg : 0 <= |pc ^ 2 - pu * pw| := abs_nonneg _
  have hratio :
      |pc ^ 2 / (pu * pw) - 1| = |pc ^ 2 - pu * pw| / (pu * pw) := by
    rw [show pc ^ 2 / (pu * pw) - 1 = (pc ^ 2 - pu * pw) / (pu * pw) by
      field_simp [hden_pos.ne']]
    rw [abs_div]
    rw [abs_of_pos hden_pos]
  calc
    |pc ^ 2 / (pu * pw) - 1| = |pc ^ 2 - pu * pw| / (pu * pw) := hratio
    _ <= |pc ^ 2 - pu * pw| / B ^ 2 := by
          exact div_le_div_of_nonneg_left hnum_nonneg hBsq_pos hden_ge
    _ <= ((4 * μ + 2 * C) * δ) / B ^ 2 := by
          exact div_le_div_of_nonneg_right hnum (sq_nonneg B)
    _ = ((4 * μ + 2 * C) / B ^ 2) * δ := by ring

private lemma matrixNormSq_upper_bound
    (n : Nat) (A : LatticeBasis n) :
    ∃ L : Real, 0 <= L ∧
      ∀ x : RealEuclideanSpace n, matrixNormSq n A x <= L * ‖x‖ ^ 2 := by
  obtain ⟨C, hCpos, hC⟩ :=
    SemilinearMapClass.bound_of_continuous
      (Matrix.toEuclideanLin A.matrix : RealEuclideanSpace n →ₗ[Real] RealEuclideanSpace n)
      (by fun_prop)
  refine ⟨C ^ 2, sq_nonneg C, ?_⟩
  intro x
  have hx := hC x
  have hsquare :
      ‖Matrix.toEuclideanLin A.matrix x‖ ^ 2 <= (C * ‖x‖) ^ 2 := by
    exact sq_le_sq.mpr (by
      rw [abs_of_nonneg (norm_nonneg _),
        abs_of_nonneg (mul_nonneg hCpos.le (norm_nonneg _))]
      exact hx)
  calc
    matrixNormSq n A x = ‖Matrix.toEuclideanLin A.matrix x‖ ^ 2 := rfl
    _ <= (C * ‖x‖) ^ 2 := hsquare
    _ = C ^ 2 * ‖x‖ ^ 2 := by ring

private lemma exists_gaussianIntegerPoint_norm_sub_sq_le (n : Nat)
    (c : RealEuclideanSpace n) :
    ∃ k : Fin n -> Int, ‖gaussianIntegerPoint n k - c‖ ^ 2 <= (n : Real) := by
  classical
  have hcoord :
      ∀ i : Fin n, ∃! z : Int,
        c i + z • (1 : Real) ∈ Set.Ioc (0 : Real) (0 + 1) := by
    intro i
    exact existsUnique_add_zsmul_mem_Ioc zero_lt_one (c i) 0
  choose q hq _ using hcoord
  refine ⟨-q, ?_⟩
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    ∑ i : Fin n, ((gaussianIntegerPoint n (-q) - c) i) ^ 2
        <= ∑ _i : Fin n, (1 : Real) := by
          refine Finset.sum_le_sum ?_
          intro i _
          have hi := hq i
          have hle : -(1 : Real) <= (gaussianIntegerPoint n (-q) - c) i ∧
              (gaussianIntegerPoint n (-q) - c) i <= 1 := by
            constructor
            · change -(1 : Real) <= ((-(q i) : Int) : Real) - c i
              have hi_le : c i + (q i : Real) <= 1 := by simpa using hi.2
              rw [Int.cast_neg]
              linarith
            · change ((-(q i) : Int) : Real) - c i <= 1
              have hi_pos : 0 < c i + (q i : Real) := by simpa using hi.1
              rw [Int.cast_neg]
              linarith
          have habs : |(gaussianIntegerPoint n (-q) - c) i| <= 1 := by
            rw [abs_le]
            exact hle
          have habs' : |(gaussianIntegerPoint n (-q) - c) i| <= |(1 : Real)| := by
            simpa using habs
          have hsquare := sq_le_sq.mpr habs'
          simpa using hsquare
    _ = (n : Real) := by simp

private lemma summable_gaussianRawFunction_sq_of_one_le
    (n : Nat) (A : LatticeBasis n) {R : Real} (u : RealEuclideanSpace n)
    (hR : 1 <= R) :
    Summable fun k : Fin n -> Int => gaussianRawFunction n A R u k ^ 2 := by
  have hmem := gaussianRawMemℓp_of_one_le n A R u hR
  have hs := hmem.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  convert hs using 1
  ext k
  have hnonneg : 0 <= gaussianRawFunction n A R u k := (Real.exp_pos _).le
  rw [Real.norm_of_nonneg hnonneg]
  norm_num

private lemma gaussianRawFunction_sq_eq_exp
    (n : Nat) (A : LatticeBasis n) (R : Real) (u : RealEuclideanSpace n)
    (k : Fin n -> Int) :
    gaussianRawFunction n A R u k ^ 2 =
      Real.exp (-(matrixNormSq n A ((R⁻¹ : Real) • (gaussianIntegerPoint n k - u)))) := by
  unfold gaussianRawFunction gaussianSample
  rw [sq, ← Real.exp_add]
  congr 1
  ring

private lemma gaussianPeriodizedMass_pos
    (n : Nat) (A : LatticeBasis n) {R : Real} (hR : 1 <= R)
    (c : RealEuclideanSpace n) :
    0 < gaussianPeriodizedMass n A R c := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hsum : Summable fun k : Fin n -> Int => gaussianRawFunction n A R c k ^ 2 :=
    summable_gaussianRawFunction_sq_of_one_le n A c hR
  have htsum_pos :
      0 < ∑' k : Fin n -> Int, gaussianRawFunction n A R c k ^ 2 := by
    refine hsum.tsum_pos (fun k => sq_nonneg _) 0 ?_
    rw [gaussianRawFunction_sq_eq_exp]
    exact Real.exp_pos _
  unfold gaussianPeriodizedMass
  exact mul_pos (inv_pos.mpr (pow_pos hRpos n)) htsum_pos

private lemma gaussianPeriodizedMass_upper_of_asymptotic
    {n N : Nat} {A : LatticeBasis n} {μ C R : Real}
    (hC_nonneg : 0 <= C) (hR : 1 <= R)
    (hMass : ∀ c : RealEuclideanSpace n,
      |gaussianPeriodizedMass n A R c - μ| <= C / R ^ N)
    (c : RealEuclideanSpace n) :
    gaussianPeriodizedMass n A R c <= μ + C := by
  have hRN_ge_one : 1 <= R ^ N := one_le_pow₀ hR
  have hdiv_le : C / R ^ N <= C := by
    calc
      C / R ^ N = C * (R ^ N)⁻¹ := by ring
      _ <= C * 1 := by
            gcongr
            exact inv_le_one_of_one_le₀ hRN_ge_one
      _ = C := by ring
  have hle : gaussianPeriodizedMass n A R c - μ <= C / R ^ N :=
    le_trans (le_abs_self _) (hMass c)
  linarith

private lemma gaussianPeriodizedMass_lower_of_le
    (n : Nat) (A : LatticeBasis n) {R S L : Real}
    (hL_nonneg : 0 <= L) (hL : ∀ x : RealEuclideanSpace n, matrixNormSq n A x <= L * ‖x‖ ^ 2)
    (hS : 1 <= S) (hR : 1 <= R) (hRS : R <= S)
    (c : RealEuclideanSpace n) :
    (S ^ n)⁻¹ * Real.exp (-(L * (n : Real))) <= gaussianPeriodizedMass n A R c := by
  obtain ⟨k, hk⟩ := exists_gaussianIntegerPoint_norm_sub_sq_le n c
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have hRinv_nonneg : 0 <= R⁻¹ := inv_nonneg.mpr hRpos.le
  have hRinv_le_one : R⁻¹ <= 1 := inv_le_one_of_one_le₀ hR
  have hnorm_scaled :
      ‖(R⁻¹ : Real) • (gaussianIntegerPoint n k - c)‖ ^ 2 <= (n : Real) := by
    rw [norm_smul, Real.norm_of_nonneg hRinv_nonneg, mul_pow]
    calc
      R⁻¹ ^ 2 * ‖gaussianIntegerPoint n k - c‖ ^ 2
          <= 1 ^ 2 * (n : Real) := by
            refine mul_le_mul ?_ hk ?_ ?_
            · exact pow_le_pow_left₀ hRinv_nonneg hRinv_le_one 2
            · exact sq_nonneg _
            · norm_num
      _ = (n : Real) := by ring
  have hquad :
      matrixNormSq n A ((R⁻¹ : Real) • (gaussianIntegerPoint n k - c)) <=
        L * (n : Real) := by
    calc
      matrixNormSq n A ((R⁻¹ : Real) • (gaussianIntegerPoint n k - c))
          <= L * ‖(R⁻¹ : Real) • (gaussianIntegerPoint n k - c)‖ ^ 2 :=
            hL _
      _ <= L * (n : Real) := by gcongr
  have hterm_lower :
      Real.exp (-(L * (n : Real))) <= gaussianRawFunction n A R c k ^ 2 := by
    rw [gaussianRawFunction_sq_eq_exp]
    exact Real.exp_le_exp.mpr (by linarith)
  have hsum : Summable fun j : Fin n -> Int => gaussianRawFunction n A R c j ^ 2 :=
    summable_gaussianRawFunction_sq_of_one_le n A c hR
  have hterm_le_tsum :
      gaussianRawFunction n A R c k ^ 2 <=
        ∑' j : Fin n -> Int, gaussianRawFunction n A R c j ^ 2 := by
    have hpartial :=
      Summable.sum_le_tsum (s := {k})
        (f := fun j : Fin n -> Int => gaussianRawFunction n A R c j ^ 2)
        (fun _ _ => sq_nonneg _) hsum
    simpa using hpartial
  have hSpow_inv_le_Rpow_inv : (S ^ n)⁻¹ <= (R ^ n)⁻¹ := by
    have hpow_le : R ^ n <= S ^ n := pow_le_pow_left₀ hRpos.le hRS n
    exact inv_anti₀ (pow_pos hRpos n) hpow_le
  have hleft_nonneg : 0 <= Real.exp (-(L * (n : Real))) := (Real.exp_pos _).le
  unfold gaussianPeriodizedMass
  calc
    (S ^ n)⁻¹ * Real.exp (-(L * (n : Real)))
        <= (R ^ n)⁻¹ * Real.exp (-(L * (n : Real))) := by gcongr
    _ <= (R ^ n)⁻¹ * gaussianRawFunction n A R c k ^ 2 := by gcongr
    _ <= (R ^ n)⁻¹ *
          (∑' j : Fin n -> Int, gaussianRawFunction n A R c j ^ 2) := by gcongr

private lemma gaussianPeriodizedMass_uniform_lower_of_asymptotic
    (n : Nat) (A : LatticeBasis n) (N : Nat) (hN : 1 <= N)
    (hMass : gaussianPeriodizedMassAsymptotic n A N) :
    ∃ B : Real, 0 < B ∧
      ∀ R : Real, 1 <= R -> ∀ c : RealEuclideanSpace n,
        B <= gaussianPeriodizedMass n A R c := by
  rcases hMass with ⟨μ, C, hμ, hC_nonneg, hErr⟩
  obtain ⟨L, hL_nonneg, hL⟩ := matrixNormSq_upper_bound n A
  let S : Real := max 1 (2 * C / μ + 1)
  have hS_one : 1 <= S := le_max_left _ _
  have hS_pos : 0 < S := lt_of_lt_of_le zero_lt_one hS_one
  let Bsmall : Real := (S ^ n)⁻¹ * Real.exp (-(L * (n : Real)))
  let Blarge : Real := μ / 2
  refine ⟨min Bsmall Blarge, ?_, ?_⟩
  · have hBsmall : 0 < Bsmall := by
      dsimp [Bsmall]
      exact mul_pos (inv_pos.mpr (pow_pos hS_pos n)) (Real.exp_pos _)
    have hBlarge : 0 < Blarge := by
      dsimp [Blarge]
      linarith
    exact lt_min hBsmall hBlarge
  intro R hR c
  by_cases hRS : R <= S
  · exact (min_le_left Bsmall Blarge).trans
      (gaussianPeriodizedMass_lower_of_le n A hL_nonneg hL hS_one hR hRS c)
  · have hSR : S <= R := le_of_not_ge hRS
    have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
    have hS_ge_large : 2 * C / μ + 1 <= S := le_max_right _ _
    have hlarge : 2 * C / μ <= R := by linarith
    have htwoC_le : 2 * C <= μ * R := by
      rw [div_le_iff₀ hμ] at hlarge
      linarith
    have hR_le_RN : R <= R ^ N := by
      exact le_self_pow₀ hR (Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hN))
    have hC_div_R : C / R <= μ / 2 := by
      rw [div_le_iff₀ hRpos]
      nlinarith
    have hC_div_RN : C / R ^ N <= μ / 2 := by
      exact (div_le_div_of_nonneg_left hC_nonneg hRpos hR_le_RN).trans hC_div_R
    have hleft :
        μ - gaussianPeriodizedMass n A R c <= C / R ^ N := by
      have habs : μ - gaussianPeriodizedMass n A R c <=
          |gaussianPeriodizedMass n A R c - μ| := by
        rw [show μ - gaussianPeriodizedMass n A R c =
            -(gaussianPeriodizedMass n A R c - μ) by ring]
        exact neg_le_abs _
      exact habs.trans (hErr R hR c)
    have hlarge_lower : Blarge <= gaussianPeriodizedMass n A R c := by
      dsimp [Blarge]
      linarith
    exact (min_le_right Bsmall Blarge).trans hlarge_lower

private theorem gaussianNormalizedRawCorrelationAsymptotic_of_periodizedMass
    (n : Nat) (A : LatticeBasis n) (N : Nat) (hN : 1 <= N)
    (hMass : gaussianPeriodizedMassAsymptotic n A N) :
    exists C : Real, 0 <= C /\
      forall R : Real, forall hR : 1 <= R, forall u w : RealEuclideanSpace n,
        exists theta : Real,
          |theta| <= C / R ^ N /\
            gaussianNormalizedRawCorrelation n A R u w
                (gaussianRawAdmissible_of_one_le n A R u hR)
                (gaussianRawAdmissible_of_one_le n A R w hR) =
              gaussianCorrelationKernel n A R u w * (1 + theta) := by
  classical
  obtain ⟨B, hB_pos, hB_lower⟩ :=
    gaussianPeriodizedMass_uniform_lower_of_asymptotic n A N hN hMass
  rcases hMass with ⟨μ, Cmass, hμ_pos, hCmass_nonneg, hErr⟩
  let Ccorr : Real := ((4 * μ + 2 * Cmass) / B ^ 2) * Cmass
  have hcoeff_nonneg : 0 <= (4 * μ + 2 * Cmass) / B ^ 2 := by
    exact div_nonneg (by nlinarith) (sq_nonneg B)
  have hCcorr_nonneg : 0 <= Ccorr := by
    dsimp [Ccorr]
    exact mul_nonneg hcoeff_nonneg hCmass_nonneg
  refine ⟨Ccorr, hCcorr_nonneg, ?_⟩
  intro R hR u w
  let hu : gaussianRawAdmissible n A R u := gaussianRawAdmissible_of_one_le n A R u hR
  let hw : gaussianRawAdmissible n A R w := gaussianRawAdmissible_of_one_le n A R w hR
  let fu : gaussianL2Space n := gaussianRawL2Vector n A R u (Classical.choose hu)
  let fw : gaussianL2Space n := gaussianRawL2Vector n A R w (Classical.choose hw)
  let pc : Real := gaussianPeriodizedMass n A R (gaussianCorrelationCenter u w)
  let pu : Real := gaussianPeriodizedMass n A R u
  let pw : Real := gaussianPeriodizedMass n A R w
  let α : Real := (R ^ n * pc) * ((‖fu‖)⁻¹ * (‖fw‖)⁻¹)
  refine ⟨α - 1, ?_, ?_⟩
  · have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
    have hR_ne : R ≠ 0 := hRpos.ne'
    have hRN_pos : 0 < R ^ N := pow_pos hRpos N
    have hdelta_nonneg : 0 <= Cmass / R ^ N := div_nonneg hCmass_nonneg hRN_pos.le
    have hRN_ge_one : 1 <= R ^ N := one_le_pow₀ hR
    have hdelta_le_C : Cmass / R ^ N <= Cmass := by
      calc
        Cmass / R ^ N = Cmass * (R ^ N)⁻¹ := by ring
        _ <= Cmass * 1 := by
              gcongr
              exact inv_le_one_of_one_le₀ hRN_ge_one
        _ = Cmass := by ring
    have hpc_err : |pc - μ| <= Cmass / R ^ N := by
      dsimp [pc]
      exact hErr R hR (gaussianCorrelationCenter u w)
    have hpu_err : |pu - μ| <= Cmass / R ^ N := by
      dsimp [pu]
      exact hErr R hR u
    have hpw_err : |pw - μ| <= Cmass / R ^ N := by
      dsimp [pw]
      exact hErr R hR w
    have hpc_nonneg : 0 <= pc := by
      dsimp [pc]
      exact (gaussianPeriodizedMass_pos n A hR (gaussianCorrelationCenter u w)).le
    have hpw_nonneg : 0 <= pw := by
      dsimp [pw]
      exact (gaussianPeriodizedMass_pos n A hR w).le
    have hpu_lower : B <= pu := by
      dsimp [pu]
      exact hB_lower R hR u
    have hpw_lower : B <= pw := by
      dsimp [pw]
      exact hB_lower R hR w
    have hratio_sq :
        |pc ^ 2 / (pu * pw) - 1| <=
          ((4 * μ + 2 * Cmass) / B ^ 2) * (Cmass / R ^ N) :=
      mass_ratio_sq_error_bound hμ_pos hCmass_nonneg hdelta_nonneg hdelta_le_C
        hB_pos hpc_nonneg hpw_nonneg hpu_lower hpw_lower hpc_err hpu_err hpw_err
    have hfu_ne : fu ≠ 0 := by
      dsimp [fu]
      exact Classical.choose_spec hu
    have hfw_ne : fw ≠ 0 := by
      dsimp [fw]
      exact Classical.choose_spec hw
    have hfu_norm_pos : 0 < ‖fu‖ := norm_pos_iff.mpr hfu_ne
    have hfw_norm_pos : 0 < ‖fw‖ := norm_pos_iff.mpr hfw_ne
    have hpu_pos : 0 < pu := lt_of_lt_of_le hB_pos hpu_lower
    have hpw_pos : 0 < pw := lt_of_lt_of_le hB_pos hpw_lower
    have hfu_sq : ‖fu‖ ^ 2 = R ^ n * pu := by
      dsimp [fu, pu]
      exact gaussianRawNorm_sq_eq_Rpow_mul_mass n A hR_ne u (Classical.choose hu)
    have hfw_sq : ‖fw‖ ^ 2 = R ^ n * pw := by
      dsimp [fw, pw]
      exact gaussianRawNorm_sq_eq_Rpow_mul_mass n A hR_ne w (Classical.choose hw)
    have halpha_sq : α ^ 2 = pc ^ 2 / (pu * pw) := by
      dsimp [α]
      rw [mul_pow, mul_pow, mul_pow, inv_pow, inv_pow, hfu_sq, hfw_sq]
      field_simp [pow_ne_zero n hR_ne, hfu_norm_pos.ne', hfw_norm_pos.ne',
        hpu_pos.ne', hpw_pos.ne']
    have halpha_nonneg : 0 <= α := by
      dsimp [α]
      positivity
    calc
      |α - 1| <= |α ^ 2 - 1| := abs_sub_one_le_abs_sq_sub_one halpha_nonneg
      _ = |pc ^ 2 / (pu * pw) - 1| := by rw [halpha_sq]
      _ <= ((4 * μ + 2 * Cmass) / B ^ 2) * (Cmass / R ^ N) := hratio_sq
      _ = Ccorr / R ^ N := by
            dsimp [Ccorr]
            field_simp [hRN_pos.ne']
  · have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
    have hcorr :=
      gaussianNormalizedRawCorrelation_eq_kernel_mul_raw_norm_factors n A hRpos.ne' u w hu hw
    change gaussianNormalizedRawCorrelation n A R u w hu hw =
      gaussianCorrelationKernel n A R u w * (1 + (α - 1))
    rw [hcorr]
    dsimp [α, hu, hw, fu, pc]
    ring

private theorem gaussianNormalizedRawCorrelationAsymptotic
    (n : Nat) (A : LatticeBasis n) (N : Nat) (hN : 1 <= N) :
    exists C : Real, 0 <= C /\
      forall R : Real, forall hR : 1 <= R, forall u w : RealEuclideanSpace n,
        exists theta : Real,
          |theta| <= C / R ^ N /\
            gaussianNormalizedRawCorrelation n A R u w
                (gaussianRawAdmissible_of_one_le n A R u hR)
                (gaussianRawAdmissible_of_one_le n A R w hR) =
              gaussianCorrelationKernel n A R u w * (1 + theta) := by
  exact gaussianNormalizedRawCorrelationAsymptotic_of_periodizedMass n A N hN
    (gaussianPeriodizedMassAsymptotic_of_uniformSummationEstimate n A N hN)

/-- The quotient point represented by the normalized Gaussian lattice vector. -/
noncomputable def gaussianQuotientPoint
    (n : Nat) (A : LatticeBasis n) (R : Real) (u : RealEuclideanSpace n) :
    higherRankSphereQuotient n := by
  exact higherRankQuotientMk n (gaussianLatticeVector n A R u)

/-- The Gaussian representative inner-product asymptotic, uniformly in the torus parameters. -/
theorem gaussianCorrelationAsymptotic
    (n : Nat) (A : LatticeBasis n) (N : Nat) (hN : 1 <= N) :
    exists C : Real, 0 <= C /\
      forall R : Real, 1 <= R -> forall u w : RealEuclideanSpace n,
        exists theta : Real,
          |theta| <= C / R ^ N /\
            higherRankRepresentativeInner n (gaussianLatticeVector n A R u)
                (gaussianLatticeVector n A R w) =
              Real.exp (-(matrixNormSq n A (u - w)) / (4 * R ^ 2)) *
                (1 + theta) := by
  classical
  obtain ⟨C, hC_nonneg, hC⟩ := gaussianNormalizedRawCorrelationAsymptotic n A N hN
  refine ⟨C, hC_nonneg, ?_⟩
  intro R hR u w
  obtain ⟨theta, htheta, hcorr⟩ := hC R hR u w
  refine ⟨theta, htheta, ?_⟩
  have hu : gaussianRawAdmissible n A R u :=
    gaussianRawAdmissible_of_one_le n A R u hR
  have hw : gaussianRawAdmissible n A R w :=
    gaussianRawAdmissible_of_one_le n A R w hR
  rw [gaussianLatticeVector_of_admissible n A R u hu,
    gaussianLatticeVector_of_admissible n A R w hw]
  simpa [gaussianNormalizedRawCorrelation, gaussianCorrelationKernel] using hcorr

private def GaussianCorrelationAsymptoticStatement (n : Nat) (A : LatticeBasis n) : Prop :=
  forall N : Nat, 1 <= N ->
    exists C : Real, 0 <= C /\
      forall R : Real, 1 <= R -> forall u w : RealEuclideanSpace n,
        exists theta : Real,
          |theta| <= C / R ^ N /\
            higherRankRepresentativeInner n (gaussianLatticeVector n A R u)
                (gaussianLatticeVector n A R w) =
              gaussianCorrelationKernel n A R u w * (1 + theta)

private lemma higherRankTranslatedGaussianCorrelationAsymptotic
    (n : Nat) (A : LatticeBasis n) (N : Nat) (hN : 1 <= N)
    (hCorr : GaussianCorrelationAsymptoticStatement n A) :
    exists C : Real, 0 <= C /\
      forall R : Real, 1 <= R -> forall u w : RealEuclideanSpace n,
        forall a : Fin n -> Int,
          exists theta : Real,
            |theta| <= C / R ^ N /\
              higherRankRepresentativeInner n (gaussianLatticeVector n A R u)
                  (higherRankTranslation n a (gaussianLatticeVector n A R w)) =
                gaussianCorrelationKernel n A R u (w + gaussianIntegerPoint n a) *
                  (1 + theta) := by
  classical
  obtain ⟨C, hC, hCest⟩ := hCorr N hN
  refine ⟨C, hC, ?_⟩
  intro R hR u w a
  obtain ⟨theta, htheta, hcorr⟩ := hCest R hR u (w + gaussianIntegerPoint n a)
  refine ⟨theta, htheta, ?_⟩
  rw [higherRankTranslation_gaussianLatticeVector n A hR w a]
  exact hcorr

private lemma flatTorusMetric_dist_mk_le_matrixNorm
    (n : Nat) (A : LatticeBasis n) (u v : RealEuclideanSpace n) :
    @dist (flatTorus n A) (flatTorusMetric n A).toDist
        (QuotientAddGroup.mk' _ u : flatTorus n A)
        (QuotientAddGroup.mk' _ v : flatTorus n A) <=
      ‖Matrix.toEuclideanLin A.matrix (u - v)‖ := by
  let ambient : SeminormedAddCommGroup (RealEuclideanSpace n) :=
    SeminormedAddCommGroup.induced (RealEuclideanSpace n) (RealEuclideanSpace n)
      (Matrix.toEuclideanLin A.matrix)
  let quotientSeminorm : SeminormedAddCommGroup (flatTorus n A) := by
    change SeminormedAddCommGroup (RealEuclideanSpace n ⧸ gaussianIntegerAddSubgroup n)
    exact @QuotientAddGroup.instSeminormedAddCommGroup (RealEuclideanSpace n) ambient
      (gaussianIntegerAddSubgroup n)
  have hmetric : flatTorusMetric n A = quotientSeminorm.toPseudoMetricSpace := rfl
  rw [hmetric]
  letI : SeminormedAddCommGroup (RealEuclideanSpace n) := ambient
  letI : SeminormedAddCommGroup (flatTorus n A) := quotientSeminorm
  change dist (QuotientAddGroup.mk' _ u : flatTorus n A)
      (QuotientAddGroup.mk' _ v : flatTorus n A) <=
    ‖Matrix.toEuclideanLin A.matrix (u - v)‖
  rw [dist_eq_norm]
  dsimp [flatTorus]
  change ‖((QuotientAddGroup.mk' _ : RealEuclideanSpace n →+ RealEuclideanSpace n ⧸ _) u -
      (QuotientAddGroup.mk' _ : RealEuclideanSpace n →+ RealEuclideanSpace n ⧸ _) v)‖ <=
    ‖Matrix.toEuclideanLin A.matrix (u - v)‖
  rw [← map_sub (QuotientAddGroup.mk' _ : RealEuclideanSpace n →+
    RealEuclideanSpace n ⧸ _)]
  rw [quotient_norm_mk_eq]
  refine csInf_le ?_ ?_
  · refine ⟨0, ?_⟩
    rintro r ⟨s, _hs, rfl⟩
    exact norm_nonneg _
  · refine ⟨0, ?_, ?_⟩
    · simp
    · change ‖Matrix.toEuclideanLin A.matrix (u - v + 0)‖ =
        ‖Matrix.toEuclideanLin A.matrix (u - v)‖
      simp

private lemma flatTorusMetric_dist_le_out_matrixNorm
    (n : Nat) (A : LatticeBasis n) (x y : flatTorus n A) (a : Fin n -> Int) :
    (letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A;
      dist x y <=
        ‖Matrix.toEuclideanLin A.matrix
          ((Quotient.out x : RealEuclideanSpace n) -
            ((Quotient.out y : RealEuclideanSpace n) + gaussianIntegerPoint n a))‖) := by
  letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A
  have hx : (QuotientAddGroup.mk' _ (Quotient.out x : RealEuclideanSpace n) :
      flatTorus n A) = x := Quotient.out_eq x
  have hy : (QuotientAddGroup.mk' _
      ((Quotient.out y : RealEuclideanSpace n) + gaussianIntegerPoint n a) :
      flatTorus n A) = y := by
    calc
      (QuotientAddGroup.mk' _
          ((Quotient.out y : RealEuclideanSpace n) + gaussianIntegerPoint n a) :
          flatTorus n A)
          = (QuotientAddGroup.mk' _ (Quotient.out y : RealEuclideanSpace n) :
              flatTorus n A) := by
              simp only [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk_add,
                Quotient.out_eq, add_eq_left, QuotientAddGroup.eq_zero_iff]
              exact ⟨a, rfl⟩
      _ = y := Quotient.out_eq y
  have hdist := flatTorusMetric_dist_mk_le_matrixNorm n A
    (Quotient.out x : RealEuclideanSpace n)
    ((Quotient.out y : RealEuclideanSpace n) + gaussianIntegerPoint n a)
  rwa [hx, hy] at hdist

private lemma flatTorusMetric_dist_sq_le_out_matrixNormSq
    (n : Nat) (A : LatticeBasis n) (x y : flatTorus n A) (a : Fin n -> Int) :
    (letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A;
      dist x y ^ 2 <=
        matrixNormSq n A
          ((Quotient.out x : RealEuclideanSpace n) -
            ((Quotient.out y : RealEuclideanSpace n) + gaussianIntegerPoint n a))) := by
  letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A
  have h := flatTorusMetric_dist_le_out_matrixNorm n A x y a
  rw [matrixNormSq]
  exact sq_le_sq.mpr (by
    rw [abs_of_nonneg dist_nonneg, abs_of_nonneg (norm_nonneg _)]
    exact h)

set_option maxHeartbeats 800000 in
-- This compactness argument combines quotient representatives, closure of the integer subgroup,
-- and norm comparison estimates; the default heartbeat budget is too small for the final search.
private lemma exists_out_matrixNorm_lt_flatTorusMetric_dist_add
    (n : Nat) (A : LatticeBasis n) (x y : flatTorus n A) {η : Real} (hη : 0 < η) :
    (letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A;
      ∃ a : Fin n -> Int,
        ‖Matrix.toEuclideanLin A.matrix
          ((Quotient.out x : RealEuclideanSpace n) -
            ((Quotient.out y : RealEuclideanSpace n) + gaussianIntegerPoint n a))‖ <
          dist x y + η) := by
  let ambient : SeminormedAddCommGroup (RealEuclideanSpace n) :=
    SeminormedAddCommGroup.induced (RealEuclideanSpace n) (RealEuclideanSpace n)
      (Matrix.toEuclideanLin A.matrix)
  let quotientSeminorm : SeminormedAddCommGroup (flatTorus n A) := by
    change SeminormedAddCommGroup (RealEuclideanSpace n ⧸ _)
    exact @QuotientAddGroup.instSeminormedAddCommGroup (RealEuclideanSpace n) ambient _
  have hmetric : flatTorusMetric n A = quotientSeminorm.toPseudoMetricSpace := rfl
  rw [hmetric]
  letI : SeminormedAddCommGroup (RealEuclideanSpace n) := ambient
  letI : SeminormedAddCommGroup (flatTorus n A) := quotientSeminorm
  let u : RealEuclideanSpace n := Quotient.out x
  let v : RealEuclideanSpace n := Quotient.out y
  have hx : (QuotientAddGroup.mk' _ u :
      flatTorus n A) = x := Quotient.out_eq x
  have hy : (QuotientAddGroup.mk' _ v :
      flatTorus n A) = y := Quotient.out_eq y
  have hdist :
      dist x y =
        ‖(QuotientAddGroup.mk' _ (u - v) : flatTorus n A)‖ := by
    rw [← hx, ← hy, dist_eq_norm]
    change ‖(QuotientAddGroup.mk' _ u -
        QuotientAddGroup.mk' _ v : flatTorus n A)‖ =
      ‖(QuotientAddGroup.mk' _ (u - v) : flatTorus n A)‖
    rw [map_sub (QuotientAddGroup.mk' _ : RealEuclideanSpace n →+ flatTorus n A)]
    rfl
  obtain ⟨s, hs, hslt⟩ := QuotientAddGroup.exists_norm_add_lt
    (gaussianIntegerAddSubgroup n) (u - v) hη
  simp only [gaussianIntegerAddSubgroup, AddSubgroup.mem_mk] at hs
  rcases hs with ⟨k, rfl⟩
  refine ⟨-k, ?_⟩
  rw [hdist]
  dsimp [u, v]
  change @norm (RealEuclideanSpace n) ambient.toNorm (u - (v + gaussianIntegerPoint n (-k))) <
    ‖(QuotientAddGroup.mk' (gaussianIntegerAddSubgroup n) (u - v) : flatTorus n A)‖ + η
  rw [show u - (v + gaussianIntegerPoint n (-k)) =
      u - v + gaussianIntegerPoint n k by
    rw [show gaussianIntegerPoint n (-k) = -gaussianIntegerPoint n k by
      ext i
      simp [gaussianIntegerPoint]]
    abel]
  exact hslt

private lemma flatTorusMetric_eq_of_dist_eq_zero
    (n : Nat) (A : LatticeBasis n) (x y : flatTorus n A)
    (hxy : (letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A;
      dist x y = 0)) :
    x = y := by
  letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A
  let u : RealEuclideanSpace n := Quotient.out x
  let v : RealEuclideanSpace n := Quotient.out y
  obtain ⟨c, hc, hc_bound⟩ := matrixNormSq_lower_bound n A
  have hclosure : u - v ∈ closure (gaussianIntegerAddSubgroup n : Set (RealEuclideanSpace n)) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    let η : Real := c * ε
    have hη : 0 < η := mul_pos hc hε
    obtain ⟨a, ha⟩ := exists_out_matrixNorm_lt_flatTorusMetric_dist_add n A x y hη
    refine ⟨gaussianIntegerPoint n a, ⟨a, rfl⟩, ?_⟩
    have hnorm_lt :
        ‖u - (v + gaussianIntegerPoint n a)‖ < ε := by
      have hbound := hc_bound (u - (v + gaussianIntegerPoint n a))
      have hmatrix_lt :
          ‖Matrix.toEuclideanLin A.matrix (u - (v + gaussianIntegerPoint n a))‖ <
            c * ε := by
        simpa [u, v, η, hxy] using ha
      have hc_mul_lt :
          c * ‖u - (v + gaussianIntegerPoint n a)‖ < c * ε :=
        lt_of_le_of_lt hbound hmatrix_lt
      exact lt_of_mul_lt_mul_left hc_mul_lt hc.le
    rw [dist_eq_norm]
    convert hnorm_lt using 1
    abel_nf
  have hmem : u - v ∈ gaussianIntegerAddSubgroup n := by
    simpa [(gaussianIntegerAddSubgroup_isClosed_default n).closure_eq] using hclosure
  rcases hmem with ⟨a, ha⟩
  have hx : (QuotientAddGroup.mk' _ u : flatTorus n A) = x := Quotient.out_eq x
  have hy : (QuotientAddGroup.mk' _ v : flatTorus n A) = y := Quotient.out_eq y
  rw [← hx, ← hy]
  have huv : u = v + gaussianIntegerPoint n a := by
    rw [← ha]
    abel_nf
  rw [huv]
  simp only [flatTorus, gaussianIntegerPoint, QuotientAddGroup.mk'_apply,
    QuotientAddGroup.mk_add, add_eq_left, QuotientAddGroup.eq_zero_iff]
  exact ⟨a, rfl⟩

private noncomputable def gaussianFiniteSubsetMap
    (n : Nat) (A : LatticeBasis n) (R : Real) (E : Finset (flatTorus n A)) :
    {x : flatTorus n A // x ∈ E} -> higherRankSphereQuotient n :=
  fun x => gaussianQuotientPoint n A R (Quotient.out x.1)

private noncomputable def gaussianEmbeddingScale (R : Real) : Real :=
  (Real.sqrt 2 * R)⁻¹

private lemma gaussianEmbeddingScale_pos {R : Real} (hR : 0 < R) :
    0 < gaussianEmbeddingScale R := by
  dsimp [gaussianEmbeddingScale]
  positivity

private lemma gaussianEmbeddingScale_mul_sq (R d : Real) :
    (gaussianEmbeddingScale R * d) ^ 2 = d ^ 2 / (2 * R ^ 2) := by
  dsimp [gaussianEmbeddingScale]
  rw [mul_pow, inv_pow, mul_pow]
  rw [Real.sq_sqrt (by norm_num : (0 : Real) <= 2)]
  ring

private lemma higherRankRepresentativeInner_le_one
    (n : Nat) (f g : higherRankHilbertSphere n) :
    higherRankRepresentativeInner n f g <= 1 := by
  have hf : ‖(f : gaussianL2Space n)‖ = 1 := by
    rw [← dist_zero_right (f : gaussianL2Space n)]
    exact f.2
  have hg : ‖(g : gaussianL2Space n)‖ = 1 := by
    rw [← dist_zero_right (g : gaussianL2Space n)]
    exact g.2
  simpa [higherRankRepresentativeInner, hf, hg, gaussianL2Space] using
    real_inner_le_norm (x := (f : gaussianL2Space n)) (y := (g : gaussianL2Space n))

private lemma higherRankCorrelationSet_bddAbove
    (n : Nat) (f g : higherRankHilbertSphere n) :
    BddAbove (higherRankCorrelationSet n f g) := by
  refine ⟨1, ?_⟩
  rintro z ⟨a, rfl⟩
  exact higherRankRepresentativeInner_le_one n f (higherRankTranslation n a g)

private lemma eventually_const_div_pow_le
    {K b : Real} (hb : 0 < b) {m : Nat} (hm : m ≠ 0) :
    ∀ᶠ R in Filter.atTop, K / R ^ m <= b := by
  have hlim : Filter.Tendsto (fun R : Real => K / R ^ m) Filter.atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop (Filter.tendsto_pow_atTop (α := Real) hm)
  have hev : ∀ᶠ R in Filter.atTop, K / R ^ m < b :=
    hlim.eventually (eventually_lt_nhds hb)
  exact hev.mono fun _ h => le_of_lt h

private lemma one_sub_exp_neg_le (t : Real) :
    1 - Real.exp (-t) <= t := by
  have hle : 1 - t <= Real.exp (-t) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using Real.add_one_le_exp (-t)
  linarith

private lemma one_sub_exp_neg_ge_mul {t alpha : Real}
    (ht : 0 <= t) (halpha_lt : alpha < 1)
    (htle : t <= alpha / (1 - alpha)) :
    (1 - alpha) * t <= 1 - Real.exp (-t) := by
  have hden_pos : 0 < 1 - alpha := by linarith
  have hone_add_pos : 0 < 1 + t := by linarith
  have hexp_pos : 0 < Real.exp t := Real.exp_pos t
  have hle_exp : 1 + t <= Real.exp t := by
    simpa [add_comm] using Real.add_one_le_exp t
  have hinv_le : (Real.exp t)⁻¹ <= (1 + t)⁻¹ := by
    exact (inv_le_inv₀ hexp_pos hone_add_pos).mpr hle_exp
  have h_exp_neg_le : Real.exp (-t) <= (1 + t)⁻¹ := by
    simpa [Real.exp_neg] using hinv_le
  calc
    (1 - alpha) * t <= t / (1 + t) := by
      rw [div_eq_mul_inv, mul_comm t]
      have hmul_bound : (1 - alpha) * (1 + t) <= 1 := by
        have hmul_t' : t * (1 - alpha) <= alpha :=
          (le_div_iff₀ hden_pos).mp htle
        have hmul_t : (1 - alpha) * t <= alpha := by
          simpa [mul_comm] using hmul_t'
        nlinarith
      have hmul : (1 - alpha) <= (1 + t)⁻¹ := by
        rw [show (1 + t)⁻¹ = 1 / (1 + t) by ring]
        exact (le_div_iff₀ hone_add_pos).mpr hmul_bound
      exact mul_le_mul_of_nonneg_right hmul ht
    _ = 1 - (1 + t)⁻¹ := by
      field_simp [hone_add_pos.ne']
      ring
    _ <= 1 - Real.exp (-t) := by linarith

private lemma gaussian_delta_rel_of_scaled
    {C R beta d : Real} (hR : 0 < R)
    (h : 4 * C / R ^ 2 <= beta * d ^ 2) :
    2 * (C / R ^ 4) <= beta * d ^ 2 / (2 * R ^ 2) := by
  have hR2_ne : R ^ 2 ≠ 0 := pow_ne_zero 2 hR.ne'
  have hR4_ne : R ^ 4 ≠ 0 := pow_ne_zero 4 hR.ne'
  have hden_ne : 2 * R ^ 2 ≠ 0 := by positivity
  field_simp [hR2_ne, hR4_ne, hden_ne] at h ⊢
  ring_nf at h ⊢
  nlinarith [sq_nonneg R]

private lemma gaussian_chordal_sq_lower_bound
    {C R beta d : Real} (hR : 0 < R) (hC : 0 <= C)
    (hbeta_lt : beta < 1)
    (ht_small : d ^ 2 / (4 * R ^ 2) <= beta / (1 - beta))
    (hdelta_rel : 4 * C / R ^ 2 <= beta * d ^ 2) :
    (1 - 2 * beta) * d ^ 2 / (2 * R ^ 2) <=
      2 - 2 * Real.exp (-(d ^ 2) / (4 * R ^ 2)) * (1 + C / R ^ 4) := by
  let t : Real := d ^ 2 / (4 * R ^ 2)
  let delta : Real := C / R ^ 4
  have ht_nonneg : 0 <= t := by
    dsimp [t]
    positivity
  have h_exp_le_one : Real.exp (-t) <= 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have hmain : (1 - beta) * t <= 1 - Real.exp (-t) :=
    one_sub_exp_neg_ge_mul ht_nonneg hbeta_lt (by simpa [t] using ht_small)
  have hdelta_nonneg : 0 <= delta := by
    dsimp [delta]
    positivity
  have hdelta_term :
      2 * delta * Real.exp (-t) <= beta * d ^ 2 / (2 * R ^ 2) := by
    have hdelta_scaled : 2 * delta <= beta * d ^ 2 / (2 * R ^ 2) := by
      simpa [delta] using gaussian_delta_rel_of_scaled hR hdelta_rel
    have htwo_delta_nonneg : 0 <= 2 * delta := by positivity
    calc
      2 * delta * Real.exp (-t) <= 2 * delta * 1 :=
        mul_le_mul_of_nonneg_left h_exp_le_one htwo_delta_nonneg
      _ = 2 * delta := by ring
      _ <= beta * d ^ 2 / (2 * R ^ 2) := hdelta_scaled
  have ht_eq : 2 * t = d ^ 2 / (2 * R ^ 2) := by
    dsimp [t]
    field_simp [show (4 * R ^ 2) ≠ 0 by positivity, show (2 * R ^ 2) ≠ 0 by positivity]
    ring_nf
  have hrewrite :
      2 - 2 * Real.exp (-(d ^ 2) / (4 * R ^ 2)) * (1 + C / R ^ 4) =
        2 * (1 - Real.exp (-t)) - 2 * delta * Real.exp (-t) := by
    dsimp [t, delta]
    ring_nf
  rw [hrewrite]
  calc
    (1 - 2 * beta) * d ^ 2 / (2 * R ^ 2)
        = (1 - 2 * beta) * (2 * t) := by
          rw [ht_eq]
          ring
    _ = 2 * ((1 - beta) * t) - beta * d ^ 2 / (2 * R ^ 2) := by
          have hbeta_dt : beta * d ^ 2 / (2 * R ^ 2) = beta * (2 * t) := by
            rw [show beta * d ^ 2 / (2 * R ^ 2) =
                beta * (d ^ 2 / (2 * R ^ 2)) by ring]
            rw [← ht_eq]
          rw [hbeta_dt]
          ring
    _ <= 2 * (1 - Real.exp (-t)) - 2 * delta * Real.exp (-t) := by
          nlinarith

private lemma gaussian_chordal_sq_upper_bound
    {C R beta d : Real} (hR : 0 < R) (hC : 0 <= C)
    (hdelta_rel : 4 * C / R ^ 2 <= beta * d ^ 2) :
    2 - 2 * Real.exp (-((d + beta * d) ^ 2) / (4 * R ^ 2)) * (1 - C / R ^ 4) <=
      ((1 + beta) ^ 2 + beta) * d ^ 2 / (2 * R ^ 2) := by
  let t : Real := (d + beta * d) ^ 2 / (4 * R ^ 2)
  let delta : Real := C / R ^ 4
  have h_exp_le_one : Real.exp (-t) <= 1 := by
    rw [Real.exp_le_one_iff]
    have ht_nonneg : 0 <= t := by
      dsimp [t]
      positivity
    linarith
  have hdelta_nonneg : 0 <= delta := by
    dsimp [delta]
    positivity
  have hdelta_term :
      2 * delta * Real.exp (-t) <= beta * d ^ 2 / (2 * R ^ 2) := by
    have hdelta_scaled : 2 * delta <= beta * d ^ 2 / (2 * R ^ 2) := by
      simpa [delta] using gaussian_delta_rel_of_scaled hR hdelta_rel
    have htwo_delta_nonneg : 0 <= 2 * delta := by positivity
    calc
      2 * delta * Real.exp (-t) <= 2 * delta * 1 :=
        mul_le_mul_of_nonneg_left h_exp_le_one htwo_delta_nonneg
      _ = 2 * delta := by ring
      _ <= beta * d ^ 2 / (2 * R ^ 2) := hdelta_scaled
  have ht_bound : 1 - Real.exp (-t) <= t := by
    simpa using one_sub_exp_neg_le t
  have ht_eq :
      2 * t = (1 + beta) ^ 2 * d ^ 2 / (2 * R ^ 2) := by
    dsimp [t]
    have hden4 : (4 * R ^ 2) ≠ 0 := by positivity
    have hden2 : (2 * R ^ 2) ≠ 0 := by positivity
    field_simp [hden4, hden2]
    ring
  have hrewrite :
      2 - 2 * Real.exp (-((d + beta * d) ^ 2) / (4 * R ^ 2)) *
          (1 - C / R ^ 4) =
        2 * (1 - Real.exp (-t)) + 2 * delta * Real.exp (-t) := by
    dsimp [t, delta]
    ring_nf
  rw [hrewrite]
  calc
    2 * (1 - Real.exp (-t)) + 2 * delta * Real.exp (-t)
        <= 2 * t + beta * d ^ 2 / (2 * R ^ 2) := by nlinarith
    _ = ((1 + beta) ^ 2 + beta) * d ^ 2 / (2 * R ^ 2) := by
          rw [ht_eq]
          ring

private lemma higherRankGaussianCorrelationSup_upper
    (n : Nat) (A : LatticeBasis n) {N : Nat} {C R : Real}
    (hC : 0 <= C) (hR : 1 <= R)
    (hEst : ∀ R : Real, 1 <= R -> ∀ u w : RealEuclideanSpace n,
      ∀ a : Fin n -> Int,
        ∃ theta : Real,
          |theta| <= C / R ^ N /\
            higherRankRepresentativeInner n (gaussianLatticeVector n A R u)
                (higherRankTranslation n a (gaussianLatticeVector n A R w)) =
              gaussianCorrelationKernel n A R u (w + gaussianIntegerPoint n a) *
                (1 + theta))
    (x y : flatTorus n A) :
    (letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A;
      higherRankCorrelationSupFromRepresentatives n
          (gaussianLatticeVector n A R (Quotient.out x : RealEuclideanSpace n))
          (gaussianLatticeVector n A R (Quotient.out y : RealEuclideanSpace n)) <=
        Real.exp (-(dist x y ^ 2) / (4 * R ^ 2)) * (1 + C / R ^ N)) := by
  letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A
  let u : RealEuclideanSpace n := Quotient.out x
  let v : RealEuclideanSpace n := Quotient.out y
  rw [higherRankCorrelationSupFromRepresentatives, higherRankCorrelationSet]
  refine csSup_le (Set.range_nonempty _) ?_
  rintro z ⟨a, rfl⟩
  obtain ⟨theta, htheta_abs, htheta_eq⟩ := hEst R hR u v a
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hden_pos : 0 < 4 * R ^ 2 := by positivity
  have hdelta_nonneg : 0 <= C / R ^ N := by positivity
  have htheta_le : 1 + theta <= 1 + C / R ^ N := by
    have htheta : theta <= C / R ^ N := (le_abs_self theta).trans htheta_abs
    linarith
  have hq :
      dist x y ^ 2 <=
        matrixNormSq n A (u - (v + gaussianIntegerPoint n a)) := by
    simpa [u, v] using flatTorusMetric_dist_sq_le_out_matrixNormSq n A x y a
  have harg :
      -(matrixNormSq n A (u - (v + gaussianIntegerPoint n a))) / (4 * R ^ 2) <=
        -(dist x y ^ 2) / (4 * R ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_right (neg_le_neg hq) (inv_nonneg.mpr hden_pos.le)
    simpa [div_eq_mul_inv] using hmul
  have hkernel_le :
      gaussianCorrelationKernel n A R u (v + gaussianIntegerPoint n a) <=
        Real.exp (-(dist x y ^ 2) / (4 * R ^ 2)) := by
    simpa [gaussianCorrelationKernel] using Real.exp_le_exp.mpr harg
  have hkernel_nonneg :
      0 <= gaussianCorrelationKernel n A R u (v + gaussianIntegerPoint n a) := by
    exact (Real.exp_pos _).le
  have hmodel_factor_nonneg : 0 <= 1 + C / R ^ N := by linarith
  calc
    higherRankRepresentativeInner n (gaussianLatticeVector n A R u)
          (higherRankTranslation n a (gaussianLatticeVector n A R v))
        = gaussianCorrelationKernel n A R u (v + gaussianIntegerPoint n a) *
            (1 + theta) := htheta_eq
    _ <= gaussianCorrelationKernel n A R u (v + gaussianIntegerPoint n a) *
          (1 + C / R ^ N) :=
            mul_le_mul_of_nonneg_left htheta_le hkernel_nonneg
    _ <= Real.exp (-(dist x y ^ 2) / (4 * R ^ 2)) * (1 + C / R ^ N) :=
            mul_le_mul_of_nonneg_right hkernel_le hmodel_factor_nonneg

private lemma higherRankGaussianCorrelationSup_lower
    (n : Nat) (A : LatticeBasis n) {N : Nat} {C R eta : Real}
    (hR : 1 <= R) (heta : 0 < eta) (hdelta_le_one : C / R ^ N <= 1)
    (hEst : ∀ R : Real, 1 <= R -> ∀ u w : RealEuclideanSpace n,
      ∀ a : Fin n -> Int,
        ∃ theta : Real,
          |theta| <= C / R ^ N /\
            higherRankRepresentativeInner n (gaussianLatticeVector n A R u)
                (higherRankTranslation n a (gaussianLatticeVector n A R w)) =
              gaussianCorrelationKernel n A R u (w + gaussianIntegerPoint n a) *
                (1 + theta))
    (x y : flatTorus n A) :
    (letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A;
      Real.exp (-((dist x y + eta) ^ 2) / (4 * R ^ 2)) * (1 - C / R ^ N) <=
        higherRankCorrelationSupFromRepresentatives n
          (gaussianLatticeVector n A R (Quotient.out x : RealEuclideanSpace n))
          (gaussianLatticeVector n A R (Quotient.out y : RealEuclideanSpace n))) := by
  letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A
  let u : RealEuclideanSpace n := Quotient.out x
  let v : RealEuclideanSpace n := Quotient.out y
  obtain ⟨a, ha⟩ := exists_out_matrixNorm_lt_flatTorusMetric_dist_add n A x y heta
  obtain ⟨theta, htheta_abs, htheta_eq⟩ := hEst R hR u v a
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hden_pos : 0 < 4 * R ^ 2 := by positivity
  have hdelta_nonneg : 0 <= C / R ^ N :=
    (abs_nonneg theta).trans htheta_abs
  have hfactor_nonneg : 0 <= 1 - C / R ^ N := by linarith
  have htheta_lower : 1 - C / R ^ N <= 1 + theta := by
    have htheta : -(C / R ^ N) <= theta := (abs_le.mp htheta_abs).1
    linarith
  have hq :
      matrixNormSq n A (u - (v + gaussianIntegerPoint n a)) <=
        (dist x y + eta) ^ 2 := by
    rw [matrixNormSq]
    have hsum_nonneg : 0 <= dist x y + eta := by positivity
    have habs :
        |‖Matrix.toEuclideanLin A.matrix (u - (v + gaussianIntegerPoint n a))‖| <=
          |dist x y + eta| := by
      rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hsum_nonneg]
      exact le_of_lt (by simpa [u, v] using ha)
    exact sq_le_sq.mpr habs
  have harg :
      -((dist x y + eta) ^ 2) / (4 * R ^ 2) <=
        -(matrixNormSq n A (u - (v + gaussianIntegerPoint n a))) / (4 * R ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_right (neg_le_neg hq) (inv_nonneg.mpr hden_pos.le)
    simpa [div_eq_mul_inv] using hmul
  have hkernel_ge :
      Real.exp (-((dist x y + eta) ^ 2) / (4 * R ^ 2)) <=
        gaussianCorrelationKernel n A R u (v + gaussianIntegerPoint n a) := by
    simpa [gaussianCorrelationKernel] using Real.exp_le_exp.mpr harg
  have hkernel_nonneg :
      0 <= gaussianCorrelationKernel n A R u (v + gaussianIntegerPoint n a) := by
    exact (Real.exp_pos _).le
  have hbdd : BddAbove (higherRankCorrelationSet n
      (gaussianLatticeVector n A R u) (gaussianLatticeVector n A R v)) :=
    higherRankCorrelationSet_bddAbove n
      (gaussianLatticeVector n A R u) (gaussianLatticeVector n A R v)
  calc
    Real.exp (-((dist x y + eta) ^ 2) / (4 * R ^ 2)) * (1 - C / R ^ N)
        <= gaussianCorrelationKernel n A R u (v + gaussianIntegerPoint n a) *
            (1 - C / R ^ N) :=
          mul_le_mul_of_nonneg_right hkernel_ge hfactor_nonneg
    _ <= gaussianCorrelationKernel n A R u (v + gaussianIntegerPoint n a) *
            (1 + theta) :=
          mul_le_mul_of_nonneg_left htheta_lower hkernel_nonneg
    _ = higherRankRepresentativeInner n (gaussianLatticeVector n A R u)
          (higherRankTranslation n a (gaussianLatticeVector n A R v)) := htheta_eq.symm
    _ <= higherRankCorrelationSupFromRepresentatives n
          (gaussianLatticeVector n A R u) (gaussianLatticeVector n A R v) := by
          exact le_csSup hbdd ⟨a, rfl⟩

private lemma gaussianFiniteSubsetMap_pair_dist_sq_bounds
    (n : Nat) (A : LatticeBasis n) (E : Finset (flatTorus n A))
    {C R beta : Real} (hC : 0 <= C) (hR : 1 <= R)
    (hbeta_pos : 0 < beta) (hbeta_lt : beta < 1)
    (hdelta_le_one : C / R ^ 4 <= 1)
    (hEst : ∀ R : Real, 1 <= R -> ∀ u w : RealEuclideanSpace n,
      ∀ a : Fin n -> Int,
        ∃ theta : Real,
          |theta| <= C / R ^ 4 /\
            higherRankRepresentativeInner n (gaussianLatticeVector n A R u)
                (higherRankTranslation n a (gaussianLatticeVector n A R w)) =
              gaussianCorrelationKernel n A R u (w + gaussianIntegerPoint n a) *
                (1 + theta))
    (x y : {x : flatTorus n A // x ∈ E})
    (hdpos : (letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A;
      0 < dist x.1 y.1))
    (ht_small_pair : (letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A;
      dist x.1 y.1 ^ 2 / (4 * R ^ 2) <= beta / (1 - beta)))
    (hdelta_rel : (letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A;
      4 * C / R ^ 2 <= beta * dist x.1 y.1 ^ 2)) :
    (letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A;
      letI : PseudoMetricSpace (higherRankSphereQuotient n) := higherRankChordalMetric n;
      (1 - 2 * beta) * dist x.1 y.1 ^ 2 / (2 * R ^ 2) <=
          dist (gaussianFiniteSubsetMap n A R E x)
            (gaussianFiniteSubsetMap n A R E y) ^ 2 /\
        dist (gaussianFiniteSubsetMap n A R E x)
            (gaussianFiniteSubsetMap n A R E y) ^ 2 <=
          ((1 + beta) ^ 2 + beta) * dist x.1 y.1 ^ 2 / (2 * R ^ 2)) := by
  classical
  letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A
  letI : PseudoMetricSpace (higherRankSphereQuotient n) := higherRankChordalMetric n
  let u : RealEuclideanSpace n := Quotient.out x.1
  let v : RealEuclideanSpace n := Quotient.out y.1
  let f : higherRankHilbertSphere n := gaussianLatticeVector n A R u
  let g : higherRankHilbertSphere n := gaussianLatticeVector n A R v
  let S : Real := higherRankCorrelationSupFromRepresentatives n f g
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hdist_sq :
      dist (gaussianFiniteSubsetMap n A R E x)
          (gaussianFiniteSubsetMap n A R E y) ^ 2 =
        2 - 2 * S := by
    dsimp [S, f, g, u, v]
    simpa [gaussianFiniteSubsetMap, gaussianQuotientPoint] using
      higherRankCorrelationFormula n
        (gaussianLatticeVector n A R (Quotient.out x.1 : RealEuclideanSpace n))
        (gaussianLatticeVector n A R (Quotient.out y.1 : RealEuclideanSpace n))
  have hsup_upper :
      S <= Real.exp (-(dist x.1 y.1 ^ 2) / (4 * R ^ 2)) * (1 + C / R ^ 4) := by
    dsimp [S, f, g, u, v]
    simpa using
      higherRankGaussianCorrelationSup_upper n A (N := 4) hC hR hEst x.1 y.1
  have hsup_lower :
      Real.exp (-((dist x.1 y.1 + beta * dist x.1 y.1) ^ 2) / (4 * R ^ 2)) *
          (1 - C / R ^ 4) <= S := by
    dsimp [S, f, g, u, v]
    have heta : 0 < beta * dist x.1 y.1 := mul_pos hbeta_pos hdpos
    simpa using
      higherRankGaussianCorrelationSup_lower n A (N := 4) (R := R)
        (C := C) (eta := beta * dist x.1 y.1) hR heta hdelta_le_one hEst x.1 y.1
  have hlower_raw :
      2 - 2 * (Real.exp (-(dist x.1 y.1 ^ 2) / (4 * R ^ 2)) * (1 + C / R ^ 4)) <=
        dist (gaussianFiniteSubsetMap n A R E x)
          (gaussianFiniteSubsetMap n A R E y) ^ 2 := by
    rw [hdist_sq]
    nlinarith
  have hupper_raw :
      dist (gaussianFiniteSubsetMap n A R E x)
          (gaussianFiniteSubsetMap n A R E y) ^ 2 <=
        2 - 2 * (Real.exp (-((dist x.1 y.1 + beta * dist x.1 y.1) ^ 2) /
            (4 * R ^ 2)) * (1 - C / R ^ 4)) := by
    rw [hdist_sq]
    nlinarith
  refine ⟨?_, ?_⟩
  · have hlower_raw' :
        2 - 2 * Real.exp (-(dist x.1 y.1 ^ 2) / (4 * R ^ 2)) * (1 + C / R ^ 4) <=
          dist (gaussianFiniteSubsetMap n A R E x)
            (gaussianFiniteSubsetMap n A R E y) ^ 2 := by
      simpa [mul_assoc] using hlower_raw
    exact (gaussian_chordal_sq_lower_bound hRpos hC hbeta_lt ht_small_pair
      hdelta_rel).trans hlower_raw'
  · have hupper_raw' :
        dist (gaussianFiniteSubsetMap n A R E x)
            (gaussianFiniteSubsetMap n A R E y) ^ 2 <=
          2 - 2 * Real.exp (-((dist x.1 y.1 + beta * dist x.1 y.1) ^ 2) /
              (4 * R ^ 2)) * (1 - C / R ^ 4) := by
      simpa [mul_assoc] using hupper_raw
    exact hupper_raw'.trans (gaussian_chordal_sq_upper_bound hRpos hC hdelta_rel)

private lemma gaussianFiniteSubsetMap_pair_distortion_eventually_of_pos
    (n : Nat) (A : LatticeBasis n) (E : Finset (flatTorus n A))
    {C eps : Real} (hC : 0 <= C) (heps : 0 < eps)
    (hEst : ∀ R : Real, 1 <= R -> ∀ u w : RealEuclideanSpace n,
      ∀ a : Fin n -> Int,
        ∃ theta : Real,
          |theta| <= C / R ^ 4 /\
            higherRankRepresentativeInner n (gaussianLatticeVector n A R u)
                (higherRankTranslation n a (gaussianLatticeVector n A R w)) =
              gaussianCorrelationKernel n A R u (w + gaussianIntegerPoint n a) *
                (1 + theta))
    (x y : {x : flatTorus n A // x ∈ E})
    (hdpos : (letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A;
      0 < dist x.1 y.1)) :
    ∀ᶠ R in Filter.atTop,
      (letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A;
        letI : PseudoMetricSpace (higherRankSphereQuotient n) := higherRankChordalMetric n;
        1 <= R /\
          (1 - eps) * gaussianEmbeddingScale R * dist x.1 y.1 <=
              dist (gaussianFiniteSubsetMap n A R E x) (gaussianFiniteSubsetMap n A R E y) /\
            dist (gaussianFiniteSubsetMap n A R E x) (gaussianFiniteSubsetMap n A R E y) <=
              (1 + eps) * gaussianEmbeddingScale R * dist x.1 y.1) := by
  classical
  letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A
  letI : PseudoMetricSpace (higherRankSphereQuotient n) := higherRankChordalMetric n
  let d : Real := dist x.1 y.1
  let beta : Real := min (eps / 8) (1 / 4)
  have hdpos' : 0 < d := by simpa [d] using hdpos
  have hd_nonneg : 0 <= d := hdpos'.le
  have hbeta_pos : 0 < beta := by
    dsimp [beta]
    exact lt_min (by linarith) (by norm_num)
  have hbeta_nonneg : 0 <= beta := hbeta_pos.le
  have hbeta_le_eps : beta <= eps / 8 := by
    dsimp [beta]
    exact min_le_left _ _
  have hbeta_le_quarter : beta <= 1 / 4 := by
    dsimp [beta]
    exact min_le_right _ _
  have hbeta_lt_one : beta < 1 := lt_of_le_of_lt hbeta_le_quarter (by norm_num)
  have hbeta_d_sq_pos : 0 < beta * d ^ 2 := by positivity
  have hbeta_div_pos : 0 < beta / (1 - beta) := by
    have hden : 0 < 1 - beta := by linarith
    positivity
  have hev_R : ∀ᶠ R : Real in Filter.atTop, (1 : Real) <= R :=
    Filter.eventually_ge_atTop (α := Real) 1
  have hev_delta_one : ∀ᶠ R in Filter.atTop, C / R ^ 4 <= 1 :=
    eventually_const_div_pow_le (K := C) (b := 1) zero_lt_one (by norm_num)
  have hev_tsmall : ∀ᶠ R in Filter.atTop, d ^ 2 / (4 * R ^ 2) <= beta / (1 - beta) := by
    have hev := eventually_const_div_pow_le
      (K := d ^ 2 / 4) (b := beta / (1 - beta)) hbeta_div_pos (m := 2)
      (by norm_num)
    filter_upwards [hev] with R hR
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hR
  have hev_delta_rel : ∀ᶠ R in Filter.atTop, 4 * C / R ^ 2 <= beta * d ^ 2 :=
    eventually_const_div_pow_le (K := 4 * C) (b := beta * d ^ 2) hbeta_d_sq_pos
      (m := 2) (by norm_num)
  filter_upwards [hev_R, hev_delta_one, hev_tsmall, hev_delta_rel] with
    R hR hdelta_one ht_small hdelta_rel
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hsq_bounds := gaussianFiniteSubsetMap_pair_dist_sq_bounds n A E hC hR hbeta_pos
    hbeta_lt_one hdelta_one hEst x y (by simpa [d] using hdpos') (by simpa [d] using ht_small)
    (by simpa [d] using hdelta_rel)
  let D : Real := dist (gaussianFiniteSubsetMap n A R E x) (gaussianFiniteSubsetMap n A R E y)
  have hD_nonneg : 0 <= D := by
    dsimp [D]
    exact dist_nonneg
  have hscale_pos : 0 < gaussianEmbeddingScale R := gaussianEmbeddingScale_pos hRpos
  have hscale_d_nonneg : 0 <= gaussianEmbeddingScale R * d := by positivity
  have hupper_coeff : ((1 + beta) ^ 2 + beta) <= (1 + eps) ^ 2 := by
    have hbeta_sq_le : beta ^ 2 <= beta / 4 := by
      nlinarith [mul_le_mul_of_nonneg_left hbeta_le_quarter hbeta_nonneg]
    nlinarith [hbeta_le_eps, hbeta_sq_le, sq_nonneg eps, heps.le]
  have hupper_sq :
      D ^ 2 <= ((1 + eps) * gaussianEmbeddingScale R * d) ^ 2 := by
    have hcoeff_scaled :
        ((1 + beta) ^ 2 + beta) * d ^ 2 / (2 * R ^ 2) <=
          (1 + eps) ^ 2 * d ^ 2 / (2 * R ^ 2) := by
      gcongr
    have htarget :
        ((1 + eps) * gaussianEmbeddingScale R * d) ^ 2 =
          (1 + eps) ^ 2 * d ^ 2 / (2 * R ^ 2) := by
      rw [show (1 + eps) * gaussianEmbeddingScale R * d =
          (1 + eps) * (gaussianEmbeddingScale R * d) by ring]
      rw [mul_pow, gaussianEmbeddingScale_mul_sq]
      ring
    dsimp [D]
    exact hsq_bounds.2.trans (by simpa [htarget] using hcoeff_scaled)
  have hupper :
      D <= (1 + eps) * gaussianEmbeddingScale R * d := by
    have hrhs_nonneg : 0 <= (1 + eps) * gaussianEmbeddingScale R * d := by positivity
    exact (sq_le_sq₀ hD_nonneg hrhs_nonneg).mp hupper_sq
  have hlower :
      (1 - eps) * gaussianEmbeddingScale R * d <= D := by
    by_cases heps_lt_one : eps < 1
    · have heps_le_one : eps <= 1 := le_of_lt heps_lt_one
      have hleft_nonneg : 0 <= (1 - eps) * gaussianEmbeddingScale R * d := by
        positivity
      have hcoeff_lower : (1 - eps) ^ 2 <= 1 - 2 * beta := by
        have h2beta_le_eps : 2 * beta <= eps := by nlinarith [hbeta_le_eps]
        have heps_sq_le : eps ^ 2 <= eps := by
          nlinarith [mul_nonneg heps.le (sub_nonneg.mpr heps_le_one)]
        nlinarith
      have hlower_sq :
          ((1 - eps) * gaussianEmbeddingScale R * d) ^ 2 <= D ^ 2 := by
        have hcoeff_scaled :
            (1 - eps) ^ 2 * d ^ 2 / (2 * R ^ 2) <=
              (1 - 2 * beta) * d ^ 2 / (2 * R ^ 2) := by
          gcongr
        have htarget :
            ((1 - eps) * gaussianEmbeddingScale R * d) ^ 2 =
              (1 - eps) ^ 2 * d ^ 2 / (2 * R ^ 2) := by
          rw [show (1 - eps) * gaussianEmbeddingScale R * d =
              (1 - eps) * (gaussianEmbeddingScale R * d) by ring]
          rw [mul_pow, gaussianEmbeddingScale_mul_sq]
          ring
        have hcoeff_scaled' :
            ((1 - eps) * gaussianEmbeddingScale R * d) ^ 2 <=
              (1 - 2 * beta) * d ^ 2 / (2 * R ^ 2) := by
          simpa [htarget] using hcoeff_scaled
        exact hcoeff_scaled'.trans hsq_bounds.1
      exact (sq_le_sq₀ hleft_nonneg hD_nonneg).mp hlower_sq
    · have hnonpos : (1 - eps) <= 0 := by linarith
      have hleft_nonpos : (1 - eps) * gaussianEmbeddingScale R * d <= 0 := by
        have htmp : (1 - eps) * (gaussianEmbeddingScale R * d) <= 0 :=
          mul_nonpos_of_nonpos_of_nonneg hnonpos hscale_d_nonneg
        simpa [mul_assoc] using htmp
      exact hleft_nonpos.trans hD_nonneg
  refine ⟨hR, ?_, ?_⟩
  · simpa [d, D, mul_assoc] using hlower
  · simpa [d, D, mul_assoc] using hupper

private lemma gaussianFiniteSubsetMap_pair_distortion_eventually
    (n : Nat) (A : LatticeBasis n) (E : Finset (flatTorus n A))
    {C eps : Real} (hC : 0 <= C) (heps : 0 < eps)
    (hEst : ∀ R : Real, 1 <= R -> ∀ u w : RealEuclideanSpace n,
      ∀ a : Fin n -> Int,
        ∃ theta : Real,
          |theta| <= C / R ^ 4 /\
            higherRankRepresentativeInner n (gaussianLatticeVector n A R u)
                (higherRankTranslation n a (gaussianLatticeVector n A R w)) =
              gaussianCorrelationKernel n A R u (w + gaussianIntegerPoint n a) *
                (1 + theta))
    (x y : {x : flatTorus n A // x ∈ E}) :
    ∀ᶠ R in Filter.atTop,
      (letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A;
        letI : PseudoMetricSpace (higherRankSphereQuotient n) := higherRankChordalMetric n;
        1 <= R /\
          (1 - eps) * gaussianEmbeddingScale R * dist x.1 y.1 <=
              dist (gaussianFiniteSubsetMap n A R E x) (gaussianFiniteSubsetMap n A R E y) /\
            dist (gaussianFiniteSubsetMap n A R E x) (gaussianFiniteSubsetMap n A R E y) <=
              (1 + eps) * gaussianEmbeddingScale R * dist x.1 y.1) := by
  classical
  letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A
  letI : PseudoMetricSpace (higherRankSphereQuotient n) := higherRankChordalMetric n
  by_cases hdpos : 0 < dist x.1 y.1
  · exact gaussianFiniteSubsetMap_pair_distortion_eventually_of_pos n A E hC heps hEst x y hdpos
  · have hdist_zero : dist x.1 y.1 = 0 := le_antisymm (le_of_not_gt hdpos) dist_nonneg
    have hxy : x.1 = y.1 := flatTorusMetric_eq_of_dist_eq_zero n A x.1 y.1 hdist_zero
    have hev_R : ∀ᶠ R : Real in Filter.atTop, (1 : Real) <= R :=
      Filter.eventually_ge_atTop (α := Real) 1
    filter_upwards [hev_R] with R hR
    have hmap :
        gaussianFiniteSubsetMap n A R E x = gaussianFiniteSubsetMap n A R E y := by
      simp [gaussianFiniteSubsetMap, hxy]
    have htarget_zero :
        dist (gaussianFiniteSubsetMap n A R E x) (gaussianFiniteSubsetMap n A R E y) = 0 := by
      rw [hmap, dist_self]
    refine ⟨hR, ?_, ?_⟩
    · simp [hdist_zero, htarget_zero]
    · simp [hdist_zero, htarget_zero]

private theorem gaussianFiniteSubsetMap_distortion
    (n : Nat) (A : LatticeBasis n)
    (E : Finset (flatTorus n A)) (eps : Real) (heps : 0 < eps)
    (hCorr : GaussianCorrelationAsymptoticStatement n A) :
    (letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A;
      letI : PseudoMetricSpace (higherRankSphereQuotient n) := higherRankChordalMetric n;
      exists R : Real, 1 <= R /\
        forall x y : {x : flatTorus n A // x ∈ E},
          (1 - eps) * gaussianEmbeddingScale R * dist x.1 y.1 <=
            dist (gaussianFiniteSubsetMap n A R E x) (gaussianFiniteSubsetMap n A R E y) /\
          dist (gaussianFiniteSubsetMap n A R E x) (gaussianFiniteSubsetMap n A R E y) <=
            (1 + eps) * gaussianEmbeddingScale R * dist x.1 y.1) := by
  classical
  letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A
  letI : PseudoMetricSpace (higherRankSphereQuotient n) := higherRankChordalMetric n
  obtain ⟨C, hC, hEst⟩ :=
    higherRankTranslatedGaussianCorrelationAsymptotic n A 4 (by norm_num) hCorr
  let X := {x : flatTorus n A // x ∈ E}
  have hpair : ∀ p : X × X,
      ∀ᶠ R in Filter.atTop,
        1 <= R /\
          (1 - eps) * gaussianEmbeddingScale R * dist p.1.1 p.2.1 <=
              dist (gaussianFiniteSubsetMap n A R E p.1)
                (gaussianFiniteSubsetMap n A R E p.2) /\
            dist (gaussianFiniteSubsetMap n A R E p.1)
                (gaussianFiniteSubsetMap n A R E p.2) <=
              (1 + eps) * gaussianEmbeddingScale R * dist p.1.1 p.2.1 := by
    intro p
    simpa [X] using
      gaussianFiniteSubsetMap_pair_distortion_eventually n A E hC heps hEst p.1 p.2
  have hall :
      ∀ᶠ R in Filter.atTop, ∀ p : X × X,
        1 <= R /\
          (1 - eps) * gaussianEmbeddingScale R * dist p.1.1 p.2.1 <=
              dist (gaussianFiniteSubsetMap n A R E p.1)
                (gaussianFiniteSubsetMap n A R E p.2) /\
            dist (gaussianFiniteSubsetMap n A R E p.1)
                (gaussianFiniteSubsetMap n A R E p.2) <=
              (1 + eps) * gaussianEmbeddingScale R * dist p.1.1 p.2.1 := by
    simpa using (Filter.eventually_all (ι := X × X)).2 hpair
  have hallR :
      ∀ᶠ R in Filter.atTop,
        (∀ p : X × X,
          1 <= R /\
            (1 - eps) * gaussianEmbeddingScale R * dist p.1.1 p.2.1 <=
                dist (gaussianFiniteSubsetMap n A R E p.1)
                  (gaussianFiniteSubsetMap n A R E p.2) /\
              dist (gaussianFiniteSubsetMap n A R E p.1)
                  (gaussianFiniteSubsetMap n A R E p.2) <=
                (1 + eps) * gaussianEmbeddingScale R * dist p.1.1 p.2.1) /\
          1 <= R :=
    hall.and (Filter.eventually_ge_atTop (α := Real) 1)
  rcases hallR.exists with ⟨R, hRall, hR⟩
  refine ⟨R, hR, ?_⟩
  intro x y
  exact (hRall (x, y)).2

/--
Every finite subset of a flat torus embeds into the corresponding higher-rank
sphere quotient with arbitrarily small bilipschitz loss.
-/
theorem flatTorusFiniteSubsetEmbedsInHigherRankSphereQuotient
    (n : Nat) (A : LatticeBasis n)
    (E : Finset (flatTorus n A)) (eps : Real) (heps : 0 < eps) :
    (letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A;
      letI : PseudoMetricSpace (higherRankSphereQuotient n) := higherRankChordalMetric n;
      FiniteMetricEmbedsWithScaleError (higherRankSphereQuotient n) E eps) := by
  classical
  letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A
  letI : PseudoMetricSpace (higherRankSphereQuotient n) := higherRankChordalMetric n
  have hCorr : GaussianCorrelationAsymptoticStatement n A := by
    intro N hN
    simpa [GaussianCorrelationAsymptoticStatement, gaussianCorrelationKernel] using
      gaussianCorrelationAsymptotic n A N hN
  obtain ⟨R, hR, hdist⟩ := gaussianFiniteSubsetMap_distortion n A E eps heps hCorr
  refine ⟨gaussianFiniteSubsetMap n A R E, gaussianEmbeddingScale R, ?_, hdist⟩
  exact gaussianEmbeddingScale_pos (lt_of_lt_of_le zero_lt_one hR)

end

end SphereObstructionHilbertShiftQuotient
