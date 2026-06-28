import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import SphereObstructionHilbertShiftQuotient.Distortion

set_option linter.style.header false

/-!
Flat torus inputs.

This file names the flat tori with unit lattice, their metric, and the
Khot--Naor lower-bound input used in the main obstruction.
-/

namespace SphereObstructionHilbertShiftQuotient

open MeasureTheory

open scoped Pointwise Topology

universe u v

noncomputable section

/-- An invertible real matrix used as a lattice basis for the flat torus metric. -/
structure LatticeBasis (n : Nat) where
  /-- The matrix whose columns encode the lattice basis. -/
  matrix : Matrix (Fin n) (Fin n) Real
  /-- The lattice basis matrix has invertible determinant. -/
  invertible : IsUnit matrix.det

private noncomputable def standardLatticeBasis (n : Nat) : LatticeBasis n where
  matrix := 1
  invertible := by simp

private noncomputable def integerVector (n : Nat) (k : Fin n -> Int) : RealEuclideanSpace n :=
  WithLp.toLp 2 (fun i : Fin n => (k i : Real))

private noncomputable def integerLattice (n : Nat) : AddSubgroup (RealEuclideanSpace n) where
  carrier := {x | exists k : Fin n -> Int, x = integerVector n k}
  zero_mem' := by
    refine ⟨0, ?_⟩
    ext i
    simp [integerVector]
  add_mem' := by
    intro x y hx hy
    rcases hx with ⟨kx, rfl⟩
    rcases hy with ⟨ky, rfl⟩
    refine ⟨kx + ky, ?_⟩
    ext i
    simp [integerVector]
  neg_mem' := by
    intro x hx
    rcases hx with ⟨kx, rfl⟩
    refine ⟨-kx, ?_⟩
    ext i
    simp [integerVector]

private noncomputable def matrixIntegerLattice (n : Nat) (A : LatticeBasis n) :
    AddSubgroup (RealEuclideanSpace n) :=
  (integerLattice n).map (Matrix.toEuclideanLin A.matrix).toAddMonoidHom

/-- The flat torus with coordinate lattice and metric encoded by `A`. -/
noncomputable def flatTorus (n : Nat) (A : LatticeBasis n) : Type :=
  let _metricEncoding := A
  RealEuclideanSpace n ⧸ integerLattice n

/-- The Euclidean norm square associated to a matrix `A`. -/
noncomputable def matrixNormSq
    (n : Nat) (A : LatticeBasis n) (x : RealEuclideanSpace n) : Real :=
  ‖Matrix.toEuclideanLin A.matrix x‖ ^ 2

@[reducible]
private noncomputable def flatTorusAmbientSeminorm
    (n : Nat) (A : LatticeBasis n) : SeminormedAddCommGroup (RealEuclideanSpace n) :=
  SeminormedAddCommGroup.induced (RealEuclideanSpace n) (RealEuclideanSpace n)
    (Matrix.toEuclideanLin A.matrix)

private lemma continuous_id_standard_to_flatTorusAmbient {n : Nat} (A : LatticeBasis n) :
    @Continuous (RealEuclideanSpace n) (RealEuclideanSpace n)
      inferInstance
      (@UniformSpace.toTopologicalSpace (RealEuclideanSpace n)
        (@PseudoMetricSpace.toUniformSpace (RealEuclideanSpace n)
          (flatTorusAmbientSeminorm n A).toPseudoMetricSpace))
      id := by
  rw [continuous_induced_rng]
  simpa using LinearMap.continuous_of_finiteDimensional (Matrix.toEuclideanLin A.matrix)

/-- The flat quotient metric on `R^n / Z^n` with matrix `A`. -/
@[reducible]
noncomputable def flatTorusMetric
    (n : Nat) (A : LatticeBasis n) : PseudoMetricSpace (flatTorus n A) := by
  letI : SeminormedAddCommGroup (RealEuclideanSpace n) := flatTorusAmbientSeminorm n A
  change PseudoMetricSpace (RealEuclideanSpace n ⧸ integerLattice n)
  infer_instance

/-- The corresponding quotient `R^n / A Z^n`. -/
noncomputable def flatTorusEuclideanLatticeQuotient
    (n : Nat) (A : LatticeBasis n) : Type :=
  RealEuclideanSpace n ⧸ matrixIntegerLattice n A

/-- The flat metric on `R^n / A Z^n`. -/
@[reducible]
noncomputable def flatTorusEuclideanLatticeMetric
    (n : Nat) (A : LatticeBasis n) :
    PseudoMetricSpace (flatTorusEuclideanLatticeQuotient n A) := by
  change PseudoMetricSpace (RealEuclideanSpace n ⧸ matrixIntegerLattice n A)
  infer_instance

/-!
### Khot--Naor lower-bound scaffold

The declarations in this section mirror the self-contained proof in
`scratch/khot_naor.tex`.  The hard analytic, geometry-of-numbers, and
Construction-A assertions are stated as Lean work units; later passes can prove
the remaining work units one lemma at a time without changing the public
`khotNaorFlatTorusLowerBound` statement.
-/

/-- A represented full-rank lattice in `R^n`, recorded by a project lattice basis. -/
structure KNFullRankLattice (n : Nat) where
  /-- A basis matrix for the lattice. -/
  basis : LatticeBasis n

namespace KNFullRankLattice

/-- The additive subgroup associated to a represented full-rank lattice. -/
noncomputable def carrier {n : Nat} (Λ : KNFullRankLattice n) :
    AddSubgroup (RealEuclideanSpace n) :=
  matrixIntegerLattice n Λ.basis

/-- The determinant/covolume of a represented matrix lattice. -/
noncomputable def det {n : Nat} (Λ : KNFullRankLattice n) : Real :=
  |Λ.basis.matrix.det|

/-- The project flat torus associated to a represented full-rank lattice. -/
noncomputable def torus {n : Nat} (Λ : KNFullRankLattice n) : Type :=
  flatTorus n Λ.basis

/-- The project metric on the torus associated to a represented full-rank lattice. -/
@[reducible]
noncomputable def torusMetric {n : Nat} (Λ : KNFullRankLattice n) :
    PseudoMetricSpace Λ.torus :=
  flatTorusMetric n Λ.basis

end KNFullRankLattice

/-- The matrix lattice `A Z^n`, as an additive subgroup of Euclidean space. -/
noncomputable def matrixLattice (n : Nat) (A : LatticeBasis n) :
    AddSubgroup (RealEuclideanSpace n) :=
  matrixIntegerLattice n A

/-- The closed unit cube in the coordinate model of `R^n`. -/
def closedUnitCube (n : Nat) : Set (RealEuclideanSpace n) :=
  {x | ∀ i : Fin n, 0 ≤ x i ∧ x i ≤ 1}

/-- The closed fundamental parallelepiped `A [0,1]^n`. -/
noncomputable def closedFundamentalParallelepiped
    (n : Nat) (A : LatticeBasis n) : Set (RealEuclideanSpace n) :=
  (Matrix.toEuclideanLin A.matrix) '' closedUnitCube n

/-- Real numbers that are integers. -/
def IsIntegerReal (x : Real) : Prop :=
  ∃ z : Int, x = z

/-- The dual-lattice relation used in the Khot--Naor scaffold. -/
def IsDualLattice {n : Nat} (Λ Λstar : KNFullRankLattice n) : Prop :=
  ∀ u : RealEuclideanSpace n,
    u ∈ Λstar.carrier ↔
      ∀ v : RealEuclideanSpace n, v ∈ Λ.carrier -> IsIntegerReal (inner Real u v)

private def intStdBasis {n : Nat} (i : Fin n) : Fin n -> Int :=
  Pi.single i 1

private lemma inverseTranspose_inner_integer {n : Nat}
    (A : Matrix (Fin n) (Fin n) Real) (hA : IsUnit A.det)
    (k l : Fin n -> Int) :
    IsIntegerReal (inner Real
      (Matrix.toEuclideanLin A⁻¹.transpose (integerVector n k))
      (Matrix.toEuclideanLin A (integerVector n l))) := by
  let kR : Fin n -> Real := fun i => (k i : Real)
  let lR : Fin n -> Real := fun i => (l i : Real)
  refine ⟨∑ i, k i * l i, ?_⟩
  have hdot : dotProduct (A.mulVec lR) (A⁻¹.transpose.mulVec kR) = dotProduct kR lR := by
    calc
      dotProduct (A.mulVec lR) (A⁻¹.transpose.mulVec kR) =
          dotProduct kR (A⁻¹.mulVec (A.mulVec lR)) := by
            rw [Matrix.dotProduct_transpose_mulVec]
      _ = dotProduct kR ((A⁻¹ * A).mulVec lR) := by
            rw [Matrix.mulVec_mulVec]
      _ = dotProduct kR lR := by
            rw [Matrix.nonsing_inv_mul A hA]
            simp
  calc
    inner Real (Matrix.toEuclideanLin A⁻¹.transpose (integerVector n k))
        (Matrix.toEuclideanLin A (integerVector n l)) =
        dotProduct (A.mulVec lR) (A⁻¹.transpose.mulVec kR) := by
          simp [integerVector, kR, lR, PiLp.inner_apply, dotProduct, mul_comm]
    _ = dotProduct kR lR := hdot
    _ = (∑ i, k i * l i : Int) := by
          simp [dotProduct, kR, lR, Int.cast_sum, Int.cast_mul]

private lemma inner_matrix_intStdBasis {n : Nat}
    (A : Matrix (Fin n) (Fin n) Real) (u : RealEuclideanSpace n) (i : Fin n) :
    inner Real u (Matrix.toEuclideanLin A (integerVector n (intStdBasis i))) =
      (A.transpose.mulVec (fun j => u j)) i := by
  simp [integerVector, intStdBasis, PiLp.inner_apply, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, Pi.single_apply]

private lemma inverseTranspose_transpose_apply {n : Nat}
    (A : Matrix (Fin n) (Fin n) Real) (hA : IsUnit A.det)
    (u : RealEuclideanSpace n) :
    Matrix.toEuclideanLin A⁻¹.transpose
        (WithLp.toLp 2 (A.transpose.mulVec (fun j => u j)) : RealEuclideanSpace n) = u := by
  ext i
  change ((A⁻¹.transpose).mulVec (A.transpose.mulVec fun j => u j)) i = u i
  rw [Matrix.mulVec_mulVec]
  have hmul : A⁻¹.transpose * A.transpose = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv A hA, Matrix.transpose_one]
  rw [hmul]
  simp

private lemma inner_inverseTranspose_intStdBasis {n : Nat}
    (A : Matrix (Fin n) (Fin n) Real) (u : RealEuclideanSpace n) (i : Fin n) :
    inner Real u (Matrix.toEuclideanLin A⁻¹.transpose (integerVector n (intStdBasis i))) =
      (A⁻¹.mulVec (fun j => u j)) i := by
  simp [integerVector, intStdBasis, PiLp.inner_apply, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, Pi.single_apply]

private lemma matrix_inverse_apply {n : Nat}
    (A : Matrix (Fin n) (Fin n) Real) (hA : IsUnit A.det)
    (u : RealEuclideanSpace n) :
    Matrix.toEuclideanLin A
        (WithLp.toLp 2 (A⁻¹.mulVec (fun j => u j)) : RealEuclideanSpace n) = u := by
  ext i
  change (A.mulVec (A⁻¹.mulVec fun j => u j)) i = u i
  rw [Matrix.mulVec_mulVec]
  rw [Matrix.mul_nonsing_inv A hA]
  simp

private noncomputable def dualLatticeBasis {n : Nat} (A : LatticeBasis n) :
    LatticeBasis n where
  matrix := A.matrix⁻¹.transpose
  invertible := by
    rw [Matrix.det_transpose]
    exact Matrix.isUnit_nonsing_inv_det A.matrix A.invertible

private theorem dualLatticeBasis_spec {n : Nat} (Λ : KNFullRankLattice n) :
    IsDualLattice Λ ⟨dualLatticeBasis Λ.basis⟩ := by
  classical
  intro u
  simp [KNFullRankLattice.carrier, matrixIntegerLattice, dualLatticeBasis, integerLattice]
  constructor
  · rintro ⟨k, rfl⟩ l
    exact inverseTranspose_inner_integer Λ.basis.matrix Λ.basis.invertible k l
  · intro h
    let hcoord : ∀ i : Fin n, IsIntegerReal
        ((Λ.basis.matrix.transpose.mulVec (fun j => u j)) i) := by
      intro i
      simpa [inner_matrix_intStdBasis] using h (intStdBasis i)
    let k : Fin n -> Int := fun i => Classical.choose (hcoord i)
    have hk : ∀ i : Fin n, (Λ.basis.matrix.transpose.mulVec (fun j => u j)) i =
        (k i : Real) := by
      intro i
      exact Classical.choose_spec (hcoord i)
    refine ⟨k, ?_⟩
    have hvec :
        integerVector n k =
          (WithLp.toLp 2 (Λ.basis.matrix.transpose.mulVec (fun j => u j)) :
            RealEuclideanSpace n) := by
      ext i
      change (k i : Real) = (Λ.basis.matrix.transpose.mulVec (fun j => u j)) i
      exact (hk i).symm
    rw [hvec]
    exact inverseTranspose_transpose_apply Λ.basis.matrix Λ.basis.invertible u

/-- Every represented full-rank lattice has a represented dual lattice. -/
theorem knDualLattice_exists {n : Nat} (Λ : KNFullRankLattice n) :
    ∃ Λstar : KNFullRankLattice n, IsDualLattice Λ Λstar := by
  exact ⟨⟨dualLatticeBasis Λ.basis⟩, dualLatticeBasis_spec Λ⟩

/-- The represented dual lattice. -/
noncomputable def knDualLattice {n : Nat} (Λ : KNFullRankLattice n) :
    KNFullRankLattice n :=
  ⟨dualLatticeBasis Λ.basis⟩

/-- The represented dual lattice satisfies the dual-lattice relation. -/
theorem knDualLattice_spec {n : Nat} (Λ : KNFullRankLattice n) :
    IsDualLattice Λ (knDualLattice Λ) :=
  dualLatticeBasis_spec Λ

/-- Full-rank lattices are represented by matrix lattices in this scaffold model. -/
theorem fullRankLattice_carrier_eq_matrixLattice {n : Nat} (Λ : KNFullRankLattice n) :
    Λ.carrier = matrixLattice n Λ.basis := by
  rfl

/-- Change of basis preserves the represented matrix lattice exactly when the bases agree. -/
theorem matrixLattice_basis_change
    {n : Nat} {A B : LatticeBasis n} (h : A.matrix = B.matrix) :
    matrixLattice n A = matrixLattice n B := by
  cases A
  cases B
  simp_all [matrixLattice, matrixIntegerLattice]

/-- The determinant of the represented lattice is basis-independent. -/
theorem matrixLattice_det_wellDefined {n : Nat} (Λ : KNFullRankLattice n) :
    0 ≤ Λ.det := by
  exact abs_nonneg _

/-- The double-dual lattice agrees with the original represented lattice. -/
theorem knDoubleDual {n : Nat} (Λ : KNFullRankLattice n) :
    IsDualLattice (knDualLattice Λ) Λ := by
  classical
  intro u
  constructor
  · intro hu v hv
    simpa [real_inner_comm] using (knDualLattice_spec Λ v).1 hv u hu
  · intro h
    simp [KNFullRankLattice.carrier, matrixIntegerLattice, integerLattice]
    let hcoord : ∀ i : Fin n, IsIntegerReal ((Λ.basis.matrix⁻¹.mulVec (fun j => u j)) i) := by
      intro i
      let w : RealEuclideanSpace n :=
        Matrix.toEuclideanLin Λ.basis.matrix⁻¹.transpose (integerVector n (intStdBasis i))
      have hw : w ∈ (knDualLattice Λ).carrier := by
        refine (knDualLattice_spec Λ w).2 ?_
        intro v hv
        simp [KNFullRankLattice.carrier, matrixIntegerLattice, integerLattice] at hv
        rcases hv with ⟨l, rfl⟩
        exact inverseTranspose_inner_integer Λ.basis.matrix Λ.basis.invertible
          (intStdBasis i) l
      simpa [w, inner_inverseTranspose_intStdBasis] using h w hw
    let k : Fin n -> Int := fun i => Classical.choose (hcoord i)
    have hk : ∀ i : Fin n, (Λ.basis.matrix⁻¹.mulVec (fun j => u j)) i =
        (k i : Real) := by
      intro i
      exact Classical.choose_spec (hcoord i)
    refine ⟨k, ?_⟩
    have hvec :
        integerVector n k =
          (WithLp.toLp 2 (Λ.basis.matrix⁻¹.mulVec (fun j => u j)) :
            RealEuclideanSpace n) := by
      ext i
      change (k i : Real) = (Λ.basis.matrix⁻¹.mulVec (fun j => u j)) i
      exact (hk i).symm
    rw [hvec]
    exact matrix_inverse_apply Λ.basis.matrix Λ.basis.invertible u

/-- The determinant of a represented lattice and of its dual multiply to `1`. -/
theorem knDet_mul_dualDet {n : Nat} (Λ : KNFullRankLattice n) :
    Λ.det * (knDualLattice Λ).det = 1 := by
  have hdet : Λ.basis.matrix.det ≠ 0 := IsUnit.ne_zero Λ.basis.invertible
  simp [KNFullRankLattice.det, knDualLattice, dualLatticeBasis, Matrix.det_transpose,
    Matrix.det_nonsing_inv, hdet]

/-- Distance from a Euclidean point to a represented full-rank lattice. -/
noncomputable def distanceToLattice {n : Nat}
    (Λ : KNFullRankLattice n) (x : RealEuclideanSpace n) : Real :=
  sInf ((fun γ : RealEuclideanSpace n => ‖x - γ‖) '' (Λ.carrier : Set (RealEuclideanSpace n)))

/-- The shortest nonzero vector length `N(Λ)`. -/
noncomputable def shortestVectorLength {n : Nat} (Λ : KNFullRankLattice n) : Real :=
  sInf {r : Real |
    ∃ γ : RealEuclideanSpace n, γ ∈ Λ.carrier ∧ γ ≠ 0 ∧ r = ‖γ‖}

/-- The covering radius `r(Λ)`. -/
noncomputable def coveringRadius {n : Nat} (Λ : KNFullRankLattice n) : Real :=
  sSup (Set.range (distanceToLattice Λ))

/-- A closed Voronoi-cell predicate centered at the origin. -/
def InClosedVoronoiCell {n : Nat}
    (Λ : KNFullRankLattice n) (x : RealEuclideanSpace n) : Prop :=
  ∀ γ : RealEuclideanSpace n, γ ∈ Λ.carrier -> ‖x‖ ≤ ‖x - γ‖

private noncomputable def euclideanStdBasis (n : Nat) :
    Module.Basis (Fin n) Real (RealEuclideanSpace n) :=
  (EuclideanSpace.basisFun (Fin n) Real).toBasis

private noncomputable def standardIntegerSubmodule (n : Nat) :
    Submodule ℤ (RealEuclideanSpace n) :=
  Submodule.span ℤ (Set.range (euclideanStdBasis n))

private lemma integerVector_mem_standardIntegerSubmodule
    (n : Nat) (k : Fin n -> Int) :
    integerVector n k ∈ standardIntegerSubmodule n := by
  classical
  rw [standardIntegerSubmodule]
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨k, ?_⟩
  ext i
  simp [integerVector, euclideanStdBasis]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Pi.single_eq_of_ne]
    · simp
    · exact fun h => hj h.symm
  · intro hi
    simp at hi

private lemma integerLattice_eq_standardIntegerSubmodule (n : Nat) :
    integerLattice n = (standardIntegerSubmodule n).toAddSubgroup := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    exact integerVector_mem_standardIntegerSubmodule n k
  · intro hx
    change x ∈ standardIntegerSubmodule n at hx
    rw [standardIntegerSubmodule] at hx
    rw [Submodule.mem_span_range_iff_exists_fun] at hx
    rcases hx with ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    ext i
    simp [integerVector, euclideanStdBasis]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [Pi.single_eq_of_ne]
      · simp
      · exact fun h => hj h.symm
    · intro hi
      simp at hi

@[reducible]
private noncomputable def KNFullRankLattice.torusSeminormedAddCommGroup {n : Nat}
    (Λ : KNFullRankLattice n) : SeminormedAddCommGroup Λ.torus := by
  letI : SeminormedAddCommGroup (RealEuclideanSpace n) := flatTorusAmbientSeminorm n Λ.basis
  dsimp [KNFullRankLattice.torus, flatTorus]
  infer_instance

private theorem KNFullRankLattice.torus_compactSpace {n : Nat} (Λ : KNFullRankLattice n) :
    letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
    CompactSpace Λ.torus := by
  letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
  rw [← isCompact_univ_iff]
  let L : Submodule ℤ (RealEuclideanSpace n) :=
    Submodule.span ℤ (Set.range (euclideanStdBasis n))
  haveI : DiscreteTopology L := by infer_instance
  haveI : IsZLattice ℝ L := by infer_instance
  let q : RealEuclideanSpace n → Λ.torus :=
    letI : SeminormedAddCommGroup (RealEuclideanSpace n) := flatTorusAmbientSeminorm n Λ.basis
    (integerLattice n).normedMk
  have hid_cont := continuous_id_standard_to_flatTorusAmbient Λ.basis
  have hq_cont : Continuous q := by
    change @Continuous (RealEuclideanSpace n) Λ.torus inferInstance
      (@UniformSpace.toTopologicalSpace Λ.torus
        (@PseudoMetricSpace.toUniformSpace Λ.torus
          (Λ.torusSeminormedAddCommGroup.toPseudoMetricSpace))) q
    letI : SeminormedAddCommGroup (RealEuclideanSpace n) :=
      flatTorusAmbientSeminorm n Λ.basis
    have hmk_cont : @Continuous (RealEuclideanSpace n) Λ.torus
        (@UniformSpace.toTopologicalSpace (RealEuclideanSpace n)
          (@PseudoMetricSpace.toUniformSpace (RealEuclideanSpace n)
            (flatTorusAmbientSeminorm n Λ.basis).toPseudoMetricSpace))
        (@UniformSpace.toTopologicalSpace Λ.torus
          (@PseudoMetricSpace.toUniformSpace Λ.torus
            (Λ.torusSeminormedAddCommGroup.toPseudoMetricSpace)))
        ((integerLattice n).normedMk : RealEuclideanSpace n → Λ.torus) := by
      simpa [KNFullRankLattice.torusSeminormedAddCommGroup, KNFullRankLattice.torus,
        flatTorus] using (integerLattice n).normedMk.continuous
    simpa [Function.comp_def, q] using
      (@Continuous.comp (RealEuclideanSpace n) (RealEuclideanSpace n) Λ.torus
        inferInstance
        (@UniformSpace.toTopologicalSpace (RealEuclideanSpace n)
          (@PseudoMetricSpace.toUniformSpace (RealEuclideanSpace n)
            (flatTorusAmbientSeminorm n Λ.basis).toPseudoMetricSpace))
        (@UniformSpace.toTopologicalSpace Λ.torus
          (@PseudoMetricSpace.toUniformSpace Λ.torus
            (Λ.torusSeminormedAddCommGroup.toPseudoMetricSpace)))
        id ((integerLattice n).normedMk : RealEuclideanSpace n → Λ.torus)
        hmk_cont hid_cont)
  have hcomp : IsCompact (Set.range q) := by
    refine IsZLattice.isCompact_range_of_periodic L q hq_cont ?_
    intro z w hw
    change (QuotientAddGroup.mk' (integerLattice n) (z + w) :
        RealEuclideanSpace n ⧸ integerLattice n) =
      QuotientAddGroup.mk' (integerLattice n) z
    rw [QuotientAddGroup.mk'_eq_mk']
    refine ⟨-w, ?_, by abel⟩
    have hw' : w ∈ integerLattice n := by
      simpa [integerLattice_eq_standardIntegerSubmodule n, L, standardIntegerSubmodule] using hw
    exact (integerLattice n).neg_mem hw'
  have hrange : Set.range q = Set.univ := by
    ext y
    constructor
    · intro _
      trivial
    · intro _
      refine QuotientAddGroup.induction_on y ?_
      intro x
      exact ⟨x, rfl⟩
  simpa [hrange] using hcomp

@[reducible]
private noncomputable def KNFullRankLattice.torusLocallyCompactSpace {n : Nat}
    (Λ : KNFullRankLattice n) :
    letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
    LocallyCompactSpace Λ.torus := by
  letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
  haveI : CompactSpace Λ.torus := Λ.torus_compactSpace
  infer_instance

private noncomputable def torusHaarMeasure {n : Nat}
    (Λ : KNFullRankLattice n) :
    letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
    letI : MeasurableSpace Λ.torus := borel Λ.torus
    MeasureTheory.Measure Λ.torus :=
  letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
  letI : MeasurableSpace Λ.torus := borel Λ.torus
  haveI : BorelSpace Λ.torus := ⟨rfl⟩
  haveI : LocallyCompactSpace Λ.torus := Λ.torusLocallyCompactSpace
  let μ : MeasureTheory.Measure Λ.torus := MeasureTheory.Measure.addHaar
  (μ Set.univ)⁻¹ • μ

private lemma torus_addHaar_measure_univ_ne_zero {n : Nat}
    (Λ : KNFullRankLattice n) :
    letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
    letI : MeasurableSpace Λ.torus := borel Λ.torus
    letI : BorelSpace Λ.torus := ⟨rfl⟩
    letI : LocallyCompactSpace Λ.torus := Λ.torusLocallyCompactSpace
    (MeasureTheory.Measure.addHaar (G := Λ.torus)) Set.univ ≠ 0 := by
  letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
  letI : MeasurableSpace Λ.torus := borel Λ.torus
  letI : BorelSpace Λ.torus := ⟨rfl⟩
  letI : LocallyCompactSpace Λ.torus := Λ.torusLocallyCompactSpace
  haveI : CompactSpace Λ.torus := Λ.torus_compactSpace
  haveI : (MeasureTheory.Measure.addHaar (G := Λ.torus)).IsAddHaarMeasure := by
    infer_instance
  haveI : NeZero (MeasureTheory.Measure.addHaar (G := Λ.torus)) := by
    infer_instance
  exact (MeasureTheory.Measure.measure_univ_pos.mpr
    (NeZero.ne (MeasureTheory.Measure.addHaar (G := Λ.torus)))).ne'

private lemma torus_addHaar_measure_univ_ne_top {n : Nat}
    (Λ : KNFullRankLattice n) :
    letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
    letI : MeasurableSpace Λ.torus := borel Λ.torus
    letI : BorelSpace Λ.torus := ⟨rfl⟩
    letI : LocallyCompactSpace Λ.torus := Λ.torusLocallyCompactSpace
    (MeasureTheory.Measure.addHaar (G := Λ.torus)) Set.univ ≠ (⊤ : ENNReal) := by
  letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
  letI : MeasurableSpace Λ.torus := borel Λ.torus
  letI : BorelSpace Λ.torus := ⟨rfl⟩
  letI : LocallyCompactSpace Λ.torus := Λ.torusLocallyCompactSpace
  haveI : CompactSpace Λ.torus := Λ.torus_compactSpace
  haveI : (MeasureTheory.Measure.addHaar (G := Λ.torus)).IsAddHaarMeasure := by
    infer_instance
  exact ne_of_lt
    (MeasureTheory.IsFiniteMeasureOnCompacts.lt_top_of_isCompact isCompact_univ)

private theorem torusHaarMeasure_isAddHaarMeasure {n : Nat}
    (Λ : KNFullRankLattice n) :
    letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
    letI : MeasurableSpace Λ.torus := borel Λ.torus
    letI : BorelSpace Λ.torus := ⟨rfl⟩
    letI : LocallyCompactSpace Λ.torus := Λ.torusLocallyCompactSpace
    (torusHaarMeasure Λ).IsAddHaarMeasure := by
  letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
  letI : MeasurableSpace Λ.torus := borel Λ.torus
  letI : BorelSpace Λ.torus := ⟨rfl⟩
  letI : LocallyCompactSpace Λ.torus := Λ.torusLocallyCompactSpace
  haveI : CompactSpace Λ.torus := Λ.torus_compactSpace
  dsimp [torusHaarMeasure]
  let μ : MeasureTheory.Measure Λ.torus := MeasureTheory.Measure.addHaar
  haveI : μ.IsAddHaarMeasure := by
    dsimp [μ]
    infer_instance
  have hμ0 : μ Set.univ ≠ 0 := by
    exact torus_addHaar_measure_univ_ne_zero Λ
  have hμtop : μ Set.univ ≠ (⊤ : ENNReal) := by
    exact torus_addHaar_measure_univ_ne_top Λ
  exact MeasureTheory.Measure.IsAddHaarMeasure.smul (μ := μ)
    (cpos := ENNReal.inv_ne_zero.mpr hμtop) (ctop := ENNReal.inv_ne_top.mpr hμ0)

private theorem torusHaarMeasure_isProbability {n : Nat}
    (Λ : KNFullRankLattice n) :
    letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
    letI : MeasurableSpace Λ.torus := borel Λ.torus
    MeasureTheory.IsProbabilityMeasure (torusHaarMeasure Λ) := by
  letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
  letI : MeasurableSpace Λ.torus := borel Λ.torus
  haveI : BorelSpace Λ.torus := ⟨rfl⟩
  haveI : LocallyCompactSpace Λ.torus := Λ.torusLocallyCompactSpace
  haveI : CompactSpace Λ.torus := Λ.torus_compactSpace
  dsimp [torusHaarMeasure]
  let μ : MeasureTheory.Measure Λ.torus := MeasureTheory.Measure.addHaar
  have hμ0 : μ Set.univ ≠ 0 := by
    exact torus_addHaar_measure_univ_ne_zero Λ
  have hμtop : μ Set.univ ≠ (⊤ : ENNReal) := by
    exact torus_addHaar_measure_univ_ne_top Λ
  refine MeasureTheory.IsProbabilityMeasure.mk ?_
  simp

private theorem torusHaarMeasure_measurePreserving_add_left {n : Nat}
    (Λ : KNFullRankLattice n) (a : Λ.torus) :
    letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
    letI : MeasurableSpace Λ.torus := borel Λ.torus
    MeasureTheory.MeasurePreserving
      (fun x : Λ.torus => a + x) (torusHaarMeasure Λ) (torusHaarMeasure Λ) := by
  letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
  letI : MeasurableSpace Λ.torus := borel Λ.torus
  haveI : BorelSpace Λ.torus := ⟨rfl⟩
  haveI : LocallyCompactSpace Λ.torus := Λ.torusLocallyCompactSpace
  haveI : (torusHaarMeasure Λ).IsAddHaarMeasure := torusHaarMeasure_isAddHaarMeasure Λ
  exact MeasureTheory.measurePreserving_add_left (torusHaarMeasure Λ) a

private theorem torusHaarMeasure_measurePreserving_neg {n : Nat}
    (Λ : KNFullRankLattice n) :
    letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
    letI : MeasurableSpace Λ.torus := borel Λ.torus
    MeasureTheory.MeasurePreserving
      (fun x : Λ.torus => -x) (torusHaarMeasure Λ) (torusHaarMeasure Λ) := by
  letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
  letI : MeasurableSpace Λ.torus := borel Λ.torus
  haveI : BorelSpace Λ.torus := ⟨rfl⟩
  haveI : LocallyCompactSpace Λ.torus := Λ.torusLocallyCompactSpace
  haveI : (torusHaarMeasure Λ).IsAddHaarMeasure := torusHaarMeasure_isAddHaarMeasure Λ
  dsimp [torusHaarMeasure]
  let μ : MeasureTheory.Measure Λ.torus := MeasureTheory.Measure.addHaar
  haveI : μ.IsNegInvariant := by
    dsimp [μ]
    infer_instance
  haveI : ((μ Set.univ)⁻¹ • μ).IsNegInvariant := by
    constructor
    rw [MeasureTheory.Measure.neg_def, MeasureTheory.Measure.map_smul,
      MeasureTheory.Measure.map_neg_eq_self]
  exact MeasureTheory.Measure.measurePreserving_neg ((μ Set.univ)⁻¹ • μ)

private theorem torusHaarMeasure_measurePreserving_sub_left {n : Nat}
    (Λ : KNFullRankLattice n) (a : Λ.torus) :
    letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
    letI : MeasurableSpace Λ.torus := borel Λ.torus
    MeasureTheory.MeasurePreserving
      (fun x : Λ.torus => a - x) (torusHaarMeasure Λ) (torusHaarMeasure Λ) := by
  letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
  letI : MeasurableSpace Λ.torus := borel Λ.torus
  simpa [sub_eq_add_neg, Function.comp_def] using
    (torusHaarMeasure_measurePreserving_add_left Λ a).comp
      (torusHaarMeasure_measurePreserving_neg Λ)

private theorem flatTorus_haar_difference_continuous {n : Nat}
    (Λ : KNFullRankLattice n) (ψ : Λ.torus -> Real)
    (_hψ :
      letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
      Continuous ψ) :
    letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
    letI : MeasurableSpace Λ.torus := borel Λ.torus
    (∫ x, ∫ y, ψ (x - y) ∂torusHaarMeasure Λ ∂torusHaarMeasure Λ) =
      ∫ z, ψ z ∂torusHaarMeasure Λ := by
  letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
  letI : MeasurableSpace Λ.torus := borel Λ.torus
  haveI : BorelSpace Λ.torus := ⟨rfl⟩
  haveI : MeasurableAdd Λ.torus := ⟨fun _ => by fun_prop, fun _ => by fun_prop⟩
  haveI : MeasurableNeg Λ.torus := ⟨by fun_prop⟩
  haveI : MeasureTheory.IsProbabilityMeasure (torusHaarMeasure Λ) :=
    torusHaarMeasure_isProbability Λ
  have hinner :
      ∀ x : Λ.torus, (∫ y, ψ (x - y) ∂torusHaarMeasure Λ) =
        ∫ z, ψ z ∂torusHaarMeasure Λ := by
    intro x
    exact (torusHaarMeasure_measurePreserving_sub_left Λ x).integral_comp
      (measurableEmbedding_subLeft x) ψ
  simp_rw [hinner]
  simp

private theorem flatTorus_haar_difference_dist_sq {n : Nat}
    (Λ : KNFullRankLattice n) :
    letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
    letI : MeasurableSpace Λ.torus := borel Λ.torus
    (∫ x, ∫ y, dist x y ^ 2 ∂torusHaarMeasure Λ ∂torusHaarMeasure Λ) =
      ∫ z, dist z 0 ^ 2 ∂torusHaarMeasure Λ := by
  letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
  letI : MeasurableSpace Λ.torus := borel Λ.torus
  have h :=
    flatTorus_haar_difference_continuous Λ (fun z : Λ.torus => dist z 0 ^ 2) (by fun_prop)
  simpa [dist_eq_norm] using h

section UnitAddTorusFourierHelpers

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : MeasureTheory.Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : MeasureTheory.IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle)

private lemma unitAddTorus_mFourier_arg_add {d : Type*} [Fintype d]
    (k : d → ℤ) (x y : UnitAddTorus d) :
    UnitAddTorus.mFourier k (x + y) =
      UnitAddTorus.mFourier k x * UnitAddTorus.mFourier k y := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.add_apply]
  simp_rw [show ∀ i : d, fourier (k i) (x i + y i) =
      fourier (k i) (x i) * fourier (k i) (y i) by
    intro i
    rw [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]
    rfl]
  simp [Finset.prod_mul_distrib]

private lemma unitAddTorus_mFourier_arg_neg {d : Type*} [Fintype d]
    (k : d → ℤ) (x : UnitAddTorus d) :
    UnitAddTorus.mFourier k (-x) = UnitAddTorus.mFourier (-k) x := by
  simp [UnitAddTorus.mFourier]

private lemma unitAddTorus_mFourier_translate_coeff {d : Type*} [Fintype d]
    (g : UnitAddTorus d → ℂ) (a : UnitAddTorus d) (k : d → ℤ) :
    UnitAddTorus.mFourierCoeff (fun x => g (x + a)) k =
      UnitAddTorus.mFourier k a * UnitAddTorus.mFourierCoeff g k := by
  unfold UnitAddTorus.mFourierCoeff
  have hmp : MeasurePreserving (fun x : UnitAddTorus d => x - a) volume volume := by
    haveI : MeasurableAdd (UnitAddTorus d) := ⟨fun _ => by fun_prop, fun _ => by fun_prop⟩
    haveI : MeasurableNeg (UnitAddTorus d) := ⟨by fun_prop⟩
    haveI : (volume : Measure (UnitAddTorus d)).IsAddHaarMeasure := by infer_instance
    simpa [sub_eq_add_neg] using
      MeasureTheory.measurePreserving_add_right (volume : Measure (UnitAddTorus d)) (-a)
  have hchar (x : UnitAddTorus d) :
      UnitAddTorus.mFourier (-k) (x - a) =
        UnitAddTorus.mFourier k a * UnitAddTorus.mFourier (-k) x := by
    rw [sub_eq_add_neg, unitAddTorus_mFourier_arg_add, unitAddTorus_mFourier_arg_neg]
    simp [mul_comm]
  calc
    (∫ x, UnitAddTorus.mFourier (-k) x * g (x + a)
        ∂(volume : Measure (UnitAddTorus d))) =
        ∫ x, UnitAddTorus.mFourier (-k) (x - a) * g ((x - a) + a)
        ∂(volume : Measure (UnitAddTorus d)) := by
          simpa using
            (hmp.integral_comp (measurableEmbedding_subRight a)
              (fun x => UnitAddTorus.mFourier (-k) x * g (x + a))).symm
    _ = ∫ x, UnitAddTorus.mFourier (-k) (x - a) * g x
        ∂(volume : Measure (UnitAddTorus d)) := by
          congr 1
          ext x
          simp
    _ = ∫ x, (UnitAddTorus.mFourier k a * UnitAddTorus.mFourier (-k) x) * g x
        ∂(volume : Measure (UnitAddTorus d)) := by
          congr 1
          ext x
          rw [hchar]
    _ = UnitAddTorus.mFourier k a *
        ∫ x, UnitAddTorus.mFourier (-k) x * g x
        ∂(volume : Measure (UnitAddTorus d)) := by
          simp_rw [mul_assoc]
          rw [integral_const_mul]

private lemma unitAddTorus_mFourierCoeff_translate_sub {d : Type*} [Fintype d]
    (g : C(UnitAddTorus d, ℂ)) (a : UnitAddTorus d) (k : d → ℤ) :
    UnitAddTorus.mFourierCoeff (fun x => g (x + a) - g x) k =
      (UnitAddTorus.mFourier k a - 1) * UnitAddTorus.mFourierCoeff g k := by
  unfold UnitAddTorus.mFourierCoeff
  simp_rw [smul_eq_mul, mul_sub]
  have htrans : Continuous (fun x : UnitAddTorus d => x + a) := by fun_prop
  have hint₁ :
      Integrable (fun t : UnitAddTorus d => UnitAddTorus.mFourier (-k) t * g (t + a)) := by
    exact ((UnitAddTorus.mFourier (-k)).continuous.mul
      (g.continuous.comp htrans)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hint₂ :
      Integrable (fun t : UnitAddTorus d => UnitAddTorus.mFourier (-k) t * g t) := by
    exact ((UnitAddTorus.mFourier (-k)).continuous.mul
      g.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  rw [integral_sub hint₁ hint₂]
  rw [show (∫ t, UnitAddTorus.mFourier (-k) t * g (t + a)) =
        UnitAddTorus.mFourier k a *
          ∫ t, UnitAddTorus.mFourier (-k) t * g t by
        simpa [UnitAddTorus.mFourierCoeff, smul_eq_mul] using
          unitAddTorus_mFourier_translate_coeff (fun x => g x) a k]
  ring

private lemma unitAddTorus_hasSum_sq_mFourierCoeff_translate_sub
    {d : Type*} [Fintype d] (g : C(UnitAddTorus d, ℂ)) (a : UnitAddTorus d) :
    HasSum
      (fun k : d → ℤ =>
        ‖(UnitAddTorus.mFourier k a - 1) * UnitAddTorus.mFourierCoeff g k‖ ^ 2)
      (∫ x, ‖g (x + a) - g x‖ ^ 2 ∂(volume : Measure (UnitAddTorus d))) := by
  let h : C(UnitAddTorus d, ℂ) :=
    { toFun := fun x => g (x + a) - g x
      continuous_toFun := by fun_prop }
  have hparse := UnitAddTorus.hasSum_sq_mFourierCoeff (h.toLp 2 volume ℂ)
  convert hparse using 1
  · ext k
    rw [UnitAddTorus.mFourierCoeff_toLp (f := h) k]
    exact congrArg (fun z : ℂ => ‖z‖ ^ 2)
      (by simpa [h] using (unitAddTorus_mFourierCoeff_translate_sub g a k).symm)
  · apply integral_congr_ae
    filter_upwards [h.coeFn_toLp (p := 2) (μ := volume) (𝕜 := ℂ)] with x hx
    rw [hx]
    rfl

private lemma unitAddTorus_mFourierCoeff_translate_sub_sq_le_integral
    {d : Type*} [Fintype d] (g : C(UnitAddTorus d, ℂ)) (a : UnitAddTorus d)
    (k : d → ℤ) :
    ‖(UnitAddTorus.mFourier k a - 1) * UnitAddTorus.mFourierCoeff g k‖ ^ 2 ≤
      ∫ x, ‖g (x + a) - g x‖ ^ 2 ∂(volume : Measure (UnitAddTorus d)) := by
  exact le_hasSum (unitAddTorus_hasSum_sq_mFourierCoeff_translate_sub g a) k
    (fun _ _ => sq_nonneg _)

private lemma unitAddTorus_finset_sum_mFourierCoeff_translate_sub_sq_le_integral
    {d : Type*} [Fintype d] (g : C(UnitAddTorus d, ℂ)) (a : UnitAddTorus d)
    (s : Finset (d → ℤ)) :
    (∑ k ∈ s,
        ‖(UnitAddTorus.mFourier k a - 1) * UnitAddTorus.mFourierCoeff g k‖ ^ 2) ≤
      ∫ x, ‖g (x + a) - g x‖ ^ 2 ∂(volume : Measure (UnitAddTorus d)) := by
  exact sum_le_hasSum s (fun _ _ => sq_nonneg _)
    (unitAddTorus_hasSum_sq_mFourierCoeff_translate_sub g a)

end UnitAddTorusFourierHelpers

private noncomputable def matrixLinearEquiv {n : Nat} (A : LatticeBasis n) :
    RealEuclideanSpace n ≃ₗ[Real] RealEuclideanSpace n :=
  Matrix.toLinearEquiv (euclideanStdBasis n) A.matrix A.invertible

private lemma matrixLinearEquiv_eq_toEuclideanLin {n : Nat} (A : LatticeBasis n) :
    (matrixLinearEquiv A : RealEuclideanSpace n →ₗ[Real] RealEuclideanSpace n) =
      Matrix.toEuclideanLin A.matrix := by
  change (matrixLinearEquiv A : RealEuclideanSpace n →ₗ[Real] RealEuclideanSpace n) =
    Matrix.toEuclideanLin A.matrix
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  rfl

private lemma continuous_toEuclideanLin_flatTorusAmbient_to_standard {n : Nat}
    (A : LatticeBasis n) :
    @Continuous (RealEuclideanSpace n) (RealEuclideanSpace n)
      (@UniformSpace.toTopologicalSpace (RealEuclideanSpace n)
        (@PseudoMetricSpace.toUniformSpace (RealEuclideanSpace n)
          (flatTorusAmbientSeminorm n A).toPseudoMetricSpace))
      inferInstance
      (Matrix.toEuclideanLin A.matrix) := by
  simpa [flatTorusAmbientSeminorm] using
    (continuous_induced_dom
      (f := (Matrix.toEuclideanLin A.matrix : RealEuclideanSpace n → RealEuclideanSpace n))
      (t := inferInstance))

private lemma continuous_id_flatTorusAmbient_to_standard {n : Nat} (A : LatticeBasis n) :
    @Continuous (RealEuclideanSpace n) (RealEuclideanSpace n)
      (@UniformSpace.toTopologicalSpace (RealEuclideanSpace n)
        (@PseudoMetricSpace.toUniformSpace (RealEuclideanSpace n)
          (flatTorusAmbientSeminorm n A).toPseudoMetricSpace))
      inferInstance
      id := by
  let L : RealEuclideanSpace n →ₗ[Real] RealEuclideanSpace n := Matrix.toEuclideanLin A.matrix
  let e := matrixLinearEquiv A
  have hLcont : @Continuous (RealEuclideanSpace n) (RealEuclideanSpace n)
      (@UniformSpace.toTopologicalSpace (RealEuclideanSpace n)
        (@PseudoMetricSpace.toUniformSpace (RealEuclideanSpace n)
          (flatTorusAmbientSeminorm n A).toPseudoMetricSpace))
      inferInstance L := by
    simpa [L] using continuous_toEuclideanLin_flatTorusAmbient_to_standard A
  have hsymm : Continuous e.symm := by
    exact LinearMap.continuous_of_finiteDimensional
      (e.symm : RealEuclideanSpace n →ₗ[Real] RealEuclideanSpace n)
  have hcomp : @Continuous (RealEuclideanSpace n) (RealEuclideanSpace n)
      (@UniformSpace.toTopologicalSpace (RealEuclideanSpace n)
        (@PseudoMetricSpace.toUniformSpace (RealEuclideanSpace n)
          (flatTorusAmbientSeminorm n A).toPseudoMetricSpace))
      inferInstance
      (fun x => e.symm (L x)) := by
    simpa [Function.comp_def] using
      (@Continuous.comp (RealEuclideanSpace n) (RealEuclideanSpace n) (RealEuclideanSpace n)
        (@UniformSpace.toTopologicalSpace (RealEuclideanSpace n)
          (@PseudoMetricSpace.toUniformSpace (RealEuclideanSpace n)
            (flatTorusAmbientSeminorm n A).toPseudoMetricSpace))
        inferInstance inferInstance
        L (fun x : RealEuclideanSpace n => e.symm x) hsymm hLcont)
  have hfun : (fun x : RealEuclideanSpace n => e.symm (L x)) = id := by
    funext x
    have hLx : L x = e x := by
      exact (congrFun
        (congrArg (fun f : RealEuclideanSpace n →ₗ[Real] RealEuclideanSpace n =>
          (f : RealEuclideanSpace n → RealEuclideanSpace n))
          (matrixLinearEquiv_eq_toEuclideanLin A).symm) x).symm
    simp [hLx]
  simpa [hfun]
    using hcomp

private noncomputable def euclideanToUnitAddTorus (n : Nat) :
    RealEuclideanSpace n →+ UnitAddTorus (Fin n) where
  toFun x := fun i => (x i : UnitAddCircle)
  map_zero' := by
    ext i
    simp
  map_add' x y := by
    ext i
    rfl

private lemma unitAddTorus_mFourier_euclideanToUnitAddTorus
    {n : Nat} (k : Fin n -> Int) (x : RealEuclideanSpace n) :
    UnitAddTorus.mFourier k (euclideanToUnitAddTorus n x) =
      Complex.exp
        (2 * Real.pi * Complex.I *
          ((∑ i : Fin n, (k i : Real) * x i : Real) : Complex)) := by
  rw [show UnitAddTorus.mFourier k (euclideanToUnitAddTorus n x) =
      ∏ i : Fin n, Complex.exp
        (2 * Real.pi * Complex.I * (k i : Complex) * (x i : Complex)) by
        simp [UnitAddTorus.mFourier, euclideanToUnitAddTorus]]
  rw [← Complex.exp_sum]
  congr 1
  simp only [Finset.mul_sum, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast]
  ring

private lemma euclideanToUnitAddTorus_surjective (n : Nat) :
    Function.Surjective (euclideanToUnitAddTorus n) := by
  intro y
  refine ⟨WithLp.toLp 2 (fun i : Fin n => Quotient.out (y i)), ?_⟩
  ext i
  exact Quotient.out_eq (y i)

private lemma euclideanToUnitAddTorus_ker (n : Nat) :
    (euclideanToUnitAddTorus n).ker = integerLattice n := by
  ext x
  constructor
  · intro hx
    change euclideanToUnitAddTorus n x = 0 at hx
    let k : Fin n -> Int := fun i =>
      Classical.choose ((AddCircle.coe_eq_zero_iff (p := (1 : Real))).1 (by
        simpa [euclideanToUnitAddTorus] using congrFun hx i))
    refine ⟨k, ?_⟩
    ext i
    have hi : ((x i : Real) : UnitAddCircle) = 0 := by
      simpa [euclideanToUnitAddTorus] using congrFun hx i
    have hk := Classical.choose_spec ((AddCircle.coe_eq_zero_iff (p := (1 : Real))).1 hi)
    simpa [integerVector, k] using hk.symm
  · rintro ⟨k, rfl⟩
    ext i
    simp [euclideanToUnitAddTorus, integerVector]

private noncomputable def coordinateTorusAddEquivUnitAddTorus (n : Nat) :
    (RealEuclideanSpace n ⧸ integerLattice n) ≃+ UnitAddTorus (Fin n) := by
  let φ := euclideanToUnitAddTorus n
  let eKer : RealEuclideanSpace n ⧸ φ.ker ≃+ UnitAddTorus (Fin n) :=
    QuotientAddGroup.quotientKerEquivOfSurjective (φ := φ)
      (euclideanToUnitAddTorus_surjective n)
  let eEq : RealEuclideanSpace n ⧸ integerLattice n ≃+ RealEuclideanSpace n ⧸ φ.ker :=
    QuotientAddGroup.quotientAddEquivOfEq (euclideanToUnitAddTorus_ker n).symm
  exact eEq.trans eKer

private lemma coordinateTorusAddEquivUnitAddTorus_apply_mk
    (n : Nat) (x : RealEuclideanSpace n) :
    coordinateTorusAddEquivUnitAddTorus n (QuotientAddGroup.mk' (integerLattice n) x) =
      euclideanToUnitAddTorus n x := by
  unfold coordinateTorusAddEquivUnitAddTorus
  dsimp
  exact QuotientAddGroup.kerLift_mk (euclideanToUnitAddTorus n) x

private lemma continuous_euclideanToUnitAddTorus (n : Nat) :
    Continuous (euclideanToUnitAddTorus n) := by
  change Continuous
    (fun x : RealEuclideanSpace n => fun i : Fin n => ((x i : Real) : UnitAddCircle))
  fun_prop

private lemma continuous_euclideanToUnitAddTorus_flatTorusAmbient
    {n : Nat} (A : LatticeBasis n) :
    @Continuous (RealEuclideanSpace n) (UnitAddTorus (Fin n))
      (@UniformSpace.toTopologicalSpace (RealEuclideanSpace n)
        (@PseudoMetricSpace.toUniformSpace (RealEuclideanSpace n)
          (flatTorusAmbientSeminorm n A).toPseudoMetricSpace))
      inferInstance
      (euclideanToUnitAddTorus n) := by
  simpa [Function.comp_def] using
    (@Continuous.comp (RealEuclideanSpace n) (RealEuclideanSpace n) (UnitAddTorus (Fin n))
      (@UniformSpace.toTopologicalSpace (RealEuclideanSpace n)
        (@PseudoMetricSpace.toUniformSpace (RealEuclideanSpace n)
          (flatTorusAmbientSeminorm n A).toPseudoMetricSpace))
      inferInstance inferInstance
      id (euclideanToUnitAddTorus n)
      (continuous_euclideanToUnitAddTorus n)
      (continuous_id_flatTorusAmbient_to_standard A))

private lemma continuous_coordinateTorusAddEquivUnitAddTorus (n : Nat) :
    Continuous (coordinateTorusAddEquivUnitAddTorus n :
      RealEuclideanSpace n ⧸ integerLattice n -> UnitAddTorus (Fin n)) := by
  let f : RealEuclideanSpace n -> UnitAddTorus (Fin n) := euclideanToUnitAddTorus n
  have hrel : ∀ a b : RealEuclideanSpace n,
      QuotientAddGroup.leftRel (integerLattice n) a b -> f a = f b := by
    intro a b hab
    have hker : -a + b ∈ (euclideanToUnitAddTorus n).ker := by
      rw [euclideanToUnitAddTorus_ker n]
      exact QuotientAddGroup.leftRel_apply.mp hab
    have hzero : -euclideanToUnitAddTorus n a + euclideanToUnitAddTorus n b = 0 := by
      simpa [f, map_add, map_neg] using hker
    calc
      f a = f a + 0 := by simp
      _ = f a + (-f a + f b) := by rw [hzero]
      _ = f b := by abel
  rw [show (coordinateTorusAddEquivUnitAddTorus n :
        RealEuclideanSpace n ⧸ integerLattice n -> UnitAddTorus (Fin n)) =
      Quotient.lift f hrel by
        funext q
        refine QuotientAddGroup.induction_on q ?_
        intro x
        exact coordinateTorusAddEquivUnitAddTorus_apply_mk n x]
  exact (continuous_euclideanToUnitAddTorus n).quotient_lift hrel

private lemma continuous_coordinateTorusAddEquivUnitAddTorus_flatTorusAmbient
    {n : Nat} (Λ : KNFullRankLattice n) :
    @Continuous Λ.torus (UnitAddTorus (Fin n))
      (@UniformSpace.toTopologicalSpace Λ.torus
        (@PseudoMetricSpace.toUniformSpace Λ.torus
          (Λ.torusSeminormedAddCommGroup.toPseudoMetricSpace)))
      inferInstance
      (coordinateTorusAddEquivUnitAddTorus n : Λ.torus -> UnitAddTorus (Fin n)) := by
  letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
  letI : SeminormedAddCommGroup (RealEuclideanSpace n) :=
    flatTorusAmbientSeminorm n Λ.basis
  let f : RealEuclideanSpace n -> UnitAddTorus (Fin n) := euclideanToUnitAddTorus n
  have hrel : ∀ a b : RealEuclideanSpace n,
      QuotientAddGroup.leftRel (integerLattice n) a b -> f a = f b := by
    intro a b hab
    have hker : -a + b ∈ (euclideanToUnitAddTorus n).ker := by
      rw [euclideanToUnitAddTorus_ker n]
      exact QuotientAddGroup.leftRel_apply.mp hab
    have hzero : -euclideanToUnitAddTorus n a + euclideanToUnitAddTorus n b = 0 := by
      simpa [f, map_add, map_neg] using hker
    calc
      f a = f a + 0 := by simp
      _ = f a + (-f a + f b) := by rw [hzero]
      _ = f b := by abel
  rw [show (coordinateTorusAddEquivUnitAddTorus n :
        Λ.torus -> UnitAddTorus (Fin n)) =
      Quotient.lift f hrel by
        funext q
        refine QuotientAddGroup.induction_on q ?_
        intro x
        exact coordinateTorusAddEquivUnitAddTorus_apply_mk n x]
  simpa [KNFullRankLattice.torusSeminormedAddCommGroup, KNFullRankLattice.torus, flatTorus]
    using
      (@Continuous.quotient_lift (RealEuclideanSpace n) (UnitAddTorus (Fin n))
        (@UniformSpace.toTopologicalSpace (RealEuclideanSpace n)
          (@PseudoMetricSpace.toUniformSpace (RealEuclideanSpace n)
            (flatTorusAmbientSeminorm n Λ.basis).toPseudoMetricSpace))
        inferInstance
        (QuotientAddGroup.leftRel (integerLattice n))
        f
        (continuous_euclideanToUnitAddTorus_flatTorusAmbient Λ.basis)
        hrel)

section CoordinateTorusMeasure

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : MeasureTheory.Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : MeasureTheory.IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle)

private theorem measurePreserving_coordinateTorusAddEquivUnitAddTorus {n : Nat}
    (Λ : KNFullRankLattice n) :
    letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
    letI : MeasurableSpace Λ.torus := borel Λ.torus
    @MeasurePreserving Λ.torus (UnitAddTorus (Fin n)) (borel Λ.torus) inferInstance
      (coordinateTorusAddEquivUnitAddTorus n : Λ.torus -> UnitAddTorus (Fin n))
      (torusHaarMeasure Λ) (volume : Measure (UnitAddTorus (Fin n))) := by
  classical
  letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
  letI : MeasurableSpace Λ.torus := borel Λ.torus
  letI : BorelSpace Λ.torus := ⟨rfl⟩
  haveI : CompactSpace Λ.torus := Λ.torus_compactSpace
  haveI : LocallyCompactSpace Λ.torus := Λ.torusLocallyCompactSpace
  haveI : (torusHaarMeasure Λ).IsAddHaarMeasure := torusHaarMeasure_isAddHaarMeasure Λ
  have hsrcProb : MeasureTheory.IsProbabilityMeasure (torusHaarMeasure Λ) :=
    torusHaarMeasure_isProbability Λ
  have htgtProb : MeasureTheory.IsProbabilityMeasure
      (volume : Measure (UnitAddTorus (Fin n))) := by infer_instance
  have hcont : @Continuous Λ.torus (UnitAddTorus (Fin n))
      (@UniformSpace.toTopologicalSpace Λ.torus
        (@PseudoMetricSpace.toUniformSpace Λ.torus
          (Λ.torusSeminormedAddCommGroup.toPseudoMetricSpace)))
      inferInstance
      (coordinateTorusAddEquivUnitAddTorus n : Λ.torus -> UnitAddTorus (Fin n)) := by
    exact continuous_coordinateTorusAddEquivUnitAddTorus_flatTorusAmbient Λ
  have hsurj : Function.Surjective
      (coordinateTorusAddEquivUnitAddTorus n : Λ.torus -> UnitAddTorus (Fin n)) :=
    (coordinateTorusAddEquivUnitAddTorus n).surjective
  have huniv :
      (torusHaarMeasure Λ) Set.univ = (volume : Measure (UnitAddTorus (Fin n))) Set.univ := by
    rw [hsrcProb.measure_univ, htgtProb.measure_univ]
  exact AddMonoidHom.measurePreserving
    (G := Λ.torus) (H := UnitAddTorus (Fin n))
    (μ := torusHaarMeasure Λ) (ν := (volume : Measure (UnitAddTorus (Fin n))))
    (f := (coordinateTorusAddEquivUnitAddTorus n).toAddMonoidHom) hcont hsurj huniv

private lemma continuous_symm_coordinateTorusAddEquivUnitAddTorus {n : Nat}
    (Λ : KNFullRankLattice n) :
    @Continuous (UnitAddTorus (Fin n)) Λ.torus inferInstance
      (@UniformSpace.toTopologicalSpace Λ.torus
        (@PseudoMetricSpace.toUniformSpace Λ.torus
          (Λ.torusSeminormedAddCommGroup.toPseudoMetricSpace)))
      ((coordinateTorusAddEquivUnitAddTorus n).symm :
        UnitAddTorus (Fin n) -> Λ.torus) := by
  classical
  letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
  haveI : CompactSpace Λ.torus := Λ.torus_compactSpace
  have hcont : @Continuous Λ.torus (UnitAddTorus (Fin n))
      (@UniformSpace.toTopologicalSpace Λ.torus
        (@PseudoMetricSpace.toUniformSpace Λ.torus
          (Λ.torusSeminormedAddCommGroup.toPseudoMetricSpace)))
      inferInstance
      (coordinateTorusAddEquivUnitAddTorus n : Λ.torus -> UnitAddTorus (Fin n)) := by
    exact continuous_coordinateTorusAddEquivUnitAddTorus_flatTorusAmbient Λ
  let eHomeomorph : Λ.torus ≃ₜ UnitAddTorus (Fin n) :=
    Continuous.homeoOfEquivCompactToT2
      (f := (coordinateTorusAddEquivUnitAddTorus n).toEquiv) hcont
  simpa using eHomeomorph.continuous_invFun

end CoordinateTorusMeasure

private lemma measurableEmbedding_coordinateTorusAddEquivUnitAddTorus {n : Nat}
    (Λ : KNFullRankLattice n) :
    letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
    letI : MeasurableSpace Λ.torus := borel Λ.torus
    @MeasurableEmbedding Λ.torus (UnitAddTorus (Fin n)) (borel Λ.torus) inferInstance
      (coordinateTorusAddEquivUnitAddTorus n : Λ.torus -> UnitAddTorus (Fin n)) := by
  classical
  letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
  letI : MeasurableSpace Λ.torus := borel Λ.torus
  haveI : BorelSpace Λ.torus := ⟨rfl⟩
  haveI : CompactSpace Λ.torus := Λ.torus_compactSpace
  have hcont : @Continuous Λ.torus (UnitAddTorus (Fin n))
      (@UniformSpace.toTopologicalSpace Λ.torus
        (@PseudoMetricSpace.toUniformSpace Λ.torus
          (Λ.torusSeminormedAddCommGroup.toPseudoMetricSpace)))
      inferInstance
      (coordinateTorusAddEquivUnitAddTorus n : Λ.torus -> UnitAddTorus (Fin n)) :=
    continuous_coordinateTorusAddEquivUnitAddTorus_flatTorusAmbient Λ
  let eHomeomorph : Λ.torus ≃ₜ UnitAddTorus (Fin n) :=
    Continuous.homeoOfEquivCompactToT2
      (f := (coordinateTorusAddEquivUnitAddTorus n).toEquiv) hcont
  exact eHomeomorph.toMeasurableEquiv.measurableEmbedding

private theorem measurePreserving_coordinateTorusAddEquivUnitAddTorus_global {n : Nat}
    (Λ : KNFullRankLattice n) :
    letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
    letI : MeasurableSpace Λ.torus := borel Λ.torus
    @MeasurePreserving Λ.torus (UnitAddTorus (Fin n)) (borel Λ.torus) inferInstance
      (coordinateTorusAddEquivUnitAddTorus n : Λ.torus -> UnitAddTorus (Fin n))
      (torusHaarMeasure Λ) (volume : Measure (UnitAddTorus (Fin n))) := by
  classical
  letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
  letI : MeasurableSpace Λ.torus := borel Λ.torus
  letI : BorelSpace Λ.torus := ⟨rfl⟩
  haveI : CompactSpace Λ.torus := Λ.torus_compactSpace
  haveI : LocallyCompactSpace Λ.torus := Λ.torusLocallyCompactSpace
  haveI : (torusHaarMeasure Λ).IsAddHaarMeasure := torusHaarMeasure_isAddHaarMeasure Λ
  have hsrcProb : MeasureTheory.IsProbabilityMeasure (torusHaarMeasure Λ) :=
    torusHaarMeasure_isProbability Λ
  haveI : MeasureTheory.IsProbabilityMeasure (volume : Measure UnitAddCircle) := by
    have hvol :
        (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
      simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : Real)))
    rw [hvol]
    infer_instance
  have htgtProb : MeasureTheory.IsProbabilityMeasure
      (volume : Measure (UnitAddTorus (Fin n))) := by infer_instance
  have hcont : @Continuous Λ.torus (UnitAddTorus (Fin n))
      (@UniformSpace.toTopologicalSpace Λ.torus
        (@PseudoMetricSpace.toUniformSpace Λ.torus
          (Λ.torusSeminormedAddCommGroup.toPseudoMetricSpace)))
      inferInstance
      (coordinateTorusAddEquivUnitAddTorus n : Λ.torus -> UnitAddTorus (Fin n)) := by
    exact continuous_coordinateTorusAddEquivUnitAddTorus_flatTorusAmbient Λ
  have hsurj : Function.Surjective
      (coordinateTorusAddEquivUnitAddTorus n : Λ.torus -> UnitAddTorus (Fin n)) :=
    (coordinateTorusAddEquivUnitAddTorus n).surjective
  have huniv :
      (torusHaarMeasure Λ) Set.univ = (volume : Measure (UnitAddTorus (Fin n))) Set.univ := by
    rw [hsrcProb.measure_univ, htgtProb.measure_univ]
  exact AddMonoidHom.measurePreserving
    (G := Λ.torus) (H := UnitAddTorus (Fin n))
    (μ := torusHaarMeasure Λ) (ν := (volume : Measure (UnitAddTorus (Fin n))))
    (f := (coordinateTorusAddEquivUnitAddTorus n).toAddMonoidHom) hcont hsurj huniv

private noncomputable def piIntegerPoint
    (n : Nat) (k : Fin n -> Int) : Fin n -> Real :=
  fun i => (k i : Real)

private instance piIntegerPointAddAction (n : Nat) :
    AddAction (Fin n -> Int) (Fin n -> Real) where
  vadd q x := piIntegerPoint n q + x
  zero_vadd := by
    intro x
    change piIntegerPoint n 0 + x = x
    funext i
    simp [piIntegerPoint]
  add_vadd := by
    intro q r x
    change piIntegerPoint n (q + r) + x = piIntegerPoint n q + (piIntegerPoint n r + x)
    funext i
    simp [piIntegerPoint, add_comm, add_left_comm]

private instance piIntegerPointMeasurableConstVAdd (n : Nat) :
    MeasurableConstVAdd (Fin n -> Int) (Fin n -> Real) where
  measurable_const_vadd q := by
    change Measurable fun x : Fin n -> Real => piIntegerPoint n q + x
    fun_prop

private instance piIntegerPointVAddInvariantMeasure (n : Nat) :
    VAddInvariantMeasure (Fin n -> Int) (Fin n -> Real)
      (volume : Measure (Fin n -> Real)) where
  measure_preimage_vadd q {s} _hs := by
    change volume ((fun x : Fin n -> Real => piIntegerPoint n q + x) ⁻¹' s) = volume s
    exact measure_preimage_add volume (piIntegerPoint n q) s

private def piUnitCube (n : Nat) : Set (Fin n -> Real) :=
  {x | ∀ i : Fin n, x i ∈ Set.Ioc (0 : Real) 1}

private lemma piUnitCube_measurableSet (n : Nat) :
    MeasurableSet (piUnitCube n) :=
  MeasurableSet.univ_pi' fun _ => measurableSet_Ioc

private lemma piUnitCube_nullMeasurable (n : Nat) :
    NullMeasurableSet (piUnitCube n) (volume : Measure (Fin n -> Real)) :=
  (piUnitCube_measurableSet n).nullMeasurableSet

private lemma piUnitCube_fundamentalDomain (n : Nat) :
    IsAddFundamentalDomain (Fin n -> Int) (piUnitCube n)
      (volume : Measure (Fin n -> Real)) := by
  classical
  refine IsAddFundamentalDomain.mk' (piUnitCube_nullMeasurable n) ?_
  intro x
  have hcoord :
      ∀ i : Fin n, ∃! z : Int, x i + z • (1 : Real) ∈ Set.Ioc (0 : Real) (0 + 1) := by
    intro i
    exact existsUnique_add_zsmul_mem_Ioc zero_lt_one (x i) 0
  choose q hq hquniq using hcoord
  refine ⟨q, ?_, ?_⟩
  · intro i
    have hi := hq i
    change (piIntegerPoint n q + x) i ∈ Set.Ioc (0 : Real) 1
    simpa [piIntegerPoint, add_comm] using hi
  · intro r hr
    funext i
    exact hquniq i (r i) (by
      change ∀ i : Fin n, (piIntegerPoint n r + x) i ∈ Set.Ioc (0 : Real) 1 at hr
      have hi := hr i
      simpa [piIntegerPoint, add_comm] using hi)

private noncomputable def piTorusMk (n : Nat) :
    (Fin n -> Real) -> UnitAddTorus (Fin n) :=
  fun x i => ((x i : Real) : UnitAddCircle)

private lemma addCircle_eq_iff_exists_int_add {x y : Real}
    (h : (x : UnitAddCircle) = (y : UnitAddCircle)) :
    ∃ z : Int, y = x + z := by
  change (QuotientAddGroup.mk x :
      Real ⧸ AddSubgroup.zmultiples (1 : Real)) = QuotientAddGroup.mk y at h
  rw [QuotientAddGroup.eq, AddSubgroup.mem_zmultiples_iff] at h
  rcases h with ⟨z, hz⟩
  use z
  norm_num at hz
  linarith

private theorem piTorusMk_image_measure_le_volume
    {n : Nat} {S : Set (Fin n -> Real)} (_hS : MeasurableSet S) :
    (volume : Measure (UnitAddTorus (Fin n))) (piTorusMk n '' S) <=
      (volume : Measure (Fin n -> Real)) S := by
  classical
  let repr := UnitAddTorus.measurableEquivPiIoc (fun _ : Fin n => (0 : Real))
  let U : Set (UnitAddTorus (Fin n)) := piTorusMk n '' S
  have hrepr_measure :
      (volume : Measure (UnitAddTorus (Fin n))) U =
        (Measure.comap Subtype.val (volume : Measure (Fin n -> Real))) (repr '' U) := by
    have hmp := UnitAddTorus.measurePreserving_equivPiIoc (fun _ : Fin n => (0 : Real))
    have hmap := repr.measurableEmbedding.map_apply
      (volume : Measure (UnitAddTorus (Fin n))) (repr '' U)
    rw [repr.preimage_image] at hmap
    have hunitTorusVolume :
        (@volume (UnitAddTorus (Fin n))
          (@MeasureSpace.pi (Fin n) (Fin.fintype n) (fun _ => UnitAddCircle)
            (fun _ => instMeasureSpaceUnitAddCircle))) =
        (@volume (UnitAddTorus (Fin n))
          (@MeasureSpace.pi (Fin n) (Fin.fintype n) (fun _ => UnitAddCircle)
            (fun _ => AddCircle.measureSpace (1 : Real)))) := by
      simp [volume, AddCircle.haarAddCircle]
    have hmp_map_eq :
        Measure.map (⇑repr) (volume : Measure (UnitAddTorus (Fin n))) =
          Measure.comap Subtype.val (volume : Measure (Fin n -> Real)) := by
      rw [← hunitTorusVolume]
      simpa [repr] using hmp.map_eq
    calc
      (volume : Measure (UnitAddTorus (Fin n))) U =
          (Measure.map (⇑repr) (volume : Measure (UnitAddTorus (Fin n)))) (repr '' U) :=
        hmap.symm
      _ = (Measure.comap Subtype.val (volume : Measure (Fin n -> Real))) (repr '' U) := by
        exact congrArg (fun μ : Measure {x : Fin n -> Real // ∀ i : Fin n,
          x i ∈ Set.Ioc (0 : Real) (0 + 1)} => μ (repr '' U)) hmp_map_eq
  have hsub :
      Subtype.val '' (repr '' U) ⊆
        ⋃ q : Fin n -> Int, (q +ᵥ S) ∩ piUnitCube n := by
    rintro z ⟨a, ha, rfl⟩
    rcases ha with ⟨u, huU, hrepr⟩
    rcases huU with ⟨y, hyS, rfl⟩
    have hu_eq : piTorusMk n y = repr.symm a := by
      simpa using congrArg repr.symm hrepr
    have hcoord : ∀ i : Fin n, ∃ m : Int, a.1 i = y i + m := by
      intro i
      have hcircle : ((y i : Real) : UnitAddCircle) = ((a.1 i : Real) : UnitAddCircle) := by
        simpa [piTorusMk, UnitAddTorus.coe_symm_measurableEquivPiIoc_apply, repr] using
          congrFun hu_eq i
      exact addCircle_eq_iff_exists_int_add hcircle
    choose q hq using hcoord
    refine Set.mem_iUnion.2 ⟨q, ?_⟩
    constructor
    · rw [Set.mem_vadd_set]
      refine ⟨y, hyS, ?_⟩
      funext i
      change (piIntegerPoint n q + y) i = a.1 i
      simpa [piIntegerPoint, add_comm] using (hq i).symm
    · simpa [piUnitCube] using a.2
  calc
    (volume : Measure (UnitAddTorus (Fin n))) (piTorusMk n '' S) =
        (volume : Measure (UnitAddTorus (Fin n))) U := by rfl
    _ = (Measure.comap Subtype.val (volume : Measure (Fin n -> Real))) (repr '' U) :=
        hrepr_measure
    _ = (volume : Measure (Fin n -> Real)) (Subtype.val '' (repr '' U)) := by
        have hcomap := comap_subtype_coe_apply
          (s := {x : Fin n -> Real | ∀ i : Fin n, x i ∈ Set.Ioc (0 : Real) (0 + 1)})
          (MeasurableSet.univ_pi' fun _ => measurableSet_Ioc)
          (volume : Measure (Fin n -> Real)) (repr '' U)
        simpa [piUnitCube, repr] using hcomap
    _ ≤ (volume : Measure (Fin n -> Real))
        (⋃ q : Fin n -> Int, (q +ᵥ S) ∩ piUnitCube n) :=
        measure_mono hsub
    _ ≤ ∑' q : Fin n -> Int,
        (volume : Measure (Fin n -> Real)) ((q +ᵥ S) ∩ piUnitCube n) :=
        measure_iUnion_le _
    _ = (volume : Measure (Fin n -> Real)) S :=
        (piUnitCube_fundamentalDomain n).measure_eq_tsum S |>.symm

private theorem euclideanToUnitAddTorus_image_measure_le_volume
    {n : Nat} {S : Set (RealEuclideanSpace n)} (hS : MeasurableSet S) :
    (volume : Measure (UnitAddTorus (Fin n))) (euclideanToUnitAddTorus n '' S) <=
      (volume : Measure (RealEuclideanSpace n)) S := by
  classical
  let toPi : RealEuclideanSpace n -> Fin n -> Real := fun x => (x : Fin n -> Real)
  let Sπ : Set (Fin n -> Real) := toPi '' S
  have hemb : MeasurableEmbedding toPi := by
    simpa [toPi, RealEuclideanSpace] using
      (MeasurableEquiv.toLp 2 (Fin n -> Real)).symm.measurableEmbedding
  have hmp : MeasurePreserving toPi
      (volume : Measure (RealEuclideanSpace n)) (volume : Measure (Fin n -> Real)) := by
    simpa [toPi, RealEuclideanSpace] using PiLp.volume_preserving_ofLp (Fin n)
  have hSπ : MeasurableSet Sπ := hemb.measurableSet_image.mpr hS
  have hvolSπ :
      (volume : Measure (Fin n -> Real)) Sπ =
        (volume : Measure (RealEuclideanSpace n)) S := by
    have hmap := hemb.map_apply (volume : Measure (RealEuclideanSpace n)) Sπ
    rw [hmp.map_eq, hemb.injective.preimage_image S] at hmap
    exact hmap
  have himage :
      euclideanToUnitAddTorus n '' S = piTorusMk n '' Sπ := by
    ext z
    constructor
    · rintro ⟨x, hxS, rfl⟩
      exact ⟨toPi x, ⟨x, hxS, rfl⟩, by
        ext i
        rfl⟩
    · rintro ⟨y, hySπ, rfl⟩
      rcases hySπ with ⟨x, hxS, rfl⟩
      exact ⟨x, hxS, by
        ext i
        rfl⟩
  calc
    (volume : Measure (UnitAddTorus (Fin n))) (euclideanToUnitAddTorus n '' S) =
        (volume : Measure (UnitAddTorus (Fin n))) (piTorusMk n '' Sπ) := by rw [himage]
    _ ≤ (volume : Measure (Fin n -> Real)) Sπ :=
        piTorusMk_image_measure_le_volume hSπ
    _ = (volume : Measure (RealEuclideanSpace n)) S :=
        hvolSπ

private theorem flatTorus_quotient_image_measure_le_volume
    {n : Nat} (Λ : KNFullRankLattice n)
    {S : Set (RealEuclideanSpace n)} (hS : MeasurableSet S) :
    letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
    letI : MeasurableSpace Λ.torus := borel Λ.torus
    (torusHaarMeasure Λ)
      (QuotientAddGroup.mk' (integerLattice n) '' S : Set Λ.torus) <= volume S := by
  classical
  letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
  letI : MeasurableSpace Λ.torus := borel Λ.torus
  let coord : Λ.torus -> UnitAddTorus (Fin n) := coordinateTorusAddEquivUnitAddTorus n
  let U : Set Λ.torus := QuotientAddGroup.mk' (integerLattice n) '' S
  have hmp := measurePreserving_coordinateTorusAddEquivUnitAddTorus_global Λ
  have hemb := measurableEmbedding_coordinateTorusAddEquivUnitAddTorus Λ
  have hcoord_image :
      coord '' U = euclideanToUnitAddTorus n '' S := by
    ext z
    constructor
    · rintro ⟨x, hxU, rfl⟩
      rcases hxU with ⟨y, hyS, rfl⟩
      exact ⟨y, hyS, by
        simpa [coord] using coordinateTorusAddEquivUnitAddTorus_apply_mk n y⟩
    · rintro ⟨y, hyS, rfl⟩
      refine ⟨QuotientAddGroup.mk' (integerLattice n) y, ?_, ?_⟩
      · exact ⟨y, hyS, rfl⟩
      · simpa [coord] using (coordinateTorusAddEquivUnitAddTorus_apply_mk n y).symm
  have hmeasure :
      (torusHaarMeasure Λ) U =
        (volume : Measure (UnitAddTorus (Fin n))) (coord '' U) := by
    have hmap := hemb.map_apply (torusHaarMeasure Λ) (coord '' U)
    rw [hmp.map_eq, hemb.injective.preimage_image U] at hmap
    exact hmap.symm
  calc
    (torusHaarMeasure Λ)
        (QuotientAddGroup.mk' (integerLattice n) '' S : Set Λ.torus) =
        (torusHaarMeasure Λ) U := by rfl
    _ = (volume : Measure (UnitAddTorus (Fin n))) (coord '' U) := hmeasure
    _ = (volume : Measure (UnitAddTorus (Fin n))) (euclideanToUnitAddTorus n '' S) := by
        rw [hcoord_image]
    _ ≤ volume S := euclideanToUnitAddTorus_image_measure_le_volume hS

private theorem flatTorus_quotient_image_measureReal_le_volume_toReal
    {n : Nat} (Λ : KNFullRankLattice n)
    {S : Set (RealEuclideanSpace n)} (hS : MeasurableSet S) (hSfin : volume S ≠ ⊤) :
    letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
    letI : MeasurableSpace Λ.torus := borel Λ.torus
    (torusHaarMeasure Λ).real
      (QuotientAddGroup.mk' (integerLattice n) '' S : Set Λ.torus) <=
        (volume S).toReal := by
  classical
  letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
  letI : MeasurableSpace Λ.torus := borel Λ.torus
  exact ENNReal.toReal_mono hSfin
    (flatTorus_quotient_image_measure_le_volume Λ hS)

private lemma KNFullRankLattice.det_pos {n : Nat} (Λ : KNFullRankLattice n) :
    0 < Λ.det := by
  have hdet : Λ.basis.matrix.det ≠ 0 := IsUnit.ne_zero Λ.basis.invertible
  simpa [KNFullRankLattice.det] using abs_pos.mpr hdet

private lemma matrixLinearEquiv_det {n : Nat} (A : LatticeBasis n) :
    LinearMap.det (matrixLinearEquiv A : RealEuclideanSpace n →ₗ[Real] RealEuclideanSpace n) =
      A.matrix.det := by
  change LinearMap.det (Matrix.toLin (euclideanStdBasis n) (euclideanStdBasis n) A.matrix) =
    A.matrix.det
  simp

private lemma volume_preimage_matrix_toEuclideanLin
    {n : Nat} (Λ : KNFullRankLattice n) {S : Set (RealEuclideanSpace n)} :
    (volume : Measure (RealEuclideanSpace n))
        ((Matrix.toEuclideanLin Λ.basis.matrix) ⁻¹' S) =
      ENNReal.ofReal (Λ.det⁻¹) * volume S := by
  classical
  let e : RealEuclideanSpace n ≃ₗ[Real] RealEuclideanSpace n := matrixLinearEquiv Λ.basis
  have heq : (e : RealEuclideanSpace n -> RealEuclideanSpace n) =
      (Matrix.toEuclideanLin Λ.basis.matrix : RealEuclideanSpace n -> RealEuclideanSpace n) := by
    exact congrArg
      (fun f : RealEuclideanSpace n →ₗ[Real] RealEuclideanSpace n =>
        (f : RealEuclideanSpace n -> RealEuclideanSpace n))
      (matrixLinearEquiv_eq_toEuclideanLin Λ.basis)
  have hpre :
      (Matrix.toEuclideanLin Λ.basis.matrix) ⁻¹' S = (e : RealEuclideanSpace n -> _) ⁻¹' S := by
    rw [← heq]
  rw [hpre]
  rw [Measure.addHaar_preimage_linearEquiv (μ := (volume : Measure (RealEuclideanSpace n))) e S]
  have hdetLin :
      LinearMap.det (e : RealEuclideanSpace n →ₗ[Real] RealEuclideanSpace n) =
        Λ.basis.matrix.det := by
    simpa [e] using matrixLinearEquiv_det Λ.basis
  have hcoef :
      |LinearMap.det (e.symm : RealEuclideanSpace n →ₗ[Real] RealEuclideanSpace n)| =
        Λ.det⁻¹ := by
    rw [LinearEquiv.det_coe_symm e, hdetLin]
    simp [KNFullRankLattice.det, abs_inv]
  rw [hcoef]

private theorem flatTorus_matrix_preimage_quotient_image_measureReal_le_volume_div_det
    {n : Nat} (Λ : KNFullRankLattice n)
    {S : Set (RealEuclideanSpace n)} (hS : MeasurableSet S) (hSfin : volume S ≠ ⊤) :
    letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
    letI : MeasurableSpace Λ.torus := borel Λ.torus
    (torusHaarMeasure Λ).real
      (QuotientAddGroup.mk' (integerLattice n) ''
        ((Matrix.toEuclideanLin Λ.basis.matrix) ⁻¹' S) : Set Λ.torus) <=
      (volume S).toReal / Λ.det := by
  classical
  letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
  letI : MeasurableSpace Λ.torus := borel Λ.torus
  let T : Set (RealEuclideanSpace n) := (Matrix.toEuclideanLin Λ.basis.matrix) ⁻¹' S
  have hTmeas : MeasurableSet T := by
    exact hS.preimage (LinearMap.continuous_of_finiteDimensional
      (Matrix.toEuclideanLin Λ.basis.matrix)).measurable
  have hTvol : volume T = ENNReal.ofReal (Λ.det⁻¹) * volume S := by
    simpa [T] using volume_preimage_matrix_toEuclideanLin Λ (S := S)
  have hTfin : volume T ≠ ⊤ := by
    rw [hTvol]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSfin
  have hTreal : (volume T).toReal = (volume S).toReal / Λ.det := by
    rw [hTvol, ENNReal.toReal_mul]
    · rw [ENNReal.toReal_ofReal]
      · field_simp [ne_of_gt (KNFullRankLattice.det_pos Λ)]
      · exact inv_nonneg.mpr (le_of_lt (KNFullRankLattice.det_pos Λ))
  have hbound :=
    flatTorus_quotient_image_measureReal_le_volume_toReal Λ hTmeas hTfin
  simpa [T, hTreal] using hbound

private lemma KNFullRankLattice.torus_borelSpace {n : Nat} (Λ : KNFullRankLattice n) :
    letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
    letI : MeasurableSpace Λ.torus := borel Λ.torus
    BorelSpace Λ.torus := by
  letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
  letI : MeasurableSpace Λ.torus := borel Λ.torus
  exact ⟨rfl⟩

private lemma KNFullRankLattice.torus_finiteHaarMeasure {n : Nat}
    (Λ : KNFullRankLattice n) :
    letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
    letI : MeasurableSpace Λ.torus := borel Λ.torus
    IsFiniteMeasure (torusHaarMeasure Λ) := by
  letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
  letI : MeasurableSpace Λ.torus := borel Λ.torus
  haveI : MeasureTheory.IsProbabilityMeasure (torusHaarMeasure Λ) :=
    torusHaarMeasure_isProbability Λ
  infer_instance

private lemma measurable_coordinateTorusAddEquivUnitAddTorus {n : Nat}
    (Λ : KNFullRankLattice n) :
    letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
    letI : MeasurableSpace Λ.torus := borel Λ.torus
    @Measurable Λ.torus (UnitAddTorus (Fin n)) (borel Λ.torus) inferInstance
      (coordinateTorusAddEquivUnitAddTorus n : Λ.torus -> UnitAddTorus (Fin n)) := by
  letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
  letI : MeasurableSpace Λ.torus := borel Λ.torus
  haveI : BorelSpace Λ.torus := Λ.torus_borelSpace
  exact (continuous_coordinateTorusAddEquivUnitAddTorus_flatTorusAmbient Λ).measurable

private lemma measurable_symm_coordinateTorusAddEquivUnitAddTorus {n : Nat}
    (Λ : KNFullRankLattice n) :
    letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
    letI : MeasurableSpace Λ.torus := borel Λ.torus
    @Measurable (UnitAddTorus (Fin n)) Λ.torus inferInstance (borel Λ.torus)
      ((coordinateTorusAddEquivUnitAddTorus n).symm :
        UnitAddTorus (Fin n) -> Λ.torus) := by
  letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
  letI : MeasurableSpace Λ.torus := borel Λ.torus
  haveI : BorelSpace Λ.torus := Λ.torus_borelSpace
  exact (continuous_symm_coordinateTorusAddEquivUnitAddTorus Λ).measurable

private lemma integrable_unitTorus_iff_integrable_flatTorus
    {n : Nat} (Λ : KNFullRankLattice n) (φ : UnitAddTorus (Fin n) -> Real) :
    letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
    letI : MeasurableSpace Λ.torus := borel Λ.torus
    Integrable
        (fun x : Λ.torus =>
          φ ((coordinateTorusAddEquivUnitAddTorus n : Λ.torus -> UnitAddTorus (Fin n)) x))
        (torusHaarMeasure Λ) ↔
      Integrable φ (volume : Measure (UnitAddTorus (Fin n))) := by
  classical
  letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
  letI : MeasurableSpace Λ.torus := borel Λ.torus
  have hmp := measurePreserving_coordinateTorusAddEquivUnitAddTorus_global Λ
  have hemb := measurableEmbedding_coordinateTorusAddEquivUnitAddTorus Λ
  simpa [Function.comp_def] using hmp.integrable_comp_emb hemb (g := φ)

private lemma integral_unitTorus_eq_integral_flatTorus
    {n : Nat} (Λ : KNFullRankLattice n) (φ : UnitAddTorus (Fin n) -> Real) :
    letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
    letI : MeasurableSpace Λ.torus := borel Λ.torus
    (∫ z : UnitAddTorus (Fin n), φ z ∂(volume : Measure (UnitAddTorus (Fin n)))) =
      ∫ x : Λ.torus,
        φ ((coordinateTorusAddEquivUnitAddTorus n : Λ.torus -> UnitAddTorus (Fin n)) x)
        ∂torusHaarMeasure Λ := by
  classical
  letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
  letI : MeasurableSpace Λ.torus := borel Λ.torus
  have hmp := measurePreserving_coordinateTorusAddEquivUnitAddTorus_global Λ
  have hemb := measurableEmbedding_coordinateTorusAddEquivUnitAddTorus Λ
  simpa [Function.comp_def] using (hmp.integral_comp hemb φ).symm

private lemma integral_flatTorus_eq_integral_unitTorus
    {n : Nat} (Λ : KNFullRankLattice n) (ψ : Λ.torus -> Real) :
    letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
    letI : MeasurableSpace Λ.torus := borel Λ.torus
    (∫ x : Λ.torus, ψ x ∂torusHaarMeasure Λ) =
      ∫ z : UnitAddTorus (Fin n),
        ψ ((coordinateTorusAddEquivUnitAddTorus n).symm z)
        ∂(volume : Measure (UnitAddTorus (Fin n))) := by
  classical
  letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
  letI : MeasurableSpace Λ.torus := borel Λ.torus
  simpa [Function.comp_def] using
    (integral_unitTorus_eq_integral_flatTorus Λ
      (fun z : UnitAddTorus (Fin n) =>
        ψ ((coordinateTorusAddEquivUnitAddTorus n).symm z))).symm

private noncomputable def torusCharacterLift {n : Nat}
    (Λ : KNFullRankLattice n)
    (u : {u : RealEuclideanSpace n // u ∈ (knDualLattice Λ).carrier})
    (x : RealEuclideanSpace n) : Circle :=
  Circle.exp (2 * Real.pi * inner Real u.1 (Matrix.toEuclideanLin Λ.basis.matrix x))

private lemma continuous_torusCharacterLift {n : Nat}
    (Λ : KNFullRankLattice n)
    (u : {u : RealEuclideanSpace n // u ∈ (knDualLattice Λ).carrier}) :
    Continuous (torusCharacterLift Λ u) := by
  unfold torusCharacterLift
  fun_prop

private lemma continuous_torusCharacterLift_flatTorusAmbient {n : Nat}
    (Λ : KNFullRankLattice n)
    (u : {u : RealEuclideanSpace n // u ∈ (knDualLattice Λ).carrier}) :
    @Continuous (RealEuclideanSpace n) Circle
      (@UniformSpace.toTopologicalSpace (RealEuclideanSpace n)
        (@PseudoMetricSpace.toUniformSpace (RealEuclideanSpace n)
          (flatTorusAmbientSeminorm n Λ.basis).toPseudoMetricSpace))
      inferInstance
      (torusCharacterLift Λ u) := by
  have hstd : Continuous (fun y : RealEuclideanSpace n =>
      Circle.exp (2 * Real.pi * inner Real u.1 y)) := by
    fun_prop
  have hlin := continuous_toEuclideanLin_flatTorusAmbient_to_standard Λ.basis
  simpa [torusCharacterLift, Function.comp_def] using
    (@Continuous.comp (RealEuclideanSpace n) (RealEuclideanSpace n) Circle
      (@UniformSpace.toTopologicalSpace (RealEuclideanSpace n)
        (@PseudoMetricSpace.toUniformSpace (RealEuclideanSpace n)
          (flatTorusAmbientSeminorm n Λ.basis).toPseudoMetricSpace))
      inferInstance inferInstance
      (Matrix.toEuclideanLin Λ.basis.matrix)
      (fun y : RealEuclideanSpace n => Circle.exp (2 * Real.pi * inner Real u.1 y))
      hstd hlin)

private lemma matrix_toEuclideanLin_mem_carrier_of_mem_integerLattice {n : Nat}
    (Λ : KNFullRankLattice n) {γ : RealEuclideanSpace n}
    (hγ : γ ∈ integerLattice n) :
    Matrix.toEuclideanLin Λ.basis.matrix γ ∈ Λ.carrier := by
  change Matrix.toEuclideanLin Λ.basis.matrix γ ∈ matrixIntegerLattice n Λ.basis
  exact AddSubgroup.mem_map.mpr ⟨γ, hγ, rfl⟩

private lemma torusCharacterLift_add_integerLattice {n : Nat}
    (Λ : KNFullRankLattice n)
    (u : {u : RealEuclideanSpace n // u ∈ (knDualLattice Λ).carrier})
    (x γ : RealEuclideanSpace n) (hγ : γ ∈ integerLattice n) :
    torusCharacterLift Λ u (x + γ) = torusCharacterLift Λ u x := by
  have hAγ : Matrix.toEuclideanLin Λ.basis.matrix γ ∈ Λ.carrier :=
    matrix_toEuclideanLin_mem_carrier_of_mem_integerLattice Λ hγ
  rcases ((knDualLattice_spec Λ u.1).1 u.2
      (Matrix.toEuclideanLin Λ.basis.matrix γ) hAγ) with ⟨z, hz⟩
  unfold torusCharacterLift
  rw [map_add, inner_add_right]
  have hper :
      Circle.exp
          (2 * Real.pi * inner Real u.1 (Matrix.toEuclideanLin Λ.basis.matrix γ)) = 1 := by
    rw [hz]
    convert Circle.exp_int_mul_two_pi z using 2
    ring
  rw [show
      2 * Real.pi *
          (inner Real u.1 (Matrix.toEuclideanLin Λ.basis.matrix x) +
            inner Real u.1 (Matrix.toEuclideanLin Λ.basis.matrix γ)) =
        2 * Real.pi * inner Real u.1 (Matrix.toEuclideanLin Λ.basis.matrix x) +
          2 * Real.pi * inner Real u.1 (Matrix.toEuclideanLin Λ.basis.matrix γ) by ring]
  rw [Circle.exp_add, hper, mul_one]

private theorem torusCharacterLift_periodic {n : Nat}
    (Λ : KNFullRankLattice n)
    (u : {u : RealEuclideanSpace n // u ∈ (knDualLattice Λ).carrier})
    (x : RealEuclideanSpace n) (m : Fin n -> Int) :
    torusCharacterLift Λ u (x + integerVector n m) = torusCharacterLift Λ u x :=
  torusCharacterLift_add_integerLattice Λ u x (integerVector n m) ⟨m, rfl⟩

private noncomputable def torusCharacter {n : Nat}
    (Λ : KNFullRankLattice n)
    (u : {u : RealEuclideanSpace n // u ∈ (knDualLattice Λ).carrier}) :
    Λ.torus → Circle := by
  dsimp [KNFullRankLattice.torus, flatTorus]
  exact Quotient.lift (torusCharacterLift Λ u) (by
    intro x y hxy
    have hγ : -x + y ∈ integerLattice n := QuotientAddGroup.leftRel_apply.mp hxy
    have hy : y = x + (-x + y) := by abel
    rw [hy]
    exact (torusCharacterLift_add_integerLattice Λ u x (-x + y) hγ).symm)

private lemma torusCharacter_apply_mk {n : Nat}
    (Λ : KNFullRankLattice n)
    (u : {u : RealEuclideanSpace n // u ∈ (knDualLattice Λ).carrier})
    (x : RealEuclideanSpace n) :
    torusCharacter Λ u (QuotientAddGroup.mk' (integerLattice n) x) =
      torusCharacterLift Λ u x := by
  rfl

private lemma continuous_torusCharacter {n : Nat}
    (Λ : KNFullRankLattice n)
    (u : {u : RealEuclideanSpace n // u ∈ (knDualLattice Λ).carrier}) :
    @Continuous Λ.torus Circle
      (@UniformSpace.toTopologicalSpace Λ.torus
        (@PseudoMetricSpace.toUniformSpace Λ.torus
          (Λ.torusSeminormedAddCommGroup.toPseudoMetricSpace)))
      inferInstance
      (torusCharacter Λ u) := by
  letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
  letI : SeminormedAddCommGroup (RealEuclideanSpace n) :=
    flatTorusAmbientSeminorm n Λ.basis
  dsimp [torusCharacter]
  simpa [KNFullRankLattice.torusSeminormedAddCommGroup, KNFullRankLattice.torus, flatTorus]
    using
      (@Continuous.quotient_lift (RealEuclideanSpace n) Circle
        (@UniformSpace.toTopologicalSpace (RealEuclideanSpace n)
          (@PseudoMetricSpace.toUniformSpace (RealEuclideanSpace n)
            (flatTorusAmbientSeminorm n Λ.basis).toPseudoMetricSpace))
        inferInstance
        (QuotientAddGroup.leftRel (integerLattice n))
        (torusCharacterLift Λ u)
        (continuous_torusCharacterLift_flatTorusAmbient Λ u)
        (by
          intro x y hxy
          have hγ : -x + y ∈ integerLattice n := QuotientAddGroup.leftRel_apply.mp hxy
          have hy : y = x + (-x + y) := by abel
          rw [hy]
          exact (torusCharacterLift_add_integerLattice Λ u x (-x + y) hγ).symm))

private lemma integerLattice_finite_inter_isBounded
    {n : Nat} {s : Set (RealEuclideanSpace n)} (hs : Bornology.IsBounded s) :
    Set.Finite (s ∩ (integerLattice n : Set (RealEuclideanSpace n))) := by
  rw [integerLattice_eq_standardIntegerSubmodule n]
  simpa using ZSpan.setFinite_inter (euclideanStdBasis n) hs

private lemma toEuclideanLin_smul_matrix {n : Nat}
    (A : Matrix (Fin n) (Fin n) Real) (t : Real) (x : RealEuclideanSpace n) :
    Matrix.toEuclideanLin (t • A) x = t • Matrix.toEuclideanLin A x := by
  ext i
  simp [Matrix.toEuclideanLin, Matrix.mulVec]

private noncomputable def scaledLatticeBasis {n : Nat} (A : LatticeBasis n)
    (t : Real) (ht : t ≠ 0) : LatticeBasis n where
  matrix := t • A.matrix
  invertible := by
    rw [Matrix.det_smul]
    exact IsUnit.mul (isUnit_iff_ne_zero.mpr (pow_ne_zero _ ht)) A.invertible

private lemma scaledLattice_carrier_iff {n : Nat}
    (Λ : KNFullRankLattice n) {t : Real} (ht : t ≠ 0) (γ : RealEuclideanSpace n) :
    γ ∈ (⟨scaledLatticeBasis Λ.basis t ht⟩ : KNFullRankLattice n).carrier ↔
      ∃ η : RealEuclideanSpace n, η ∈ Λ.carrier ∧ γ = t • η := by
  constructor
  · intro hγ
    simp [KNFullRankLattice.carrier, matrixIntegerLattice, integerLattice,
      scaledLatticeBasis] at hγ
    rcases hγ with ⟨k, rfl⟩
    let η : RealEuclideanSpace n := Matrix.toEuclideanLin Λ.basis.matrix (integerVector n k)
    refine ⟨η, ?_, ?_⟩
    · change η ∈ matrixIntegerLattice n Λ.basis
      simp [η, matrixIntegerLattice, integerLattice]
    · simp [η]
  · rintro ⟨η, hη, rfl⟩
    simp [KNFullRankLattice.carrier, matrixIntegerLattice, integerLattice] at hη ⊢
    rcases hη with ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    simpa [scaledLatticeBasis] using
      toEuclideanLin_smul_matrix Λ.basis.matrix t (integerVector n k)

private noncomputable def matrixEuclideanBasis {n : Nat} (A : LatticeBasis n) :
    Module.Basis (Fin n) Real (RealEuclideanSpace n) :=
  (euclideanStdBasis n).map (matrixLinearEquiv A)

private lemma integerVector_eq_sum_euclideanStdBasis
    (n : Nat) (k : Fin n -> Int) :
    integerVector n k = (∑ i, k i • euclideanStdBasis n i : RealEuclideanSpace n) := by
  ext i
  simp [integerVector, euclideanStdBasis]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Pi.single_eq_of_ne]
    · simp
    · exact fun h => hj h.symm
  · intro hi
    simp at hi

private lemma matrixEuclideanBasis_sum_eq {n : Nat}
    (A : LatticeBasis n) (k : Fin n -> Int) :
    (∑ i, k i • matrixEuclideanBasis A i : RealEuclideanSpace n) =
      Matrix.toEuclideanLin A.matrix (integerVector n k) := by
  calc
    (∑ i, k i • matrixEuclideanBasis A i : RealEuclideanSpace n) =
        matrixLinearEquiv A (∑ i, k i • euclideanStdBasis n i : RealEuclideanSpace n) := by
          simp [matrixEuclideanBasis, map_sum]
    _ = matrixLinearEquiv A (integerVector n k) := by
          rw [← integerVector_eq_sum_euclideanStdBasis]
    _ = Matrix.toEuclideanLin A.matrix (integerVector n k) := by
          exact congrFun
            (congrArg (fun f : RealEuclideanSpace n →ₗ[Real] RealEuclideanSpace n =>
              (f : RealEuclideanSpace n → RealEuclideanSpace n))
              (matrixLinearEquiv_eq_toEuclideanLin A)) (integerVector n k)

private lemma matrixIntegerLattice_eq_span_matrixEuclideanBasis {n : Nat} (A : LatticeBasis n) :
    matrixIntegerLattice n A =
      (Submodule.span ℤ (Set.range (matrixEuclideanBasis A))).toAddSubgroup := by
  ext y
  constructor
  · simp [matrixIntegerLattice, integerLattice]
    rintro k rfl
    rw [Submodule.mem_span_range_iff_exists_fun]
    exact ⟨k, matrixEuclideanBasis_sum_eq A k⟩
  · intro hy
    change y ∈ Submodule.span ℤ (Set.range (matrixEuclideanBasis A)) at hy
    rw [Submodule.mem_span_range_iff_exists_fun] at hy
    rcases hy with ⟨k, rfl⟩
    rw [matrixEuclideanBasis_sum_eq A k]
    simp [matrixIntegerLattice, integerLattice]

private theorem matrixIntegerLattice_quotient_compactSpace {n : Nat} (A : LatticeBasis n) :
    CompactSpace (RealEuclideanSpace n ⧸ matrixIntegerLattice n A) := by
  rw [← isCompact_univ_iff]
  let L : Submodule ℤ (RealEuclideanSpace n) :=
    Submodule.span ℤ (Set.range (matrixEuclideanBasis A))
  haveI : DiscreteTopology L := by infer_instance
  haveI : IsZLattice ℝ L := by infer_instance
  let q : RealEuclideanSpace n → RealEuclideanSpace n ⧸ matrixIntegerLattice n A :=
    QuotientAddGroup.mk' (matrixIntegerLattice n A)
  have hcomp : IsCompact (Set.range q) := by
    refine IsZLattice.isCompact_range_of_periodic L q continuous_quotient_mk' ?_
    intro z w hw
    change (QuotientAddGroup.mk' (matrixIntegerLattice n A) (z + w) :
        RealEuclideanSpace n ⧸ matrixIntegerLattice n A) =
      QuotientAddGroup.mk' (matrixIntegerLattice n A) z
    rw [QuotientAddGroup.mk'_eq_mk']
    refine ⟨-w, ?_, by abel⟩
    have hw' : w ∈ matrixIntegerLattice n A := by
      simpa [matrixIntegerLattice_eq_span_matrixEuclideanBasis A, L] using hw
    exact (matrixIntegerLattice n A).neg_mem hw'
  have hrange : Set.range q = Set.univ := by
    ext y
    constructor
    · intro _
      trivial
    · intro _
      refine QuotientAddGroup.induction_on y ?_
      intro x
      exact ⟨x, rfl⟩
  simpa [hrange] using hcomp

private theorem flatTorusUnitLatticeIsometry_aux (n : Nat) (A : LatticeBasis n) :
    (letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A;
      letI : PseudoMetricSpace (flatTorusEuclideanLatticeQuotient n A) :=
        flatTorusEuclideanLatticeMetric n A;
      exists e : Equiv (flatTorus n A) (flatTorusEuclideanLatticeQuotient n A),
        Isometry e) := by
  classical
  let b : Module.Basis (Fin n) Real (RealEuclideanSpace n) :=
    (EuclideanSpace.basisFun (Fin n) Real).toBasis
  let L : RealEuclideanSpace n →ₗ[Real] RealEuclideanSpace n :=
    Matrix.toEuclideanLin A.matrix
  let eLin : RealEuclideanSpace n ≃ₗ[Real] RealEuclideanSpace n :=
    Matrix.toLinearEquiv b A.matrix A.invertible
  let eAdd : RealEuclideanSpace n ≃+ RealEuclideanSpace n := eLin.toAddEquiv
  have hLin : (eLin : RealEuclideanSpace n →ₗ[Real] RealEuclideanSpace n) = L := by
    change (eLin : RealEuclideanSpace n →ₗ[Real] RealEuclideanSpace n) =
      Matrix.toEuclideanLin A.matrix
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    rfl
  have hmap : AddSubgroup.map (eAdd : RealEuclideanSpace n →+ RealEuclideanSpace n)
      (integerLattice n) = matrixIntegerLattice n A := by
    ext y
    simp [matrixIntegerLattice, eAdd, L, hLin]
  let qAdd : (RealEuclideanSpace n ⧸ integerLattice n) ≃+
      (RealEuclideanSpace n ⧸ matrixIntegerLattice n A) :=
    QuotientAddGroup.congr (integerLattice n) (matrixIntegerLattice n A) eAdd hmap
  let sourceQuotSeminorm :
      SeminormedAddCommGroup (RealEuclideanSpace n ⧸ integerLattice n) :=
    @QuotientAddGroup.instSeminormedAddCommGroup (RealEuclideanSpace n)
      (flatTorusAmbientSeminorm n A) (integerLattice n)
  have hTargetMetric :
      flatTorusEuclideanLatticeMetric n A =
        (inferInstance : PseudoMetricSpace
          (RealEuclideanSpace n ⧸ matrixIntegerLattice n A)) := by
    dsimp [flatTorusEuclideanLatticeMetric]
  rw [hTargetMetric]
  letI : SeminormedAddCommGroup (RealEuclideanSpace n ⧸ integerLattice n) :=
    sourceQuotSeminorm
  letI : Norm (RealEuclideanSpace n ⧸ integerLattice n) := sourceQuotSeminorm.toNorm
  refine ⟨qAdd.toEquiv, ?_⟩
  refine AddMonoidHomClass.isometry_of_norm qAdd ?_
  intro x
  refine QuotientAddGroup.induction_on x ?_
  intro v
  have hqv : qAdd ((v : RealEuclideanSpace n) :
        RealEuclideanSpace n ⧸ integerLattice n) =
      ((eAdd v : RealEuclideanSpace n) :
        RealEuclideanSpace n ⧸ matrixIntegerLattice n A) := rfl
  rw [hqv]
  have heAdd_v : eAdd v = L v := by
    change eLin v = L v
    exact congrFun
      (congrArg (fun f : RealEuclideanSpace n →ₗ[Real] RealEuclideanSpace n =>
        (f : RealEuclideanSpace n → RealEuclideanSpace n)) hLin) v
  rw [heAdd_v]
  have hnorm_source (z : RealEuclideanSpace n) :
      @norm (RealEuclideanSpace n) (flatTorusAmbientSeminorm n A).toNorm z =
        ‖L z‖ := by
    dsimp [flatTorusAmbientSeminorm, L]
    rfl
  have hsourceNorm :
      ‖((v : RealEuclideanSpace n) :
          RealEuclideanSpace n ⧸ integerLattice n)‖ =
        sInf ((fun s : RealEuclideanSpace n =>
          @norm (RealEuclideanSpace n) (flatTorusAmbientSeminorm n A).toNorm
            (v + s)) '' (integerLattice n : Set (RealEuclideanSpace n))) := by
    letI : SeminormedAddCommGroup (RealEuclideanSpace n) := flatTorusAmbientSeminorm n A
    simpa using (quotient_norm_mk_eq (integerLattice n) v)
  have htargetNorm :
      ‖((L v : RealEuclideanSpace n) :
          RealEuclideanSpace n ⧸ matrixIntegerLattice n A)‖ =
        sInf ((fun t : RealEuclideanSpace n => ‖L v + t‖) ''
          (matrixIntegerLattice n A : Set (RealEuclideanSpace n))) := by
    simpa using (quotient_norm_mk_eq (matrixIntegerLattice n A) (L v))
  have hsourceSet :
      ((fun s : RealEuclideanSpace n =>
        @norm (RealEuclideanSpace n) (flatTorusAmbientSeminorm n A).toNorm
          (v + s)) '' (integerLattice n : Set (RealEuclideanSpace n))) =
      ((fun s : RealEuclideanSpace n => ‖L v + L s‖) ''
        (integerLattice n : Set (RealEuclideanSpace n))) := by
    ext r
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨s, hs, ?_⟩
      calc
        ‖L v + L s‖ = ‖L (v + s)‖ := by rw [map_add]
        _ = @norm (RealEuclideanSpace n) (flatTorusAmbientSeminorm n A).toNorm
            (v + s) := (hnorm_source (v + s)).symm
    · rintro ⟨s, hs, rfl⟩
      refine ⟨s, hs, ?_⟩
      calc
        @norm (RealEuclideanSpace n) (flatTorusAmbientSeminorm n A).toNorm
            (v + s) = ‖L (v + s)‖ := hnorm_source (v + s)
        _ = ‖L v + L s‖ := by rw [map_add]
  have hmatrixSet :
      ((fun s : RealEuclideanSpace n => ‖L v + L s‖) ''
        (integerLattice n : Set (RealEuclideanSpace n))) =
      ((fun t : RealEuclideanSpace n => ‖L v + t‖) ''
        (matrixIntegerLattice n A : Set (RealEuclideanSpace n))) := by
    ext r
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨L s, ?_, rfl⟩
      exact ⟨s, hs, by dsimp [L]⟩
    · rintro ⟨t, ht, rfl⟩
      rcases ht with ⟨s, hs, hst⟩
      subst hst
      exact ⟨s, hs, rfl⟩
  rw [htargetNorm, hsourceNorm, hsourceSet, hmatrixSet]

private theorem flatTorusMetric_compactSpace {n : Nat} (A : LatticeBasis n) :
    letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A
    CompactSpace (flatTorus n A) := by
  classical
  letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A
  letI : PseudoMetricSpace (flatTorusEuclideanLatticeQuotient n A) :=
    flatTorusEuclideanLatticeMetric n A
  haveI : CompactSpace (flatTorusEuclideanLatticeQuotient n A) := by
    dsimp [flatTorusEuclideanLatticeQuotient]
    exact matrixIntegerLattice_quotient_compactSpace A
  rcases flatTorusUnitLatticeIsometry_aux n A with ⟨e, he⟩
  have hsymm : Isometry e.symm := by
    refine Isometry.of_dist_eq ?_
    intro x y
    have h := he.dist_eq (e.symm x) (e.symm y)
    simpa using h.symm
  rw [← isCompact_univ_iff]
  have hcompact_range : IsCompact (Set.range e.symm) :=
    by simpa [Set.image_univ] using isCompact_univ.image hsymm.continuous
  have hrange : Set.range e.symm = Set.univ := by
    ext x
    constructor
    · intro _
      trivial
    · intro _
      exact ⟨e x, by simp⟩
  simpa [hrange] using hcompact_range

private theorem flatTorusMetric_secondCountableTopology {n : Nat} (A : LatticeBasis n) :
    letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A
    SecondCountableTopology (flatTorus n A) := by
  letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A
  haveI : CompactSpace (flatTorus n A) := flatTorusMetric_compactSpace A
  exact UniformSpace.secondCountable_of_separable (flatTorus n A)

private lemma flatTorusMetric_dist_mk_le_matrixNorm
    (n : Nat) (A : LatticeBasis n) (u v : RealEuclideanSpace n) :
    @dist (flatTorus n A) (flatTorusMetric n A).toDist
        (QuotientAddGroup.mk' _ u : flatTorus n A)
        (QuotientAddGroup.mk' _ v : flatTorus n A) ≤
      ‖Matrix.toEuclideanLin A.matrix (u - v)‖ := by
  let ambient : SeminormedAddCommGroup (RealEuclideanSpace n) :=
    SeminormedAddCommGroup.induced (RealEuclideanSpace n) (RealEuclideanSpace n)
      (Matrix.toEuclideanLin A.matrix)
  let quotientSeminorm : SeminormedAddCommGroup (flatTorus n A) := by
    change SeminormedAddCommGroup (RealEuclideanSpace n ⧸ integerLattice n)
    exact @QuotientAddGroup.instSeminormedAddCommGroup (RealEuclideanSpace n) ambient
      (integerLattice n)
  have hmetric : flatTorusMetric n A = quotientSeminorm.toPseudoMetricSpace := rfl
  rw [hmetric]
  letI : SeminormedAddCommGroup (RealEuclideanSpace n) := ambient
  letI : SeminormedAddCommGroup (flatTorus n A) := quotientSeminorm
  change dist (QuotientAddGroup.mk' _ u : flatTorus n A)
      (QuotientAddGroup.mk' _ v : flatTorus n A) ≤
    ‖Matrix.toEuclideanLin A.matrix (u - v)‖
  rw [dist_eq_norm]
  dsimp [flatTorus]
  change ‖((QuotientAddGroup.mk' _ : RealEuclideanSpace n →+
        RealEuclideanSpace n ⧸ _) u -
      (QuotientAddGroup.mk' _ : RealEuclideanSpace n →+
        RealEuclideanSpace n ⧸ _) v)‖ ≤
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

@[reducible]
private def flatTorusAddCommGroup (n : Nat) (A : LatticeBasis n) :
    AddCommGroup (flatTorus n A) := by
  change AddCommGroup (RealEuclideanSpace n ⧸ integerLattice n)
  infer_instance

private lemma flatTorusMetric_dist_add_mk_le_matrixNorm
    (n : Nat) (A : LatticeBasis n) (x : flatTorus n A) (h : RealEuclideanSpace n) :
    letI : AddCommGroup (flatTorus n A) := flatTorusAddCommGroup n A
    letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A
    dist (x + (show flatTorus n A from QuotientAddGroup.mk' (integerLattice n) h)) x ≤
      ‖Matrix.toEuclideanLin A.matrix h‖ := by
  letI : AddCommGroup (flatTorus n A) := flatTorusAddCommGroup n A
  letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A
  refine QuotientAddGroup.induction_on x ?_
  intro u
  have hdist := flatTorusMetric_dist_mk_le_matrixNorm n A (u + h) u
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hdist

private noncomputable def coordinateVectorForPhysicalDirection {n : Nat}
    (A : LatticeBasis n) (j : Fin n) : RealEuclideanSpace n :=
  (matrixLinearEquiv A).symm (euclideanStdBasis n j)

private lemma matrix_toEuclideanLin_coordinateVectorForPhysicalDirection {n : Nat}
    (A : LatticeBasis n) (j : Fin n) :
    Matrix.toEuclideanLin A.matrix (coordinateVectorForPhysicalDirection A j) =
      euclideanStdBasis n j := by
  have hlin :
      (matrixLinearEquiv A : RealEuclideanSpace n →ₗ[Real] RealEuclideanSpace n) =
        Matrix.toEuclideanLin A.matrix :=
    matrixLinearEquiv_eq_toEuclideanLin A
  change Matrix.toEuclideanLin A.matrix ((matrixLinearEquiv A).symm (euclideanStdBasis n j)) =
    euclideanStdBasis n j
  rw [← hlin]
  simp

private lemma flatTorusMetric_dist_add_physicalDirection_le_abs
    {n : Nat} (A : LatticeBasis n) (x : flatTorus n A) (j : Fin n) (t : Real) :
    letI : AddCommGroup (flatTorus n A) := flatTorusAddCommGroup n A
    letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A
    dist
        (x + (show flatTorus n A from QuotientAddGroup.mk' (integerLattice n)
          (t • coordinateVectorForPhysicalDirection A j))) x ≤
      |t| := by
  letI : AddCommGroup (flatTorus n A) := flatTorusAddCommGroup n A
  letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A
  calc
    dist
        (x + (show flatTorus n A from QuotientAddGroup.mk' (integerLattice n)
          (t • coordinateVectorForPhysicalDirection A j))) x
        ≤ ‖Matrix.toEuclideanLin A.matrix (t • coordinateVectorForPhysicalDirection A j)‖ :=
      flatTorusMetric_dist_add_mk_le_matrixNorm n A x
        (t • coordinateVectorForPhysicalDirection A j)
    _ = |t| := by
      rw [map_smul, matrix_toEuclideanLin_coordinateVectorForPhysicalDirection]
      rw [norm_smul]
      simp [euclideanStdBasis]

private lemma inner_integerVector_coordinateVectorForPhysicalDirection {n : Nat}
    (A : LatticeBasis n) (k : Fin n -> Int) (j : Fin n) :
    inner Real (integerVector n k) (coordinateVectorForPhysicalDirection A j) =
      inner Real
        (Matrix.toEuclideanLin A.matrix⁻¹.transpose (integerVector n k))
        (euclideanStdBasis n j) := by
  let e := matrixLinearEquiv A
  have heq : (e : RealEuclideanSpace n →ₗ[Real] RealEuclideanSpace n) =
      Matrix.toEuclideanLin A.matrix :=
    matrixLinearEquiv_eq_toEuclideanLin A
  have hsymm_eq :
      (e.symm : RealEuclideanSpace n →ₗ[Real] RealEuclideanSpace n) =
        Matrix.toEuclideanLin A.matrix⁻¹ := by
    ext x i
    let z : RealEuclideanSpace n := Matrix.toEuclideanLin A.matrix⁻¹ x
    have hz : Matrix.toEuclideanLin A.matrix z = x := by
      ext i
      simp [z, Matrix.toEuclideanLin, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv,
        IsUnit.ne_zero A.invertible]
    have hez : e z = x := by
      change (e : RealEuclideanSpace n →ₗ[Real] RealEuclideanSpace n) z = x
      rw [heq]
      exact hz
    have hvec :
        e.symm x = Matrix.toEuclideanLin A.matrix⁻¹ x := by
      calc
        e.symm x = z := by
          rw [← hez]
          simp
        _ = Matrix.toEuclideanLin A.matrix⁻¹ x := rfl
    exact congrArg (fun y : RealEuclideanSpace n => y i) hvec
  change inner Real (integerVector n k)
      ((e.symm : RealEuclideanSpace n →ₗ[Real] RealEuclideanSpace n)
        (euclideanStdBasis n j)) =
    inner Real (Matrix.toEuclideanLin A.matrix⁻¹.transpose (integerVector n k))
      (euclideanStdBasis n j)
  rw [hsymm_eq]
  simp only [EuclideanSpace.inner_eq_star_dotProduct]
  change dotProduct (A.matrix⁻¹.mulVec (euclideanStdBasis n j : Fin n -> Real))
      (integerVector n k : Fin n -> Real) =
    dotProduct (euclideanStdBasis n j : Fin n -> Real)
      (A.matrix⁻¹.transpose.mulVec (integerVector n k : Fin n -> Real))
  rw [dotProduct_comm (A.matrix⁻¹.mulVec (euclideanStdBasis n j : Fin n -> Real))]
  exact (Matrix.dotProduct_transpose_mulVec (A := A.matrix⁻¹)
    (x := (euclideanStdBasis n j : Fin n -> Real))
    (y := (integerVector n k : Fin n -> Real))).symm

private lemma matrixIntegerLattice_finite_inter_isBounded
    {n : Nat} (A : LatticeBasis n) {s : Set (RealEuclideanSpace n)}
    (hs : Bornology.IsBounded s) :
    Set.Finite (s ∩ (matrixIntegerLattice n A : Set (RealEuclideanSpace n))) := by
  classical
  let e := matrixLinearEquiv A
  let L : RealEuclideanSpace n →ₗ[Real] RealEuclideanSpace n := Matrix.toEuclideanLin A.matrix
  have heq : (e : RealEuclideanSpace n →ₗ[Real] RealEuclideanSpace n) = L := by
    simpa [e, L] using matrixLinearEquiv_eq_toEuclideanLin A
  have hs_pre : Bornology.IsBounded (e.symm '' s) := by
    let f : RealEuclideanSpace n →L[Real] RealEuclideanSpace n :=
      LinearMap.toContinuousLinearMap
        (e.symm : RealEuclideanSpace n →ₗ[Real] RealEuclideanSpace n)
    simpa [f] using Bornology.IsBounded.image f hs
  have hfinite_pre : Set.Finite
      ((e.symm '' s) ∩ (integerLattice n : Set (RealEuclideanSpace n))) :=
    integerLattice_finite_inter_isBounded hs_pre
  refine Set.Finite.subset (hfinite_pre.image e) ?_
  rintro y ⟨hyS, hyL⟩
  simp [matrixIntegerLattice, L, ← heq] at hyL
  rcases hyL with ⟨z, hz, rfl⟩
  exact ⟨z, ⟨⟨e z, hyS, by simp⟩, hz⟩, by simp⟩

private lemma lattice_nearest_minimizer {n : Nat}
    (Λ : KNFullRankLattice n) (x : RealEuclideanSpace n) :
    ∃ γ : RealEuclideanSpace n, γ ∈ Λ.carrier ∧
      ∀ η : RealEuclideanSpace n, η ∈ Λ.carrier -> ‖x - γ‖ ≤ ‖x - η‖ := by
  classical
  let S : Set (RealEuclideanSpace n) :=
    Metric.closedBall x ‖x‖ ∩ (Λ.carrier : Set (RealEuclideanSpace n))
  have hSfinite : S.Finite := by
    simpa [S, KNFullRankLattice.carrier] using
      matrixIntegerLattice_finite_inter_isBounded Λ.basis
        (s := Metric.closedBall x ‖x‖) Metric.isBounded_closedBall
  have hSnonempty : S.Nonempty := by
    refine ⟨0, ?_⟩
    constructor
    · simpa [Metric.mem_closedBall, dist_eq_norm] using le_rfl
    · exact Λ.carrier.zero_mem
  let F := hSfinite.toFinset
  have hFnonempty : F.Nonempty := by
    rcases hSnonempty with ⟨y, hy⟩
    exact ⟨y, by simpa [F] using hy⟩
  obtain ⟨γ, hγF, hγmin⟩ := Finset.exists_min_image F (fun y => ‖x - y‖) hFnonempty
  have hγS : γ ∈ S := by simpa [F] using hγF
  refine ⟨γ, hγS.2, ?_⟩
  intro η hη
  by_cases hηball : η ∈ Metric.closedBall x ‖x‖
  · exact hγmin η (by simpa [F, S] using And.intro hηball hη)
  · have hγ_le_R : ‖x - γ‖ ≤ ‖x‖ := by
      simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hγS.1
    have hR_lt_eta : ‖x‖ < ‖x - η‖ := by
      have hηball' : ¬ ‖x - η‖ ≤ ‖x‖ := by
        simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hηball
      exact not_le.mp hηball'
    exact le_trans hγ_le_R hR_lt_eta.le

/-- Nearest lattice vectors are attained. -/
theorem nearest_lattice_vector_attained {n : Nat}
    (Λ : KNFullRankLattice n) (x : RealEuclideanSpace n) :
    ∃ γ : RealEuclideanSpace n,
      γ ∈ Λ.carrier ∧ distanceToLattice Λ x = ‖x - γ‖ := by
  obtain ⟨γ, hγ, hmin⟩ := lattice_nearest_minimizer Λ x
  refine ⟨γ, hγ, ?_⟩
  let S := ((fun γ : RealEuclideanSpace n => ‖x - γ‖) ''
    (Λ.carrier : Set (RealEuclideanSpace n)))
  have hSnonempty : S.Nonempty := ⟨‖x - γ‖, ⟨γ, hγ, rfl⟩⟩
  have hSbdd : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro r ⟨η, _hη, rfl⟩
    exact norm_nonneg _
  unfold distanceToLattice
  change sInf S = ‖x - γ‖
  apply le_antisymm
  · exact csInf_le hSbdd ⟨γ, hγ, rfl⟩
  · rw [le_csInf_iff hSbdd hSnonempty]
    rintro r ⟨η, hη, rfl⟩
    exact hmin η hη

private lemma distanceToLattice_le_norm_sub {n : Nat}
    (Λ : KNFullRankLattice n) (x γ : RealEuclideanSpace n) (hγ : γ ∈ Λ.carrier) :
    distanceToLattice Λ x ≤ ‖x - γ‖ := by
  let S := ((fun γ : RealEuclideanSpace n => ‖x - γ‖) ''
    (Λ.carrier : Set (RealEuclideanSpace n)))
  have hSbdd : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro r ⟨η, _hη, rfl⟩
    exact norm_nonneg _
  unfold distanceToLattice
  change sInf S ≤ ‖x - γ‖
  exact csInf_le hSbdd ⟨γ, hγ, rfl⟩

private lemma distanceToLattice_le_basis_norm_sum {n : Nat}
    (Λ : KNFullRankLattice n) (x : RealEuclideanSpace n) :
    distanceToLattice Λ x ≤ ∑ i, ‖matrixEuclideanBasis Λ.basis i‖ := by
  classical
  let b := matrixEuclideanBasis Λ.basis
  let γ : RealEuclideanSpace n := (ZSpan.floor b x : RealEuclideanSpace n)
  have hγ : γ ∈ Λ.carrier := by
    change γ ∈ matrixIntegerLattice n Λ.basis
    rw [matrixIntegerLattice_eq_span_matrixEuclideanBasis Λ.basis]
    exact (ZSpan.floor b x).property
  calc
    distanceToLattice Λ x ≤ ‖x - γ‖ := distanceToLattice_le_norm_sub Λ x γ hγ
    _ = ‖ZSpan.fract b x‖ := by rfl
    _ ≤ ∑ i, ‖b i‖ := ZSpan.norm_fract_le b x

private lemma distanceToLattice_range_bddAbove {n : Nat} (Λ : KNFullRankLattice n) :
    BddAbove (Set.range (distanceToLattice Λ)) := by
  refine ⟨∑ i, ‖matrixEuclideanBasis Λ.basis i‖, ?_⟩
  rintro r ⟨x, rfl⟩
  exact distanceToLattice_le_basis_norm_sum Λ x

private lemma distanceToLattice_eq_norm_of_voronoi {n : Nat}
    (Λ : KNFullRankLattice n) {x : RealEuclideanSpace n}
    (hx : InClosedVoronoiCell Λ x) :
    distanceToLattice Λ x = ‖x‖ := by
  let S := ((fun γ : RealEuclideanSpace n => ‖x - γ‖) ''
    (Λ.carrier : Set (RealEuclideanSpace n)))
  have h0 : (0 : RealEuclideanSpace n) ∈ Λ.carrier := Λ.carrier.zero_mem
  have hSnonempty : S.Nonempty := ⟨‖x - 0‖, ⟨0, h0, rfl⟩⟩
  have hSbdd : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro r ⟨η, _hη, rfl⟩
    exact norm_nonneg _
  unfold distanceToLattice
  change sInf S = ‖x‖
  apply le_antisymm
  · simpa using (csInf_le hSbdd ⟨0, h0, rfl⟩)
  · rw [le_csInf_iff hSbdd hSnonempty]
    rintro r ⟨η, hη, rfl⟩
    exact hx η hη

private lemma distanceToLattice_nonneg {n : Nat}
    (Λ : KNFullRankLattice n) (x : RealEuclideanSpace n) :
    0 ≤ distanceToLattice Λ x := by
  obtain ⟨γ, _hγ, hγeq⟩ := nearest_lattice_vector_attained Λ x
  rw [hγeq]
  exact norm_nonneg _

private lemma norm_sub_le_norm_sub_add_norm_sub {n : Nat}
    (x y γ : RealEuclideanSpace n) :
    ‖x - γ‖ ≤ ‖x - y‖ + ‖y - γ‖ := by
  calc
    ‖x - γ‖ = ‖(x - y) + (y - γ)‖ := by
      congr 1
      abel
    _ ≤ ‖x - y‖ + ‖y - γ‖ := norm_add_le _ _

private lemma add_sub_eq_sub_sub {n : Nat}
    (z w γ : RealEuclideanSpace n) :
    z + w - γ = z - (γ - w) := by
  abel

private lemma add_sub_add_eq_sub {n : Nat}
    (z w η : RealEuclideanSpace n) :
    z + w - (η + w) = z - η := by
  abel

private lemma distanceToLattice_sub_le_dist {n : Nat}
    (Λ : KNFullRankLattice n) (x y : RealEuclideanSpace n) :
    distanceToLattice Λ x - distanceToLattice Λ y ≤ dist x y := by
  obtain ⟨γ, hγ, hyγ⟩ := nearest_lattice_vector_attained Λ y
  have hxγ := distanceToLattice_le_norm_sub Λ x γ hγ
  calc
    distanceToLattice Λ x - distanceToLattice Λ y ≤ ‖x - γ‖ - ‖y - γ‖ := by
      rw [hyγ]
      exact sub_le_sub_right hxγ _
    _ ≤ ‖x - y‖ := by
      have htri := norm_sub_le_norm_sub_add_norm_sub x y γ
      linarith
    _ = dist x y := by rw [dist_eq_norm]

private lemma lipschitzWith_distanceToLattice {n : Nat} (Λ : KNFullRankLattice n) :
    LipschitzWith 1 (distanceToLattice Λ) := by
  refine LipschitzWith.mk_one ?_
  intro x y
  rw [Real.dist_eq]
  exact abs_sub_le_iff.mpr
    ⟨distanceToLattice_sub_le_dist Λ x y,
      by simpa [dist_comm] using distanceToLattice_sub_le_dist Λ y x⟩

private lemma continuous_distanceToLattice {n : Nat} (Λ : KNFullRankLattice n) :
    Continuous (distanceToLattice Λ) :=
  (lipschitzWith_distanceToLattice Λ).continuous

private lemma distanceToLattice_add_lattice_eq {n : Nat}
    (Λ : KNFullRankLattice n) (z w : RealEuclideanSpace n) (hw : w ∈ Λ.carrier) :
    distanceToLattice Λ (z + w) = distanceToLattice Λ z := by
  apply le_antisymm
  · obtain ⟨η, hη, hηeq⟩ := nearest_lattice_vector_attained Λ z
    have hηw : η + w ∈ Λ.carrier := Λ.carrier.add_mem hη hw
    calc
      distanceToLattice Λ (z + w) ≤ ‖z + w - (η + w)‖ :=
        distanceToLattice_le_norm_sub Λ (z + w) (η + w) hηw
      _ = ‖z - η‖ := by rw [add_sub_add_eq_sub]
      _ = distanceToLattice Λ z := hηeq.symm
  · obtain ⟨γ, hγ, hγeq⟩ := nearest_lattice_vector_attained Λ (z + w)
    have hγw : γ - w ∈ Λ.carrier := Λ.carrier.sub_mem hγ hw
    calc
      distanceToLattice Λ z ≤ ‖z - (γ - w)‖ :=
        distanceToLattice_le_norm_sub Λ z (γ - w) hγw
      _ = ‖z + w - γ‖ := by rw [← add_sub_eq_sub_sub]
      _ = distanceToLattice Λ (z + w) := hγeq.symm

private lemma distanceToLattice_range_isCompact {n : Nat} (Λ : KNFullRankLattice n) :
    IsCompact (Set.range (distanceToLattice Λ)) := by
  let L : Submodule ℤ (RealEuclideanSpace n) :=
    Submodule.span ℤ (Set.range (matrixEuclideanBasis Λ.basis))
  haveI : DiscreteTopology L := by infer_instance
  haveI : IsZLattice ℝ L := by infer_instance
  refine IsZLattice.isCompact_range_of_periodic L (distanceToLattice Λ)
    (continuous_distanceToLattice Λ) ?_
  intro z w hw
  have hwcarrier : w ∈ Λ.carrier := by
    change w ∈ matrixIntegerLattice n Λ.basis
    rw [matrixIntegerLattice_eq_span_matrixEuclideanBasis Λ.basis]
    exact hw
  exact distanceToLattice_add_lattice_eq Λ z w hwcarrier

private lemma distanceToLattice_scaled {n : Nat}
    (Λ : KNFullRankLattice n) {t : Real} (ht : 0 < t) (x : RealEuclideanSpace n) :
    distanceToLattice (⟨scaledLatticeBasis Λ.basis t ht.ne'⟩ : KNFullRankLattice n) (t • x) =
      t * distanceToLattice Λ x := by
  let tΛ : KNFullRankLattice n := ⟨scaledLatticeBasis Λ.basis t ht.ne'⟩
  let SΛ := ((fun γ : RealEuclideanSpace n => ‖x - γ‖) ''
    (Λ.carrier : Set (RealEuclideanSpace n)))
  let StΛ := ((fun γ : RealEuclideanSpace n => ‖t • x - γ‖) ''
    (tΛ.carrier : Set (RealEuclideanSpace n)))
  have hset : StΛ = t • SΛ := by
    ext r
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      rcases (scaledLattice_carrier_iff Λ ht.ne' γ).1 hγ with ⟨η, hη, rfl⟩
      refine ⟨‖x - η‖, ⟨η, hη, rfl⟩, ?_⟩
      simp [← smul_sub, norm_smul, Real.norm_of_nonneg ht.le, smul_eq_mul]
    · rintro ⟨r0, ⟨η, hη, rfl⟩, rfl⟩
      refine ⟨t • η, ?_, ?_⟩
      · exact (scaledLattice_carrier_iff Λ ht.ne' (t • η)).2 ⟨η, hη, rfl⟩
      · simp [← smul_sub, norm_smul, Real.norm_of_nonneg ht.le, smul_eq_mul]
  unfold distanceToLattice
  change sInf StΛ = t * sInf SΛ
  rw [hset, Real.sInf_smul_of_nonneg ht.le]
  rfl

private lemma shortestVectorLength_scaled {n : Nat}
    (Λ : KNFullRankLattice n) {t : Real} (ht : 0 < t) :
    shortestVectorLength (⟨scaledLatticeBasis Λ.basis t ht.ne'⟩ : KNFullRankLattice n) =
      t * shortestVectorLength Λ := by
  let tΛ : KNFullRankLattice n := ⟨scaledLatticeBasis Λ.basis t ht.ne'⟩
  let SΛ : Set Real := {r : Real |
    ∃ γ : RealEuclideanSpace n, γ ∈ Λ.carrier ∧ γ ≠ 0 ∧ r = ‖γ‖}
  let StΛ : Set Real := {r : Real |
    ∃ γ : RealEuclideanSpace n, γ ∈ tΛ.carrier ∧ γ ≠ 0 ∧ r = ‖γ‖}
  have hset : StΛ = t • SΛ := by
    ext r
    constructor
    · rintro ⟨γ, hγ, hγne, rfl⟩
      rcases (scaledLattice_carrier_iff Λ ht.ne' γ).1 hγ with ⟨η, hη, rfl⟩
      have hηne : η ≠ 0 := by
        intro hη0
        apply hγne
        simp [hη0]
      refine ⟨‖η‖, ?_, ?_⟩
      · exact ⟨η, hη, hηne, rfl⟩
      · simp [norm_smul, Real.norm_of_nonneg ht.le, smul_eq_mul]
    · rintro ⟨r0, ⟨η, hη, hηne, rfl⟩, rfl⟩
      refine ⟨t • η, ?_, ?_, ?_⟩
      · exact (scaledLattice_carrier_iff Λ ht.ne' (t • η)).2 ⟨η, hη, rfl⟩
      · intro hzero
        apply hηne
        simpa [ht.ne'] using congrArg (fun x : RealEuclideanSpace n => t⁻¹ • x) hzero
      · simp [norm_smul, Real.norm_of_nonneg ht.le, smul_eq_mul]
  unfold shortestVectorLength
  change sInf StΛ = t * sInf SΛ
  rw [hset, Real.sInf_smul_of_nonneg ht.le]
  rfl

private lemma coveringRadius_scaled {n : Nat}
    (Λ : KNFullRankLattice n) {t : Real} (ht : 0 < t) :
    coveringRadius (⟨scaledLatticeBasis Λ.basis t ht.ne'⟩ : KNFullRankLattice n) =
      t * coveringRadius Λ := by
  let tΛ : KNFullRankLattice n := ⟨scaledLatticeBasis Λ.basis t ht.ne'⟩
  have hrange :
      Set.range (distanceToLattice tΛ) = t • Set.range (distanceToLattice Λ) := by
    ext r
    constructor
    · rintro ⟨y, rfl⟩
      let x : RealEuclideanSpace n := t⁻¹ • y
      refine ⟨distanceToLattice Λ x, ⟨x, rfl⟩, ?_⟩
      have hx : t • x = y := by
        simp [x, smul_smul, ht.ne']
      have hscaled := distanceToLattice_scaled Λ ht x
      rw [hx] at hscaled
      simpa [smul_eq_mul] using hscaled.symm
    · rintro ⟨r0, ⟨x, rfl⟩, rfl⟩
      refine ⟨t • x, ?_⟩
      simpa [tΛ, smul_eq_mul] using distanceToLattice_scaled Λ ht x
  unfold coveringRadius
  change sSup (Set.range (distanceToLattice tΛ)) = t * sSup (Set.range (distanceToLattice Λ))
  rw [hrange, Real.sSup_smul_of_nonneg ht.le]
  rfl

private lemma exists_nonzero_lattice_vector {n : Nat}
    (hn : 1 ≤ n) (Λ : KNFullRankLattice n) :
    ∃ γ : RealEuclideanSpace n, γ ∈ Λ.carrier ∧ γ ≠ 0 := by
  let i : Fin n := ⟨0, hn⟩
  let v : RealEuclideanSpace n := integerVector n (intStdBasis i)
  let γ : RealEuclideanSpace n := Matrix.toEuclideanLin Λ.basis.matrix v
  refine ⟨γ, ?_, ?_⟩
  · change γ ∈ matrixIntegerLattice n Λ.basis
    simp [γ, v, matrixIntegerLattice, integerLattice]
  · have hv_ne : v ≠ 0 := by
      intro hv
      have hi := congrArg (fun x : RealEuclideanSpace n => (x : Fin n -> Real) i) hv
      norm_num [v, integerVector, intStdBasis] at hi
    intro hγ
    have hlin :
        matrixLinearEquiv Λ.basis v = Matrix.toEuclideanLin Λ.basis.matrix v := by
      exact congrFun
        (congrArg (fun f : RealEuclideanSpace n →ₗ[Real] RealEuclideanSpace n =>
          (f : RealEuclideanSpace n → RealEuclideanSpace n))
          (matrixLinearEquiv_eq_toEuclideanLin Λ.basis)) v
    apply hv_ne
    have hv_zero : matrixLinearEquiv Λ.basis v = 0 := by
      rwa [hlin]
    have hv_zero' := congrArg (matrixLinearEquiv Λ.basis).symm hv_zero
    simpa using hv_zero'

private lemma lattice_shortest_minimizer {n : Nat}
    (hn : 1 ≤ n) (Λ : KNFullRankLattice n) :
    ∃ γ : RealEuclideanSpace n, γ ∈ Λ.carrier ∧ γ ≠ 0 ∧
      ∀ η : RealEuclideanSpace n, η ∈ Λ.carrier -> η ≠ 0 -> ‖γ‖ ≤ ‖η‖ := by
  classical
  obtain ⟨γ0, hγ0, hγ0ne⟩ := exists_nonzero_lattice_vector hn Λ
  let R : Real := ‖γ0‖
  let S : Set (RealEuclideanSpace n) :=
    {γ | γ ∈ Λ.carrier ∧ γ ≠ 0 ∧ ‖γ‖ ≤ R}
  have hballFinite :
      Set.Finite (Metric.closedBall (0 : RealEuclideanSpace n) R ∩
        (Λ.carrier : Set (RealEuclideanSpace n))) := by
    simpa [KNFullRankLattice.carrier] using
      matrixIntegerLattice_finite_inter_isBounded Λ.basis
        (s := Metric.closedBall (0 : RealEuclideanSpace n) R) Metric.isBounded_closedBall
  have hSfinite : S.Finite := by
    refine hballFinite.subset ?_
    intro y hy
    exact ⟨by simpa [Metric.mem_closedBall, dist_eq_norm] using hy.2.2, hy.1⟩
  have hSnonempty : S.Nonempty := by
    refine ⟨γ0, hγ0, hγ0ne, ?_⟩
    exact le_rfl
  let F := hSfinite.toFinset
  have hFnonempty : F.Nonempty := by
    rcases hSnonempty with ⟨y, hy⟩
    exact ⟨y, by simpa [F] using hy⟩
  obtain ⟨γ, hγF, hγmin⟩ := Finset.exists_min_image F (fun y => ‖y‖) hFnonempty
  have hγS : γ ∈ S := by simpa [F] using hγF
  refine ⟨γ, hγS.1, hγS.2.1, ?_⟩
  intro η hη hηne
  by_cases hηR : ‖η‖ ≤ R
  · exact hγmin η (by simpa [F, S] using ⟨hη, hηne, hηR⟩)
  · have hγ_le_R : ‖γ‖ ≤ R := hγS.2.2
    exact le_trans hγ_le_R (not_le.mp hηR).le

/-- The shortest nonzero vector is positive and attained. -/
theorem shortestVectorLength_pos_attained {n : Nat}
    (hn : 1 ≤ n) (Λ : KNFullRankLattice n) :
    0 < shortestVectorLength Λ ∧
      ∃ γ : RealEuclideanSpace n,
        γ ∈ Λ.carrier ∧ γ ≠ 0 ∧ shortestVectorLength Λ = ‖γ‖ := by
  obtain ⟨γ, hγ, hγne, hmin⟩ := lattice_shortest_minimizer hn Λ
  have hshort : shortestVectorLength Λ = ‖γ‖ := by
    let S := {r : Real |
      ∃ η : RealEuclideanSpace n, η ∈ Λ.carrier ∧ η ≠ 0 ∧ r = ‖η‖}
    have hSnonempty : S.Nonempty := ⟨‖γ‖, ⟨γ, hγ, hγne, rfl⟩⟩
    have hSbdd : BddBelow S := by
      refine ⟨0, ?_⟩
      rintro r ⟨η, _hη, _hηne, rfl⟩
      exact norm_nonneg _
    unfold shortestVectorLength
    change sInf S = ‖γ‖
    apply le_antisymm
    · exact csInf_le hSbdd ⟨γ, hγ, hγne, rfl⟩
    · rw [le_csInf_iff hSbdd hSnonempty]
      rintro r ⟨η, hη, hηne, rfl⟩
      exact hmin η hη hηne
  refine ⟨?_, γ, hγ, hγne, hshort⟩
  simpa [hshort] using norm_pos_iff.mpr hγne

/-- The covering radius is finite and attained. -/
theorem coveringRadius_finite_attained {n : Nat} (Λ : KNFullRankLattice n) :
    0 ≤ coveringRadius Λ ∧
      ∃ x : RealEuclideanSpace n, distanceToLattice Λ x = coveringRadius Λ := by
  have hclosed : IsClosed (Set.range (distanceToLattice Λ)) :=
    (distanceToLattice_range_isCompact Λ).isClosed
  have hmem :
      sSup (Set.range (distanceToLattice Λ)) ∈ Set.range (distanceToLattice Λ) :=
    hclosed.csSup_mem (Set.range_nonempty (distanceToLattice Λ))
      (distanceToLattice_range_bddAbove Λ)
  rcases hmem with ⟨x, hx⟩
  unfold coveringRadius
  refine ⟨?_, x, hx⟩
  rw [← hx]
  exact distanceToLattice_nonneg Λ x

private lemma shortestVectorLength_least {n : Nat}
    (hn : 1 ≤ n) (Λ : KNFullRankLattice n) {a : Real}
    (h : ∀ γ : RealEuclideanSpace n, γ ∈ Λ.carrier -> γ ≠ 0 -> a ≤ ‖γ‖) :
    a ≤ shortestVectorLength Λ := by
  obtain ⟨_hpos, γ, hγ, hγne, hγeq⟩ := shortestVectorLength_pos_attained hn Λ
  rw [hγeq]
  exact h γ hγ hγne

private lemma coveringRadius_le_of_distanceToLattice_le {n : Nat}
    (Λ : KNFullRankLattice n) {R : Real}
    (h : ∀ x : RealEuclideanSpace n, distanceToLattice Λ x ≤ R) :
    coveringRadius Λ ≤ R := by
  obtain ⟨_hnonneg, x, hx⟩ := coveringRadius_finite_attained Λ
  rw [← hx]
  exact h x

private theorem lattice_bounds_of_pointwise_bounds {n : Nat} (hn : 1 ≤ n)
    (Λ : KNFullRankLattice n) {N R : Real}
    (hN : ∀ γ : RealEuclideanSpace n, γ ∈ Λ.carrier -> γ ≠ 0 -> N ≤ ‖γ‖)
    (hR : ∀ x : RealEuclideanSpace n, distanceToLattice Λ x ≤ R) :
    N ≤ shortestVectorLength Λ ∧ coveringRadius Λ ≤ R :=
  ⟨shortestVectorLength_least hn Λ hN, coveringRadius_le_of_distanceToLattice_le Λ hR⟩

/-- The closed Voronoi cell lies in the covering ball. -/
theorem closedVoronoiCell_subset_coveringBall {n : Nat}
    (Λ : KNFullRankLattice n) {x : RealEuclideanSpace n}
    (hx : InClosedVoronoiCell Λ x) :
    ‖x‖ ≤ coveringRadius Λ := by
  rw [← distanceToLattice_eq_norm_of_voronoi Λ hx]
  unfold coveringRadius
  exact le_csSup (distanceToLattice_range_bddAbove Λ) (Set.mem_range_self x)

private lemma shortestVectorLength_le_norm {n : Nat}
    (Λ : KNFullRankLattice n) {γ : RealEuclideanSpace n}
    (hγ : γ ∈ Λ.carrier) (hγne : γ ≠ 0) :
    shortestVectorLength Λ ≤ ‖γ‖ := by
  let S : Set Real := {r : Real |
    ∃ η : RealEuclideanSpace n, η ∈ Λ.carrier ∧ η ≠ 0 ∧ r = ‖η‖}
  have hSbdd : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro r ⟨η, _hη, _hηne, rfl⟩
    exact norm_nonneg _
  unfold shortestVectorLength
  change sInf S ≤ ‖γ‖
  exact csInf_le hSbdd ⟨γ, hγ, hγne, rfl⟩

private noncomputable def dualVectorOfFrequency {n : Nat}
    (Λ : KNFullRankLattice n) (k : Fin n -> Int) : RealEuclideanSpace n :=
  Matrix.toEuclideanLin Λ.basis.matrix⁻¹.transpose (integerVector n k)

private lemma dualVectorOfFrequency_eq_matrixLinearEquiv {n : Nat}
    (Λ : KNFullRankLattice n) (k : Fin n -> Int) :
    dualVectorOfFrequency Λ k =
      matrixLinearEquiv (dualLatticeBasis Λ.basis) (integerVector n k) := by
  dsimp [dualVectorOfFrequency, dualLatticeBasis]
  exact (congrFun
    (congrArg (fun f : RealEuclideanSpace n →ₗ[Real] RealEuclideanSpace n =>
      (f : RealEuclideanSpace n → RealEuclideanSpace n))
      (matrixLinearEquiv_eq_toEuclideanLin (dualLatticeBasis Λ.basis)))
    (integerVector n k)).symm

private lemma dualVectorOfFrequency_mem {n : Nat}
    (Λ : KNFullRankLattice n) (k : Fin n -> Int) :
    dualVectorOfFrequency Λ k ∈ (knDualLattice Λ).carrier := by
  change dualVectorOfFrequency Λ k ∈ matrixIntegerLattice n (dualLatticeBasis Λ.basis)
  simp [dualVectorOfFrequency, matrixIntegerLattice, integerLattice, dualLatticeBasis]

private lemma dualVectorOfFrequency_eq_zero_iff {n : Nat}
    (Λ : KNFullRankLattice n) (k : Fin n -> Int) :
    dualVectorOfFrequency Λ k = 0 ↔ k = 0 := by
  constructor
  · intro hzero
    have hvec : integerVector n k = 0 := by
      apply (matrixLinearEquiv (dualLatticeBasis Λ.basis)).injective
      rw [← dualVectorOfFrequency_eq_matrixLinearEquiv Λ k, hzero]
      simp
    funext i
    have hi := congrArg (fun x : RealEuclideanSpace n => (x : Fin n -> Real) i) hvec
    norm_num [integerVector] at hi
    exact Int.cast_eq_zero.mp hi
  · intro hk
    have hzeroVec : integerVector n (0 : Fin n -> Int) = 0 := by
      ext i
      simp [integerVector]
    rw [dualVectorOfFrequency_eq_matrixLinearEquiv, hk]
    rw [hzeroVec]
    simp

private lemma dualVectorOfFrequency_ne_zero {n : Nat}
    (Λ : KNFullRankLattice n) {k : Fin n -> Int} (hk : k ≠ 0) :
    dualVectorOfFrequency Λ k ≠ 0 := by
  intro hzero
  exact hk ((dualVectorOfFrequency_eq_zero_iff Λ k).1 hzero)

private lemma shortestVectorLength_le_norm_dualVectorOfFrequency {n : Nat}
    (Λ : KNFullRankLattice n) {k : Fin n -> Int} (hk : k ≠ 0) :
    shortestVectorLength (knDualLattice Λ) ≤ ‖dualVectorOfFrequency Λ k‖ :=
  shortestVectorLength_le_norm (knDualLattice Λ) (dualVectorOfFrequency_mem Λ k)
    (dualVectorOfFrequency_ne_zero Λ hk)

private lemma inner_integerVector_coordinateVectorForPhysicalDirection_eq_dualVector
    {n : Nat} (Λ : KNFullRankLattice n) (k : Fin n -> Int) (j : Fin n) :
    inner Real (integerVector n k) (coordinateVectorForPhysicalDirection Λ.basis j) =
      inner Real (dualVectorOfFrequency Λ k) (euclideanStdBasis n j) := by
  simpa [dualVectorOfFrequency] using
    inner_integerVector_coordinateVectorForPhysicalDirection Λ.basis k j

private lemma unitAddTorus_mFourier_physicalDirection
    {n : Nat} (Λ : KNFullRankLattice n) (k : Fin n -> Int) (j : Fin n) (t : Real) :
    UnitAddTorus.mFourier k
        (euclideanToUnitAddTorus n (t • coordinateVectorForPhysicalDirection Λ.basis j)) =
      Complex.exp
        (2 * Real.pi * Complex.I *
          ((t * inner Real (dualVectorOfFrequency Λ k) (euclideanStdBasis n j) : Real) :
            Complex)) := by
  rw [unitAddTorus_mFourier_euclideanToUnitAddTorus]
  congr 1
  have hsum :
      (∑ i : Fin n,
          (k i : Real) * (t • coordinateVectorForPhysicalDirection Λ.basis j) i) =
        t * inner Real (integerVector n k)
          (coordinateVectorForPhysicalDirection Λ.basis j) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [integerVector]
    simp [dotProduct, Finset.mul_sum, mul_left_comm, mul_comm]
  rw [hsum, inner_integerVector_coordinateVectorForPhysicalDirection_eq_dualVector]

private lemma dualVectorOfFrequency_coordinate_sq_sum {n : Nat}
    (Λ : KNFullRankLattice n) (k : Fin n -> Int) :
    (∑ j : Fin n,
      inner Real (dualVectorOfFrequency Λ k) (euclideanStdBasis n j) ^ 2) =
      ‖dualVectorOfFrequency Λ k‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  congr 1
  simp [euclideanStdBasis, PiLp.inner_apply]

private lemma four_pi_sq_dualVector_norm_sq_eq_coordinate_sum {n : Nat}
    (Λ : KNFullRankLattice n) (k : Fin n -> Int) :
    4 * Real.pi ^ 2 * ‖dualVectorOfFrequency Λ k‖ ^ 2 =
      ∑ j : Fin n,
        4 * Real.pi ^ 2 *
          inner Real (dualVectorOfFrequency Λ k) (euclideanStdBasis n j) ^ 2 := by
  rw [← dualVectorOfFrequency_coordinate_sq_sum Λ k]
  rw [Finset.mul_sum]

private lemma complex_exp_sub_one_sq_div_tendsto
    (alpha : Real) :
    Filter.Tendsto
      (fun t : Real =>
        ‖Complex.exp
          (2 * Real.pi * Complex.I * ((t * alpha : Real) : Complex)) - 1‖ ^ 2 /
          t ^ 2)
      (𝓝[≠] (0 : Real))
      (𝓝 (4 * Real.pi ^ 2 * alpha ^ 2)) := by
  let c : Complex := 2 * Real.pi * Complex.I * (alpha : Complex)
  let f : Real -> Complex := fun t => Complex.exp (c * (t : Complex))
  have hfderiv : HasDerivAt f c 0 := by
    have hlin : HasDerivAt (fun t : Real => c * (t : Complex)) c 0 := by
      have hcomplex : HasDerivAt (fun z : Complex => c * z) c (0 : Complex) := by
        simpa using ((hasDerivAt_id (0 : Complex)).const_mul c)
      simpa using hcomplex.comp_ofReal
    have hexp :
        HasDerivAt (fun z : Complex => Complex.exp z)
          (Complex.exp (c * (0 : Complex))) (c * (0 : Complex)) := by
      simpa using Complex.hasDerivAt_exp (c * (0 : Complex))
    simpa [f] using hexp.comp (0 : Real) hlin
  have hslope : Filter.Tendsto (slope f 0) (𝓝[≠] (0 : Real)) (𝓝 c) :=
    hfderiv.tendsto_slope
  have hlim :
      Filter.Tendsto (fun t : Real => ‖slope f 0 t‖ ^ 2)
        (𝓝[≠] (0 : Real)) (𝓝 (‖c‖ ^ 2)) := by
    exact hslope.norm.pow 2
  have hc_norm : ‖c‖ ^ 2 = 4 * Real.pi ^ 2 * alpha ^ 2 := by
    simp only [c, Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_I, mul_one]
    rw [mul_pow, mul_pow, sq_abs alpha, abs_of_pos Real.pi_pos]
    ring
  refine (hlim.congr' ?_).trans ?_
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t ≠ 0 := by simpa using ht
    simp [f, c, slope_def_module, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, sq]
    have hsq : |t| ^ 2 = t ^ 2 := by rw [sq_abs]
    field_simp [ht', abs_ne_zero.mpr ht']
    rw [hsq]
    ring
  · rw [hc_norm]

private lemma finite_summed_multiplier_limit
    {n : Nat} (Λ : KNFullRankLattice n)
    (F : Finset (Fin n -> Int)) :
    Filter.Tendsto
      (fun t : Real =>
        ∑ k ∈ F, ∑ j : Fin n,
          ‖Complex.exp
            (2 * Real.pi * Complex.I *
              ((t * inner Real (dualVectorOfFrequency Λ k)
                (euclideanStdBasis n j) : Real) : Complex)) - 1‖ ^ 2 / t ^ 2)
      (𝓝[≠] (0 : Real))
      (𝓝 (∑ k ∈ F,
        4 * Real.pi ^ 2 * ‖dualVectorOfFrequency Λ k‖ ^ 2)) := by
  have hsum :
      Filter.Tendsto
        (fun t : Real =>
          ∑ k ∈ F, ∑ j : Fin n,
            ‖Complex.exp
              (2 * Real.pi * Complex.I *
                ((t * inner Real (dualVectorOfFrequency Λ k)
                  (euclideanStdBasis n j) : Real) : Complex)) - 1‖ ^ 2 / t ^ 2)
        (𝓝[≠] (0 : Real))
        (𝓝 (∑ k ∈ F, ∑ j : Fin n,
          4 * Real.pi ^ 2 *
            inner Real (dualVectorOfFrequency Λ k) (euclideanStdBasis n j) ^ 2)) := by
    exact tendsto_finsetSum F (fun k _hk => by
      simpa using
        tendsto_finsetSum (Finset.univ : Finset (Fin n)) (fun j _hj =>
          complex_exp_sub_one_sq_div_tendsto
            (inner Real (dualVectorOfFrequency Λ k) (euclideanStdBasis n j))))
  refine hsum.trans ?_
  have htarget :
      (∑ k ∈ F, ∑ j : Fin n,
          4 * Real.pi ^ 2 *
            inner Real (dualVectorOfFrequency Λ k) (euclideanStdBasis n j) ^ 2) =
        ∑ k ∈ F, 4 * Real.pi ^ 2 * ‖dualVectorOfFrequency Λ k‖ ^ 2 := by
    refine Finset.sum_congr rfl ?_
    intro k _hk
    exact (four_pi_sq_dualVector_norm_sq_eq_coordinate_sum Λ k).symm
  rw [htarget]

private lemma four_pi_sq_shortest_sq_le_dualVector_frequency_weight {n : Nat}
    (hn : 1 ≤ n) (Λ : KNFullRankLattice n) {k : Fin n -> Int} (hk : k ≠ 0) :
    4 * Real.pi ^ 2 * shortestVectorLength (knDualLattice Λ) ^ 2 ≤
      4 * Real.pi ^ 2 * ‖dualVectorOfFrequency Λ k‖ ^ 2 := by
  have hle := shortestVectorLength_le_norm_dualVectorOfFrequency Λ hk
  have hNnonneg : 0 ≤ shortestVectorLength (knDualLattice Λ) :=
    (shortestVectorLength_pos_attained hn (knDualLattice Λ)).1.le
  have hnorm_nonneg : 0 ≤ ‖dualVectorOfFrequency Λ k‖ := norm_nonneg _
  have hsq :
      shortestVectorLength (knDualLattice Λ) ^ 2 ≤
        ‖dualVectorOfFrequency Λ k‖ ^ 2 := by
    have hdiff :
        0 ≤ ‖dualVectorOfFrequency Λ k‖ - shortestVectorLength (knDualLattice Λ) :=
      sub_nonneg.mpr hle
    have hsum :
        0 ≤ ‖dualVectorOfFrequency Λ k‖ + shortestVectorLength (knDualLattice Λ) :=
      add_nonneg hnorm_nonneg hNnonneg
    nlinarith [mul_nonneg hdiff hsum]
  exact mul_le_mul_of_nonneg_left hsq (by positivity)

private lemma finset_sum_shortest_weighted_le_dualVector_weighted {n : Nat}
    (hn : 1 ≤ n) (Λ : KNFullRankLattice n) (F : Finset (Fin n -> Int))
    (a : (Fin n -> Int) -> Real) (ha : ∀ k, 0 ≤ a k)
    (hF : ∀ k ∈ F, k ≠ 0) :
    (∑ k ∈ F, (4 * Real.pi ^ 2 * shortestVectorLength (knDualLattice Λ) ^ 2) * a k) ≤
      ∑ k ∈ F, (4 * Real.pi ^ 2 * ‖dualVectorOfFrequency Λ k‖ ^ 2) * a k := by
  refine Finset.sum_le_sum ?_
  intro k hk
  exact mul_le_mul_of_nonneg_right
    (four_pi_sq_shortest_sq_le_dualVector_frequency_weight hn Λ (hF k hk)) (ha k)

private lemma hilbertBasis_finset_sum_repr_norm_sq_le
    {ι : Type*} {H : Type v} [NormedAddCommGroup H] [InnerProductSpace Real H]
    [CompleteSpace H] (b : HilbertBasis ι Real H) (s : Finset ι) (v : H) :
    (∑ i ∈ s, ‖b.repr v i‖ ^ 2) ≤ ‖v‖ ^ 2 := by
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  have hsum := lp.hasSum_norm (E := fun _ : ι => Real) hp (b.repr v)
  have hle := sum_le_hasSum s (fun _ _ => by positivity) hsum
  simpa using hle

private lemma half_shortestVectorLength_le_coveringRadius {n : Nat}
    (hn : 1 ≤ n) (Λ : KNFullRankLattice n) :
    (1 / 2 : Real) * shortestVectorLength Λ ≤ coveringRadius Λ := by
  obtain ⟨_hNpos, γ, hγ, hγne, hshort⟩ :=
    shortestVectorLength_pos_attained hn Λ
  let x : RealEuclideanSpace n := (1 / 2 : Real) • γ
  have hxnorm : ‖x‖ = (1 / 2 : Real) * ‖γ‖ := by
    simp [x, norm_smul]
  have hx : InClosedVoronoiCell Λ x := by
    intro η hη
    let δ : RealEuclideanSpace n := γ - (η + η)
    have hδmem : δ ∈ Λ.carrier :=
      Λ.carrier.sub_mem hγ (Λ.carrier.add_mem hη hη)
    have hδne : δ ≠ 0 := by
      intro hδ
      have hγeq : γ = η + η := by
        change γ - (η + η) = 0 at hδ
        exact sub_eq_zero.mp hδ
      have hηne : η ≠ 0 := by
        intro hη0
        apply hγne
        simpa [hη0] using hγeq
      have hηlower : ‖γ‖ ≤ ‖η‖ := by
        have hle := shortestVectorLength_le_norm Λ hη hηne
        simpa [hshort] using hle
      have hγnorm : ‖γ‖ = 2 * ‖η‖ := by
        calc
          ‖γ‖ = ‖η + η‖ := by rw [hγeq]
          _ = ‖(2 : Real) • η‖ := by simp [two_smul]
          _ = 2 * ‖η‖ := by
                simp [norm_smul]
      have hγpos : 0 < ‖γ‖ := norm_pos_iff.mpr hγne
      nlinarith
    have hδlower : ‖γ‖ ≤ ‖δ‖ := by
      have hle := shortestVectorLength_le_norm Λ hδmem hδne
      simpa [hshort] using hle
    have hxη : x - η = (1 / 2 : Real) • δ := by
      dsimp [x, δ]
      module
    have hxηnorm : ‖x - η‖ = (1 / 2 : Real) * ‖δ‖ := by
      rw [hxη, norm_smul,
        Real.norm_of_nonneg (by norm_num : (0 : Real) ≤ (1 / 2 : Real))]
    rw [hxnorm, hxηnorm]
    exact mul_le_mul_of_nonneg_left hδlower
      (by norm_num : (0 : Real) ≤ (1 / 2 : Real))
  calc
    (1 / 2 : Real) * shortestVectorLength Λ = ‖x‖ := by
      rw [hshort, hxnorm]
    _ ≤ coveringRadius Λ := closedVoronoiCell_subset_coveringBall Λ hx

private lemma coveringRadius_pos {n : Nat}
    (hn : 1 ≤ n) (Λ : KNFullRankLattice n) :
    0 < coveringRadius Λ := by
  obtain ⟨hshort_pos, _γ, _hγ, _hγne, _hshort⟩ :=
    shortestVectorLength_pos_attained hn Λ
  have hhalf := half_shortestVectorLength_le_coveringRadius hn Λ
  have hhalf_pos : 0 < (1 / 2 : Real) * shortestVectorLength Λ := by
    positivity
  exact lt_of_lt_of_le hhalf_pos hhalf

/-- Scaling law for shortest vector length. -/
theorem shortestVectorLength_smul {n : Nat}
    (Λ : KNFullRankLattice n) {t : Real} (ht : 0 < t) :
    ∃ tΛ : KNFullRankLattice n, shortestVectorLength tΛ = t * shortestVectorLength Λ := by
  let tΛ : KNFullRankLattice n := ⟨scaledLatticeBasis Λ.basis t ht.ne'⟩
  refine ⟨tΛ, ?_⟩
  let SΛ : Set Real := {r : Real |
    ∃ γ : RealEuclideanSpace n, γ ∈ Λ.carrier ∧ γ ≠ 0 ∧ r = ‖γ‖}
  let StΛ : Set Real := {r : Real |
    ∃ γ : RealEuclideanSpace n, γ ∈ tΛ.carrier ∧ γ ≠ 0 ∧ r = ‖γ‖}
  have hset : StΛ = t • SΛ := by
    ext r
    constructor
    · rintro ⟨γ, hγ, hγne, rfl⟩
      rcases (scaledLattice_carrier_iff Λ ht.ne' γ).1 hγ with ⟨η, hη, rfl⟩
      have hηne : η ≠ 0 := by
        intro hη0
        apply hγne
        simp [hη0]
      refine ⟨‖η‖, ?_, ?_⟩
      · exact ⟨η, hη, hηne, rfl⟩
      · simp [norm_smul, Real.norm_of_nonneg ht.le, smul_eq_mul]
    · rintro ⟨r0, ⟨η, hη, hηne, rfl⟩, rfl⟩
      refine ⟨t • η, ?_, ?_, ?_⟩
      · exact (scaledLattice_carrier_iff Λ ht.ne' (t • η)).2 ⟨η, hη, rfl⟩
      · intro hzero
        apply hηne
        simpa [ht.ne'] using congrArg (fun x : RealEuclideanSpace n => t⁻¹ • x) hzero
      · simp [norm_smul, Real.norm_of_nonneg ht.le, smul_eq_mul]
  unfold shortestVectorLength
  change sInf StΛ = t * sInf SΛ
  rw [hset, Real.sInf_smul_of_nonneg ht.le]
  rfl

/-- Scaling law for covering radius. -/
theorem coveringRadius_smul {n : Nat}
    (Λ : KNFullRankLattice n) {t : Real} (ht : 0 < t) :
    ∃ tΛ : KNFullRankLattice n, coveringRadius tΛ = t * coveringRadius Λ := by
  let tΛ : KNFullRankLattice n := ⟨scaledLatticeBasis Λ.basis t ht.ne'⟩
  refine ⟨tΛ, ?_⟩
  have hrange :
      Set.range (distanceToLattice tΛ) = t • Set.range (distanceToLattice Λ) := by
    ext r
    constructor
    · rintro ⟨y, rfl⟩
      let x : RealEuclideanSpace n := t⁻¹ • y
      refine ⟨distanceToLattice Λ x, ⟨x, rfl⟩, ?_⟩
      have hx : t • x = y := by
        simp [x, smul_smul, ht.ne']
      have hscaled := distanceToLattice_scaled Λ ht x
      rw [hx] at hscaled
      simpa [smul_eq_mul] using hscaled.symm
    · rintro ⟨r0, ⟨x, rfl⟩, rfl⟩
      refine ⟨t • x, ?_⟩
      simpa [tΛ, smul_eq_mul] using distanceToLattice_scaled Λ ht x
  unfold coveringRadius
  change sSup (Set.range (distanceToLattice tΛ)) = t * sSup (Set.range (distanceToLattice Λ))
  rw [hrange, Real.sSup_smul_of_nonneg ht.le]
  rfl

/-- The constant `a₀ = 7/8 * (1 / (16πe))^2` from the average-distance estimate. -/
noncomputable def khotNaorAverageDistanceConstant : Real :=
  (7 / 8 : Real) * (1 / (16 * Real.pi * Real.exp 1)) ^ 2

/-- Positivity of the average-distance constant. -/
theorem khotNaorAverageDistanceConstant_pos :
    0 < khotNaorAverageDistanceConstant := by
  unfold khotNaorAverageDistanceConstant
  positivity

/-- The analytic Khot--Naor constant `b₀ = sqrt 7 / (32e)`. -/
noncomputable def khotNaorAnalyticConstant : Real :=
  Real.sqrt 7 / (32 * Real.exp 1)

/-- Positivity of the analytic Khot--Naor constant. -/
theorem khotNaorAnalyticConstant_pos :
    0 < khotNaorAnalyticConstant := by
  unfold khotNaorAnalyticConstant
  positivity

private lemma khotNaorAnalyticConstant_sq :
    khotNaorAnalyticConstant ^ 2 =
      2 * Real.pi ^ 2 * khotNaorAverageDistanceConstant := by
  unfold khotNaorAnalyticConstant khotNaorAverageDistanceConstant
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : Real) ≤ 7)]
  field_simp [Real.exp_ne_zero, Real.pi_ne_zero]
  ring

private theorem dualLattice_distortion_witness_lower_of_energy_bounds
    {n : Nat} (hn : 1 ≤ n) {N R scale D E : Real}
    (hN : 0 < N) (hR : 0 < R) (hscale : 0 < scale) (hD : 1 ≤ D)
    (hLower :
      scale ^ 2 * (khotNaorAverageDistanceConstant * (n : Real) ^ 2 / R ^ 2) ≤ E)
    (hUpper : E ≤ (n : Real) * (D * scale) ^ 2 / (2 * Real.pi ^ 2 * N ^ 2)) :
    khotNaorAnalyticConstant * (N / R) * Real.sqrt (n : Real) ≤ D := by
  have hnpos : 0 < (n : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hcomb :
      scale ^ 2 * (khotNaorAverageDistanceConstant * (n : Real) ^ 2 / R ^ 2) ≤
        (n : Real) * (D * scale) ^ 2 / (2 * Real.pi ^ 2 * N ^ 2) :=
    le_trans hLower hUpper
  have hsq :
      (khotNaorAnalyticConstant * (N / R) * Real.sqrt (n : Real)) ^ 2 ≤ D ^ 2 := by
    rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt hnpos.le, khotNaorAnalyticConstant_sq]
    have hpi2pos : 0 < 2 * Real.pi ^ 2 * N ^ 2 := by positivity
    have hRsqpos : 0 < R ^ 2 := sq_pos_of_ne_zero hR.ne'
    have hscalesqpos : 0 < scale ^ 2 := sq_pos_of_ne_zero hscale.ne'
    field_simp [hpi2pos.ne', hRsqpos.ne', hscalesqpos.ne'] at hcomb ⊢
    nlinarith [hcomb, hN]
  exact le_of_sq_le_sq hsq hDpos.le

private lemma dual_shortestVectorLength_pos {n : Nat}
    (hn : 1 ≤ n) (Λ : KNFullRankLattice n) :
    0 < shortestVectorLength (knDualLattice Λ) :=
  (shortestVectorLength_pos_attained hn (knDualLattice Λ)).1

private lemma dual_coveringRadius_pos {n : Nat}
    (hn : 1 ≤ n) (Λ : KNFullRankLattice n) :
    0 < coveringRadius (knDualLattice Λ) :=
  coveringRadius_pos hn (knDualLattice Λ)

private theorem dualLattice_distortion_witness_lower_of_dual_energy_bounds
    {n : Nat} (hn : 1 ≤ n) (Λ : KNFullRankLattice n) {scale D E : Real}
    (hscale : 0 < scale) (hD : 1 ≤ D)
    (hLower :
      scale ^ 2 *
          (khotNaorAverageDistanceConstant * (n : Real) ^ 2 /
            coveringRadius (knDualLattice Λ) ^ 2) ≤ E)
    (hUpper :
      E ≤
        (n : Real) * (D * scale) ^ 2 /
          (2 * Real.pi ^ 2 * shortestVectorLength (knDualLattice Λ) ^ 2)) :
    khotNaorAnalyticConstant *
        (shortestVectorLength (knDualLattice Λ) /
          coveringRadius (knDualLattice Λ)) *
        Real.sqrt (n : Real) ≤ D := by
  exact dualLattice_distortion_witness_lower_of_energy_bounds (n := n) hn
    (N := shortestVectorLength (knDualLattice Λ))
    (R := coveringRadius (knDualLattice Λ)) (scale := scale) (D := D) (E := E)
    (dual_shortestVectorLength_pos hn Λ) (dual_coveringRadius_pos hn Λ)
    hscale hD hLower hUpper

private lemma one_le_hilbertDistortion_local
    {X : Type u} [PseudoMetricSpace X] : (1 : ENNReal) ≤ hilbertDistortion.{u, v} X := by
  unfold hilbertDistortion
  refine le_sInf ?_
  intro D hD
  exact hD.1

private lemma ofReal_le_hilbertDistortion_of_le_one
    {X : Type u} [PseudoMetricSpace X] {K : Real} (hK : K ≤ 1) :
    ENNReal.ofReal K ≤ hilbertDistortion.{u, v} X := by
  calc
    ENNReal.ofReal K ≤ (1 : ENNReal) := by
      simpa using ENNReal.ofReal_le_one.mpr hK
    _ ≤ hilbertDistortion.{u, v} X := one_le_hilbertDistortion_local

private lemma dualLatticeHilbertLowerBound_of_prefactor_le_one {n : Nat}
    (Λ : KNFullRankLattice n)
    (hK :
      khotNaorAnalyticConstant *
          (shortestVectorLength (knDualLattice Λ) / coveringRadius (knDualLattice Λ)) *
        Real.sqrt (n : Real) ≤ 1) :
    ENNReal.ofReal
        (khotNaorAnalyticConstant *
          (shortestVectorLength (knDualLattice Λ) / coveringRadius (knDualLattice Λ)) *
            Real.sqrt (n : Real)) ≤
      (letI : PseudoMetricSpace Λ.torus := Λ.torusMetric;
        hilbertDistortion Λ.torus) := by
  letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
  exact ofReal_le_hilbertDistortion_of_le_one hK

private lemma dualLatticeHilbertLowerBound_of_distortion_witnesses {n : Nat}
    (Λ : KNFullRankLattice n)
    (hLower : ∀ D : ENNReal,
      (letI : PseudoMetricSpace Λ.torus := Λ.torusMetric;
        hilbertDistortion.{0, v} Λ.torus) ≤ D ->
      ENNReal.ofReal
          (khotNaorAnalyticConstant *
            (shortestVectorLength (knDualLattice Λ) / coveringRadius (knDualLattice Λ)) *
              Real.sqrt (n : Real)) ≤ D) :
    ENNReal.ofReal
        (khotNaorAnalyticConstant *
          (shortestVectorLength (knDualLattice Λ) / coveringRadius (knDualLattice Λ)) *
            Real.sqrt (n : Real)) ≤
      (letI : PseudoMetricSpace Λ.torus := Λ.torusMetric;
        hilbertDistortion.{0, v} Λ.torus) := by
  have hle :
      (letI : PseudoMetricSpace Λ.torus := Λ.torusMetric;
        hilbertDistortion.{0, v} Λ.torus) ≤
      (letI : PseudoMetricSpace Λ.torus := Λ.torusMetric;
        hilbertDistortion.{0, v} Λ.torus) := le_rfl
  exact hLower
    (letI : PseudoMetricSpace Λ.torus := Λ.torusMetric;
      hilbertDistortion.{0, v} Λ.torus) hle

private lemma lipschitzWith_of_distortion_upper
    {n : Nat} (Λ : KNFullRankLattice n)
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
    (f : Λ.torus -> H) {scale D : Real} (hscale : 0 < scale) (hD : 1 ≤ D)
    (hupper :
      letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
      ∀ x y : Λ.torus, ‖f x - f y‖ ≤ D * (scale * dist x y)) :
    letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
    LipschitzWith ⟨D * scale, mul_nonneg (le_trans zero_le_one hD) hscale.le⟩ f := by
  letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  calc
    dist (f x) (f y) = ‖f x - f y‖ := dist_eq_norm _ _
    _ ≤ D * (scale * dist x y) := hupper x y
    _ = (D * scale) * dist x y := by ring

private lemma continuous_of_distortion_upper
    {n : Nat} (Λ : KNFullRankLattice n)
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
    (f : Λ.torus -> H) {scale D : Real} (hscale : 0 < scale) (hD : 1 ≤ D)
    (hupper :
      letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
      ∀ x y : Λ.torus, ‖f x - f y‖ ≤ D * (scale * dist x y)) :
    letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
    Continuous f := by
  letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
  exact (lipschitzWith_of_distortion_upper Λ f hscale hD hupper).continuous

private lemma lipschitzWith_of_flatTorus_lipschitz_bound
    {n : Nat} (Λ : KNFullRankLattice n)
    {H : Type v} [NormedAddCommGroup H] (f : Λ.torus -> H) {L : Real} (hL : 0 ≤ L)
    (hfLip :
      letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
      ∀ x y : Λ.torus, ‖f x - f y‖ ≤ L * dist x y) :
    letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
    LipschitzWith ⟨L, hL⟩ f := by
  letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  calc
    dist (f x) (f y) = ‖f x - f y‖ := dist_eq_norm _ _
    _ ≤ L * dist x y := hfLip x y

private lemma continuous_of_flatTorus_lipschitz_bound
    {n : Nat} (Λ : KNFullRankLattice n)
    {H : Type v} [NormedAddCommGroup H] (f : Λ.torus -> H) {L : Real} (hL : 0 ≤ L)
    (hfLip :
      letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
      ∀ x y : Λ.torus, ‖f x - f y‖ ≤ L * dist x y) :
    letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
    Continuous f := by
  letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
  exact (lipschitzWith_of_flatTorus_lipschitz_bound Λ f hL hfLip).continuous

private lemma continuous_energy_integrand_of_distortion_upper
    {n : Nat} (Λ : KNFullRankLattice n)
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
    (f : Λ.torus -> H) {scale D : Real} (hscale : 0 < scale) (hD : 1 ≤ D)
    (hupper :
      letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
      ∀ x y : Λ.torus, ‖f x - f y‖ ≤ D * (scale * dist x y)) :
    letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
    Continuous (fun p : Λ.torus × Λ.torus => ‖f p.1 - f p.2‖ ^ 2) := by
  letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
  have hf : Continuous f := continuous_of_distortion_upper Λ f hscale hD hupper
  fun_prop

private lemma continuous_dist_sq_integrand {n : Nat} (Λ : KNFullRankLattice n) :
    letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
    Continuous (fun p : Λ.torus × Λ.torus => dist p.1 p.2 ^ 2) := by
  letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
  fun_prop

private lemma distortion_lower_sq_pointwise
    {n : Nat} (Λ : KNFullRankLattice n)
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
    (f : Λ.torus -> H) {scale : Real} (hscale : 0 < scale)
    (hlower :
      letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
      ∀ x y : Λ.torus, scale * dist x y ≤ ‖f x - f y‖)
    (x y : Λ.torus) :
    letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
    (scale * dist x y) ^ 2 ≤ ‖f x - f y‖ ^ 2 := by
  letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
  have hle := hlower x y
  have hleft_nonneg : 0 ≤ scale * dist x y := mul_nonneg hscale.le dist_nonneg
  have hright_nonneg : 0 ≤ ‖f x - f y‖ := norm_nonneg _
  have hdiff : 0 ≤ ‖f x - f y‖ - scale * dist x y := sub_nonneg.mpr hle
  have hsum : 0 ≤ ‖f x - f y‖ + scale * dist x y :=
    add_nonneg hright_nonneg hleft_nonneg
  nlinarith [mul_nonneg hdiff hsum]

private lemma distortion_upper_sq_pointwise
    {n : Nat} (Λ : KNFullRankLattice n)
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
    (f : Λ.torus -> H) {scale D : Real} (hscale : 0 < scale) (hD : 1 ≤ D)
    (hupper :
      letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
      ∀ x y : Λ.torus, ‖f x - f y‖ ≤ D * (scale * dist x y))
    (x y : Λ.torus) :
    letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
    ‖f x - f y‖ ^ 2 ≤ (D * (scale * dist x y)) ^ 2 := by
  letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
  have hle := hupper x y
  have hleft_nonneg : 0 ≤ ‖f x - f y‖ := norm_nonneg _
  have hright_nonneg : 0 ≤ D * (scale * dist x y) :=
    mul_nonneg (le_trans zero_le_one hD) (mul_nonneg hscale.le dist_nonneg)
  have hdiff : 0 ≤ D * (scale * dist x y) - ‖f x - f y‖ := sub_nonneg.mpr hle
  have hsum : 0 ≤ D * (scale * dist x y) + ‖f x - f y‖ :=
    add_nonneg hright_nonneg hleft_nonneg
  nlinarith [mul_nonneg hdiff hsum]

private lemma integral_integral_mono_of_integrable
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ] {f g : X -> X -> Real}
    (hf : Integrable (Function.uncurry f) (μ.prod μ))
    (hg : Integrable (Function.uncurry g) (μ.prod μ))
    (hfg : ∀ x y, f x y ≤ g x y) :
    (∫ x, ∫ y, f x y ∂μ ∂μ) ≤ ∫ x, ∫ y, g x y ∂μ ∂μ := by
  rw [MeasureTheory.integral_integral hf, MeasureTheory.integral_integral hg]
  exact MeasureTheory.integral_mono hf hg (fun p => hfg p.1 p.2)

private lemma integral_integral_const_mul
    {X : Type*} [MeasurableSpace X] {μ : Measure X} (c : Real) (φ : X -> X -> Real) :
    (∫ x, ∫ y, c * φ x y ∂μ ∂μ) = c * ∫ x, ∫ y, φ x y ∂μ ∂μ := by
  simp_rw [MeasureTheory.integral_const_mul]

private lemma integrable_of_continuous_compactSpace
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {g : X -> Real} (hg : Continuous g) :
    Integrable g μ := by
  exact hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)

private lemma integrable_of_continuous_compactSpace_of_borel
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    (hB : BorelSpace X) {μ : Measure X} (hμ : IsFiniteMeasure μ) {g : X -> Real}
    (hg : Continuous g) :
    Integrable g μ := by
  letI : BorelSpace X := hB
  letI : IsFiniteMeasure μ := hμ
  exact integrable_of_continuous_compactSpace (μ := μ) hg

private lemma integrable_prod_of_continuous_compactSpace
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [BorelSpace (X × X)] {μ : Measure X} [IsFiniteMeasure μ]
    {g : X × X -> Real} (hg : Continuous g) :
    Integrable g (μ.prod μ) := by
  exact integrable_of_continuous_compactSpace (X := X × X) (μ := μ.prod μ) hg

private lemma integrable_dist_sq_of_compactSpace
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [BorelSpace (X × X)] {μ : Measure X} [IsFiniteMeasure μ] :
    Integrable (Function.uncurry fun x y : X => dist x y ^ 2) (μ.prod μ) := by
  exact integrable_prod_of_continuous_compactSpace (μ := μ) (by fun_prop)

private lemma integrable_scaled_dist_sq_of_compactSpace
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [BorelSpace (X × X)] {μ : Measure X} [IsFiniteMeasure μ] (scale : Real) :
    Integrable (Function.uncurry fun x y : X => (scale * dist x y) ^ 2) (μ.prod μ) := by
  exact integrable_prod_of_continuous_compactSpace (μ := μ) (by fun_prop)

private lemma integrable_energy_sq_of_continuous_compactSpace
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [BorelSpace (X × X)] {μ : Measure X} [IsFiniteMeasure μ]
    {H : Type*} [NormedAddCommGroup H] {f : X -> H} (hf : Continuous f) :
    Integrable (Function.uncurry fun x y : X => ‖f x - f y‖ ^ 2) (μ.prod μ) := by
  exact integrable_prod_of_continuous_compactSpace (μ := μ) (by
    change Continuous (fun p : X × X => ‖f p.1 - f p.2‖ ^ 2)
    fun_prop)

private lemma flatTorus_lipschitz_energy_integrable
    {n : Nat} (Λ : KNFullRankLattice n)
    {H : Type v} [NormedAddCommGroup H] (f : Λ.torus -> H) {L : Real} (hL : 0 ≤ L)
    (hfLip :
      letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
      ∀ x y : Λ.torus, ‖f x - f y‖ ≤ L * dist x y) :
    letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
    letI : MeasurableSpace Λ.torus := borel Λ.torus
    Integrable
      (Function.uncurry fun x y : Λ.torus => ‖f x - f y‖ ^ 2)
      ((torusHaarMeasure Λ).prod (torusHaarMeasure Λ)) := by
  letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
  letI : MeasurableSpace Λ.torus := borel Λ.torus
  haveI : CompactSpace Λ.torus := flatTorusMetric_compactSpace Λ.basis
  haveI : SecondCountableTopology Λ.torus := flatTorusMetric_secondCountableTopology Λ.basis
  haveI : BorelSpace Λ.torus := ⟨rfl⟩
  haveI : BorelSpace (Λ.torus × Λ.torus) := by infer_instance
  haveI : MeasureTheory.IsProbabilityMeasure (torusHaarMeasure Λ) :=
    torusHaarMeasure_isProbability Λ
  have hFinProd : IsFiniteMeasure ((torusHaarMeasure Λ).prod (torusHaarMeasure Λ)) := by
    infer_instance
  letI : IsFiniteMeasure ((torusHaarMeasure Λ).prod (torusHaarMeasure Λ)) := hFinProd
  have hf : Continuous f := continuous_of_flatTorus_lipschitz_bound Λ f hL hfLip
  have hcont : Continuous (fun p : Λ.torus × Λ.torus => ‖f p.1 - f p.2‖ ^ 2) := by
    fun_prop
  exact integrable_of_continuous_compactSpace_of_borel
    (X := Λ.torus × Λ.torus)
    (hB := inferInstance)
    (μ := (torusHaarMeasure Λ).prod (torusHaarMeasure Λ))
    (hμ := hFinProd)
    (g := fun p : Λ.torus × Λ.torus => ‖f p.1 - f p.2‖ ^ 2)
    hcont

private lemma flatTorus_lipschitz_physicalDirection_integral_sq_le
    {n : Nat} (Λ : KNFullRankLattice n)
    {H : Type v} [NormedAddCommGroup H] (f : Λ.torus -> H) {L : Real} (hL : 0 ≤ L)
    (hfLip :
      letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
      ∀ x y : Λ.torus, ‖f x - f y‖ ≤ L * dist x y)
    (j : Fin n) (t : Real) :
    letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
    letI : MeasurableSpace Λ.torus := borel Λ.torus
    (∫ x,
        ‖f (x + (show Λ.torus from QuotientAddGroup.mk' (integerLattice n)
          (t • coordinateVectorForPhysicalDirection Λ.basis j))) - f x‖ ^ 2
        ∂torusHaarMeasure Λ) ≤
      L ^ 2 * t ^ 2 := by
  letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
  letI : MeasurableSpace Λ.torus := borel Λ.torus
  haveI : CompactSpace Λ.torus := flatTorusMetric_compactSpace Λ.basis
  haveI : SecondCountableTopology Λ.torus := flatTorusMetric_secondCountableTopology Λ.basis
  haveI : BorelSpace Λ.torus := ⟨rfl⟩
  haveI : MeasureTheory.IsProbabilityMeasure (torusHaarMeasure Λ) :=
    torusHaarMeasure_isProbability Λ
  have hFinite : IsFiniteMeasure (torusHaarMeasure Λ) := by infer_instance
  letI : IsFiniteMeasure (torusHaarMeasure Λ) := hFinite
  let a : Λ.torus :=
    QuotientAddGroup.mk' (integerLattice n) (t • coordinateVectorForPhysicalDirection Λ.basis j)
  have hf_metric :
      letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
      Continuous f := continuous_of_flatTorus_lipschitz_bound Λ f hL hfLip
  have hf : Continuous f := by
    simpa [KNFullRankLattice.torusSeminormedAddCommGroup, KNFullRankLattice.torusMetric] using
      hf_metric
  have hInt :
      Integrable (fun x : Λ.torus => ‖f (x + a) - f x‖ ^ 2) (torusHaarMeasure Λ) := by
    refine integrable_of_continuous_compactSpace_of_borel
      (X := Λ.torus) (hB := inferInstance) (μ := torusHaarMeasure Λ)
      (hμ := hFinite) ?_
    fun_prop
  have hConstInt :
      Integrable (fun _ : Λ.torus => L ^ 2 * t ^ 2) (torusHaarMeasure Λ) :=
    integrable_const _
  have hpoint :
      ∀ x : Λ.torus, ‖f (x + a) - f x‖ ^ 2 ≤ L ^ 2 * t ^ 2 := by
    intro x
    have hdist_metric :
        (letI : PseudoMetricSpace Λ.torus := Λ.torusMetric;
          dist (x + a) x ≤ |t|) := by
      simpa [a] using flatTorusMetric_dist_add_physicalDirection_le_abs Λ.basis x j t
    have hnorm_metric :
        ‖f (x + a) - f x‖ ≤
          L * (letI : PseudoMetricSpace Λ.torus := Λ.torusMetric; dist (x + a) x) :=
      hfLip (x + a) x
    have hnorm_abs : ‖f (x + a) - f x‖ ≤ L * |t| := by
      exact hnorm_metric.trans (mul_le_mul_of_nonneg_left hdist_metric hL)
    have hsq :
        ‖f (x + a) - f x‖ ^ 2 ≤ (L * |t|) ^ 2 := by
      have hright_nonneg : 0 ≤ L * |t| := mul_nonneg hL (abs_nonneg _)
      have hdiff :
          0 ≤ L * |t| - ‖f (x + a) - f x‖ := sub_nonneg.mpr hnorm_abs
      have hsum :
          0 ≤ L * |t| + ‖f (x + a) - f x‖ :=
        add_nonneg hright_nonneg (norm_nonneg _)
      nlinarith [mul_nonneg hdiff hsum]
    calc
      ‖f (x + a) - f x‖ ^ 2 ≤ (L * |t|) ^ 2 := hsq
      _ = L ^ 2 * t ^ 2 := by rw [mul_pow, sq_abs]
  have hmono :
      (∫ x, ‖f (x + a) - f x‖ ^ 2 ∂torusHaarMeasure Λ) ≤
        ∫ _x : Λ.torus, L ^ 2 * t ^ 2 ∂torusHaarMeasure Λ :=
    MeasureTheory.integral_mono hInt hConstInt hpoint
  calc
    (∫ x, ‖f (x + a) - f x‖ ^ 2 ∂torusHaarMeasure Λ)
        ≤ ∫ _x : Λ.torus, L ^ 2 * t ^ 2 ∂torusHaarMeasure Λ := hmono
    _ = L ^ 2 * t ^ 2 := by simp

private lemma hilbertBasis_integral_finset_sum_repr_norm_sq_le
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [IsFiniteMeasure μ]
    {ι : Type*} {H : Type v} [NormedAddCommGroup H] [InnerProductSpace Real H]
    [CompleteSpace H] (b : HilbertBasis ι Real H) (s : Finset ι) {g : X -> H}
    (hg : Continuous g) :
    (∫ x, ∑ i ∈ s, ‖b.repr (g x) i‖ ^ 2 ∂μ) ≤ ∫ x, ‖g x‖ ^ 2 ∂μ := by
  have hleft :
      Integrable (fun x : X => ∑ i ∈ s, ‖b.repr (g x) i‖ ^ 2) μ := by
    refine integrable_of_continuous_compactSpace (μ := μ) ?_
    refine continuous_finsetSum s ?_
    intro i _hi
    have hcoord : Continuous (fun x : X => b.repr (g x) i) := by
      simpa [HilbertBasis.repr_apply_apply] using
        (continuous_const.inner (𝕜 := Real) hg : Continuous fun x : X => inner Real (b i) (g x))
    exact (hcoord.norm.pow 2)
  have hright : Integrable (fun x : X => ‖g x‖ ^ 2) μ := by
    exact integrable_of_continuous_compactSpace (μ := μ) (by fun_prop)
  exact integral_mono hleft hright fun x =>
    hilbertBasis_finset_sum_repr_norm_sq_le b s (g x)

private lemma hilbertBasis_exists_finset_norm_sq_lt_sum_repr_norm_sq_add
    {ι : Type*} {H : Type v} [NormedAddCommGroup H] [InnerProductSpace Real H]
    [CompleteSpace H] (b : HilbertBasis ι Real H) (v : H) {ε : Real} (hε : 0 < ε) :
    ∃ s : Finset ι, ‖v‖ ^ 2 < (∑ i ∈ s, ‖b.repr v i‖ ^ 2) + ε := by
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  have hsum :
      HasSum (fun i : ι => ‖b.repr v i‖ ^ 2) (‖v‖ ^ 2) := by
    simpa [LinearIsometryEquiv.norm_map] using lp.hasSum_norm (E := fun _ : ι => Real) hp (b.repr v)
  rw [HasSum, SummationFilter.unconditional_filter] at hsum
  have hnhds : Set.Ioi (‖v‖ ^ 2 - ε) ∈ 𝓝 (‖v‖ ^ 2) :=
    isOpen_Ioi.mem_nhds (sub_lt_self _ hε)
  rcases Filter.mem_atTop_sets.mp (hsum hnhds) with ⟨s, hs⟩
  refine ⟨s, ?_⟩
  have hs' : ‖v‖ ^ 2 - ε < ∑ i ∈ s, ‖b.repr v i‖ ^ 2 := by
    simpa using hs s le_rfl
  linarith

private lemma hilbertBasis_uniform_finset_norm_sq_le_sum_repr_norm_sq_add
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} {H : Type v} [NormedAddCommGroup H] [InnerProductSpace Real H]
    [CompleteSpace H] (b : HilbertBasis ι Real H) {g : X -> H}
    (hg : Continuous g) {ε : Real} (hε : 0 < ε) :
    ∃ s : Finset ι, ∀ x : X,
      ‖g x‖ ^ 2 ≤ (∑ i ∈ s, ‖b.repr (g x) i‖ ^ 2) + ε := by
  classical
  let U : Finset ι -> Set X := fun s =>
    {x : X | ‖g x‖ ^ 2 < (∑ i ∈ s, ‖b.repr (g x) i‖ ^ 2) + ε}
  have hUopen : ∀ s, IsOpen (U s) := by
    intro s
    dsimp [U]
    have hleft : Continuous fun x : X => ‖g x‖ ^ 2 := by fun_prop
    have hsum :
        Continuous fun x : X => ∑ i ∈ s, ‖b.repr (g x) i‖ ^ 2 := by
      refine continuous_finsetSum s ?_
      intro i _hi
      have hcoord : Continuous (fun x : X => b.repr (g x) i) := by
        simpa [HilbertBasis.repr_apply_apply] using
          (continuous_const.inner (𝕜 := Real) hg :
            Continuous fun x : X => inner Real (b i) (g x))
      exact hcoord.norm.pow 2
    exact isOpen_lt hleft (hsum.add continuous_const)
  have hcover : (Set.univ : Set X) ⊆ ⋃ s, U s := by
    intro x _hx
    rcases hilbertBasis_exists_finset_norm_sq_lt_sum_repr_norm_sq_add b (g x) hε with
      ⟨s, hs⟩
    exact Set.mem_iUnion.mpr ⟨s, hs⟩
  rcases isCompact_univ.elim_finite_subcover U hUopen hcover with ⟨S, hS⟩
  refine ⟨S.biUnion id, ?_⟩
  intro x
  have hxcover : x ∈ ⋃ s ∈ S, U s := hS (Set.mem_univ x)
  rcases Set.mem_iUnion.mp hxcover with ⟨s, hsx⟩
  rcases Set.mem_iUnion.mp hsx with ⟨hsS, hxs⟩
  have hsubset : s ⊆ S.biUnion id := Finset.subset_biUnion_of_mem id hsS
  have hsum_le :
      (∑ i ∈ s, ‖b.repr (g x) i‖ ^ 2) ≤
        ∑ i ∈ S.biUnion id, ‖b.repr (g x) i‖ ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset fun i _hi _his => sq_nonneg _
  have hsum_le_add :
      (∑ i ∈ s, ‖b.repr (g x) i‖ ^ 2) + ε ≤
        (∑ i ∈ S.biUnion id, ‖b.repr (g x) i‖ ^ 2) + ε := by
    linarith
  exact (le_of_lt hxs).trans hsum_le_add

private lemma hilbertBasis_integral_norm_sq_le_of_finset_integral_le
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] [IsProbabilityMeasure μ]
    {ι : Type*} {H : Type v} [NormedAddCommGroup H] [InnerProductSpace Real H]
    [CompleteSpace H] (b : HilbertBasis ι Real H) {g : X -> H} (hg : Continuous g)
    {C : Real}
    (hbound :
      ∀ s : Finset ι,
        (∫ x, ∑ i ∈ s, ‖b.repr (g x) i‖ ^ 2 ∂μ) ≤ C) :
    (∫ x, ‖g x‖ ^ 2 ∂μ) ≤ C := by
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  rcases hilbertBasis_uniform_finset_norm_sq_le_sum_repr_norm_sq_add b hg hε with ⟨s, hs⟩
  have hnormInt : Integrable (fun x : X => ‖g x‖ ^ 2) μ := by
    exact integrable_of_continuous_compactSpace (μ := μ) (by fun_prop)
  have hsumInt : Integrable (fun x : X => ∑ i ∈ s, ‖b.repr (g x) i‖ ^ 2) μ := by
    refine integrable_of_continuous_compactSpace (μ := μ) ?_
    refine continuous_finsetSum s ?_
    intro i _hi
    have hcoord : Continuous (fun x : X => b.repr (g x) i) := by
      simpa [HilbertBasis.repr_apply_apply] using
        (continuous_const.inner (𝕜 := Real) hg :
          Continuous fun x : X => inner Real (b i) (g x))
    exact hcoord.norm.pow 2
  have hsumAddInt :
      Integrable (fun x : X => (∑ i ∈ s, ‖b.repr (g x) i‖ ^ 2) + ε) μ :=
    hsumInt.add (integrable_const (c := ε))
  have hmono :
      (∫ x, ‖g x‖ ^ 2 ∂μ) ≤
        ∫ x, (∑ i ∈ s, ‖b.repr (g x) i‖ ^ 2) + ε ∂μ :=
    integral_mono hnormInt hsumAddInt hs
  calc
    (∫ x, ‖g x‖ ^ 2 ∂μ)
        ≤ ∫ x, (∑ i ∈ s, ‖b.repr (g x) i‖ ^ 2) + ε ∂μ := hmono
    _ = (∫ x, ∑ i ∈ s, ‖b.repr (g x) i‖ ^ 2 ∂μ) + ε := by
          rw [integral_add hsumInt (integrable_const (c := ε))]
          simp
    _ ≤ C + ε := by linarith [hbound s]

private lemma flatTorus_lipschitz_physicalDirection_hilbertBasis_integral_sq_le
    {n : Nat} (Λ : KNFullRankLattice n)
    {ι : Type*} {H : Type v} [NormedAddCommGroup H] [InnerProductSpace Real H]
    [CompleteSpace H] (b : HilbertBasis ι Real H) (s : Finset ι)
    (f : Λ.torus -> H) {L : Real} (hL : 0 ≤ L)
    (hfLip :
      letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
      ∀ x y : Λ.torus, ‖f x - f y‖ ≤ L * dist x y)
    (j : Fin n) (t : Real) :
    letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
    letI : MeasurableSpace Λ.torus := borel Λ.torus
    (∫ x,
        ∑ i ∈ s,
          ‖b.repr
            (f (x + (show Λ.torus from QuotientAddGroup.mk' (integerLattice n)
              (t • coordinateVectorForPhysicalDirection Λ.basis j))) - f x) i‖ ^ 2
        ∂torusHaarMeasure Λ) ≤
      L ^ 2 * t ^ 2 := by
  letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
  letI : MeasurableSpace Λ.torus := borel Λ.torus
  haveI : CompactSpace Λ.torus := Λ.torus_compactSpace
  haveI : BorelSpace Λ.torus := ⟨rfl⟩
  haveI : MeasureTheory.IsProbabilityMeasure (torusHaarMeasure Λ) :=
    torusHaarMeasure_isProbability Λ
  have hFinite : IsFiniteMeasure (torusHaarMeasure Λ) := by infer_instance
  letI : IsFiniteMeasure (torusHaarMeasure Λ) := hFinite
  let a : Λ.torus :=
    QuotientAddGroup.mk' (integerLattice n) (t • coordinateVectorForPhysicalDirection Λ.basis j)
  have hf_metric :
      letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
      Continuous f := continuous_of_flatTorus_lipschitz_bound Λ f hL hfLip
  have hf : Continuous f := by
    simpa [KNFullRankLattice.torusSeminormedAddCommGroup, KNFullRankLattice.torusMetric] using
      hf_metric
  have hg : Continuous fun x : Λ.torus => f (x + a) - f x := by
    fun_prop
  have hcoords :
      (∫ x, ∑ i ∈ s, ‖b.repr (f (x + a) - f x) i‖ ^ 2
          ∂torusHaarMeasure Λ) ≤
        ∫ x, ‖f (x + a) - f x‖ ^ 2 ∂torusHaarMeasure Λ :=
    hilbertBasis_integral_finset_sum_repr_norm_sq_le
      (X := Λ.torus) (μ := torusHaarMeasure Λ) b s hg
  have hdir :=
    flatTorus_lipschitz_physicalDirection_integral_sq_le Λ f hL hfLip j t
  exact hcoords.trans (by simpa [a] using hdir)

private noncomputable def flatTorusHilbertCoordinateOnUnitTorus
    {n : Nat} (Λ : KNFullRankLattice n)
    {ι : Type*} {H : Type v} [NormedAddCommGroup H] [InnerProductSpace Real H]
    [CompleteSpace H] (b : HilbertBasis ι Real H) (f : Λ.torus -> H)
    (hf :
      letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
      Continuous f)
    (i : ι) : C(UnitAddTorus (Fin n), ℂ) where
  toFun z := ((b.repr (f ((coordinateTorusAddEquivUnitAddTorus n).symm z)) i : Real) : ℂ)
  continuous_toFun := by
    letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
    have hsymm := continuous_symm_coordinateTorusAddEquivUnitAddTorus Λ
    have hcoord : Continuous (fun x : Λ.torus => (b.repr (f x) i : Real)) := by
      simpa [HilbertBasis.repr_apply_apply] using
        (continuous_const.inner (𝕜 := Real) hf :
          Continuous fun x : Λ.torus => inner Real (b i) (f x))
    exact Complex.continuous_ofReal.comp (hcoord.comp hsymm)

private lemma coordinateTorusAddEquivUnitAddTorus_symm_add_physicalDirection
    {n : Nat} (Λ : KNFullRankLattice n) (x : Λ.torus) (j : Fin n) (t : Real) :
    letI : AddCommGroup Λ.torus := flatTorusAddCommGroup n Λ.basis
    (coordinateTorusAddEquivUnitAddTorus n).symm
        (coordinateTorusAddEquivUnitAddTorus n x +
          euclideanToUnitAddTorus n (t • coordinateVectorForPhysicalDirection Λ.basis j)) =
      x + (show Λ.torus from QuotientAddGroup.mk' (integerLattice n)
        (t • coordinateVectorForPhysicalDirection Λ.basis j)) := by
  letI : AddCommGroup Λ.torus := flatTorusAddCommGroup n Λ.basis
  let e := coordinateTorusAddEquivUnitAddTorus n
  let a : Λ.torus := QuotientAddGroup.mk' (integerLattice n)
    (t • coordinateVectorForPhysicalDirection Λ.basis j)
  have ha : e a = euclideanToUnitAddTorus n
      (t • coordinateVectorForPhysicalDirection Λ.basis j) := by
    simpa [e, a] using
      coordinateTorusAddEquivUnitAddTorus_apply_mk n
        (t • coordinateVectorForPhysicalDirection Λ.basis j)
  apply e.injective
  rw [e.apply_symm_apply]
  change e x + euclideanToUnitAddTorus n
      (t • coordinateVectorForPhysicalDirection Λ.basis j) = e (x + a)
  rw [← ha]
  exact (e.map_add x a).symm

private lemma unitAddTorus_lipschitz_physicalDirection_hilbertBasis_integral_sq_le
    {n : Nat} (Λ : KNFullRankLattice n)
    {ι : Type*} {H : Type v} [NormedAddCommGroup H] [InnerProductSpace Real H]
    [CompleteSpace H] (b : HilbertBasis ι Real H) (s : Finset ι)
    (f : Λ.torus -> H) {L : Real} (hL : 0 ≤ L)
    (hf :
      letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
      Continuous f)
    (hfLip :
      letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
      ∀ x y : Λ.torus, ‖f x - f y‖ ≤ L * dist x y)
    (j : Fin n) (t : Real) :
    letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
    letI : MeasurableSpace Λ.torus := borel Λ.torus
    (∫ z : UnitAddTorus (Fin n),
        ∑ i ∈ s,
          ‖(flatTorusHilbertCoordinateOnUnitTorus Λ b f hf i)
              (z + euclideanToUnitAddTorus n
                (t • coordinateVectorForPhysicalDirection Λ.basis j)) -
            (flatTorusHilbertCoordinateOnUnitTorus Λ b f hf i) z‖ ^ 2
        ∂(volume : Measure (UnitAddTorus (Fin n)))) ≤
      L ^ 2 * t ^ 2 := by
  classical
  letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
  letI : MeasurableSpace Λ.torus := borel Λ.torus
  haveI : BorelSpace Λ.torus := ⟨rfl⟩
  haveI : CompactSpace Λ.torus := Λ.torus_compactSpace
  let e := coordinateTorusAddEquivUnitAddTorus n
  let aT : Λ.torus :=
    QuotientAddGroup.mk' (integerLattice n)
      (t • coordinateVectorForPhysicalDirection Λ.basis j)
  let aU : UnitAddTorus (Fin n) :=
    euclideanToUnitAddTorus n (t • coordinateVectorForPhysicalDirection Λ.basis j)
  let φ : UnitAddTorus (Fin n) -> Real := fun z =>
    ∑ i ∈ s,
      ‖(flatTorusHilbertCoordinateOnUnitTorus Λ b f hf i) (z + aU) -
        (flatTorusHilbertCoordinateOnUnitTorus Λ b f hf i) z‖ ^ 2
  let ψ : Λ.torus -> Real := fun x =>
    ∑ i ∈ s, ‖b.repr (f (x + aT) - f x) i‖ ^ 2
  have hpoint : ∀ x : Λ.torus, φ (e x) = ψ x := by
    intro x
    dsimp [φ, ψ, flatTorusHilbertCoordinateOnUnitTorus]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    congr 1
    have htranslate : e.symm (e x + aU) = x + aT := by
      simpa [e, aT, aU] using
        coordinateTorusAddEquivUnitAddTorus_symm_add_physicalDirection Λ x j t
    have hcoord :
        b.repr (f (x + aT) - f x) i =
          b.repr (f (x + aT)) i - b.repr (f x) i := by
      rw [map_sub]
      rfl
    have hbase : (coordinateTorusAddEquivUnitAddTorus n).symm (e x) = x := by
      simpa [e] using e.symm_apply_apply x
    rw [htranslate, hbase]
    rw [hcoord]
    rw [← Complex.ofReal_sub]
    exact RCLike.norm_ofReal _
  have hmp := measurePreserving_coordinateTorusAddEquivUnitAddTorus_global Λ
  have hemb := measurableEmbedding_coordinateTorusAddEquivUnitAddTorus Λ
  have htransfer :
      (∫ z : UnitAddTorus (Fin n), φ z ∂(volume : Measure (UnitAddTorus (Fin n)))) =
        ∫ x : Λ.torus, ψ x ∂torusHaarMeasure Λ := by
    calc
      (∫ z : UnitAddTorus (Fin n), φ z ∂(volume : Measure (UnitAddTorus (Fin n)))) =
          ∫ x : Λ.torus, φ (e x) ∂torusHaarMeasure Λ := by
            simpa [e] using
              (hmp.integral_comp hemb φ).symm
      _ = ∫ x : Λ.torus, ψ x ∂torusHaarMeasure Λ := by
            simp_rw [hpoint]
  change (∫ z : UnitAddTorus (Fin n), φ z
      ∂(volume : Measure (UnitAddTorus (Fin n)))) ≤ L ^ 2 * t ^ 2
  rw [htransfer]
  simpa [ψ, aT] using
    flatTorus_lipschitz_physicalDirection_hilbertBasis_integral_sq_le
      Λ b s f hL hfLip j t

private lemma unitAddTorus_integral_fourierVolume_eq_default
    {n : Nat} (g : UnitAddTorus (Fin n) -> Real) :
    (letI : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
      ∫ z, g z ∂(volume : Measure (UnitAddTorus (Fin n)))) =
      ∫ z, g z ∂(volume : Measure (UnitAddTorus (Fin n))) := by
  simp [volume, AddCircle.haarAddCircle]

private lemma unitAddTorus_finset_sum_hilbertCoordinate_mFourierCoeff_translate_sub_sq_le_integral
    {n : Nat} (Λ : KNFullRankLattice n)
    {ι : Type*} {H : Type v} [NormedAddCommGroup H] [InnerProductSpace Real H]
    [CompleteSpace H] (b : HilbertBasis ι Real H) (E : Finset ι)
    (f : Λ.torus -> H)
    (hf :
      letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
      Continuous f)
    (a : UnitAddTorus (Fin n)) (F : Finset (Fin n -> Int)) :
    (∑ i ∈ E, ∑ k ∈ F,
        ‖(UnitAddTorus.mFourier k a - 1) *
          UnitAddTorus.mFourierCoeff
            (flatTorusHilbertCoordinateOnUnitTorus Λ b f hf i) k‖ ^ 2) ≤
      ∫ z : UnitAddTorus (Fin n),
        ∑ i ∈ E,
          ‖(flatTorusHilbertCoordinateOnUnitTorus Λ b f hf i) (z + a) -
            (flatTorusHilbertCoordinateOnUnitTorus Λ b f hf i) z‖ ^ 2
        ∂(volume : Measure (UnitAddTorus (Fin n))) := by
  classical
  let φ : ι -> C(UnitAddTorus (Fin n), ℂ) :=
    fun i => flatTorusHilbertCoordinateOnUnitTorus Λ b f hf i
  change
    (∑ i ∈ E, ∑ k ∈ F,
        ‖(UnitAddTorus.mFourier k a - 1) *
          UnitAddTorus.mFourierCoeff (φ i) k‖ ^ 2) ≤
      ∫ z : UnitAddTorus (Fin n),
        ∑ i ∈ E, ‖(φ i) (z + a) - (φ i) z‖ ^ 2
        ∂(volume : Measure (UnitAddTorus (Fin n)))
  have hsum_le :
      (∑ i ∈ E, ∑ k ∈ F,
          ‖(UnitAddTorus.mFourier k a - 1) *
            UnitAddTorus.mFourierCoeff (φ i) k‖ ^ 2) ≤
        ∑ i ∈ E,
          ∫ z : UnitAddTorus (Fin n), ‖(φ i) (z + a) - (φ i) z‖ ^ 2
            ∂(volume : Measure (UnitAddTorus (Fin n))) := by
    refine Finset.sum_le_sum ?_
    intro i _hi
    have hscalar :=
      unitAddTorus_finset_sum_mFourierCoeff_translate_sub_sq_le_integral (φ i) a F
    have hvolume :=
      unitAddTorus_integral_fourierVolume_eq_default (n := n)
        (fun z : UnitAddTorus (Fin n) => ‖(φ i) (z + a) - (φ i) z‖ ^ 2)
    exact hscalar.trans_eq hvolume
  have hint :
      ∀ i ∈ E,
        Integrable (fun z : UnitAddTorus (Fin n) => ‖(φ i) (z + a) - (φ i) z‖ ^ 2)
          (volume : Measure (UnitAddTorus (Fin n))) := by
    intro i _hi
    have hcont :
        Continuous (fun z : UnitAddTorus (Fin n) => ‖(φ i) (z + a) - (φ i) z‖ ^ 2) := by
      fun_prop
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    (∑ i ∈ E, ∑ k ∈ F,
        ‖(UnitAddTorus.mFourier k a - 1) *
          UnitAddTorus.mFourierCoeff (φ i) k‖ ^ 2)
        ≤ ∑ i ∈ E,
          ∫ z : UnitAddTorus (Fin n), ‖(φ i) (z + a) - (φ i) z‖ ^ 2
            ∂(volume : Measure (UnitAddTorus (Fin n))) := hsum_le
    _ = ∫ z : UnitAddTorus (Fin n),
        ∑ i ∈ E, ‖(φ i) (z + a) - (φ i) z‖ ^ 2
        ∂(volume : Measure (UnitAddTorus (Fin n))) := by
          exact (MeasureTheory.integral_finsetSum E hint).symm

private theorem flatTorus_finite_spectral_estimate
    {n : Nat} (_hn : 1 ≤ n) (Λ : KNFullRankLattice n)
    {ι : Type*} {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
    (b : HilbertBasis ι Real H)
    (E : Finset ι) (F : Finset (Fin n -> Int))
    (f : Λ.torus -> H) {L : Real} (hL : 0 ≤ L)
    (hf :
      letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
      Continuous f)
    (hfLip :
      letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
      ∀ x y : Λ.torus, ‖f x - f y‖ ≤ L * dist x y) :
    (∑ i ∈ E, ∑ k ∈ F,
        (4 * Real.pi ^ 2 * ‖dualVectorOfFrequency Λ k‖ ^ 2) *
          ‖UnitAddTorus.mFourierCoeff
            (flatTorusHilbertCoordinateOnUnitTorus Λ b f hf i) k‖ ^ 2) ≤
      (n : Real) * L ^ 2 := by
  classical
  letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
  letI : MeasurableSpace Λ.torus := borel Λ.torus
  let φ : ι -> C(UnitAddTorus (Fin n), ℂ) :=
    fun i => flatTorusHilbertCoordinateOnUnitTorus Λ b f hf i
  change
    (∑ i ∈ E, ∑ k ∈ F,
        (4 * Real.pi ^ 2 * ‖dualVectorOfFrequency Λ k‖ ^ 2) *
          ‖UnitAddTorus.mFourierCoeff (φ i) k‖ ^ 2) ≤
      (n : Real) * L ^ 2
  let approx : Real -> Real := fun t =>
    ∑ j : Fin n, ∑ i ∈ E, ∑ k ∈ F,
      ‖(Complex.exp
          (2 * Real.pi * Complex.I *
            ((t * inner Real (dualVectorOfFrequency Λ k) (euclideanStdBasis n j) : Real) :
              Complex)) - 1) *
        UnitAddTorus.mFourierCoeff (φ i) k‖ ^ 2 / t ^ 2
  have hlimRaw :
      Filter.Tendsto approx (𝓝[≠] (0 : Real))
        (𝓝 (∑ j : Fin n, ∑ i ∈ E, ∑ k ∈ F,
          (4 * Real.pi ^ 2 *
            inner Real (dualVectorOfFrequency Λ k) (euclideanStdBasis n j) ^ 2) *
              ‖UnitAddTorus.mFourierCoeff (φ i) k‖ ^ 2)) := by
    dsimp [approx]
    refine tendsto_finsetSum (Finset.univ : Finset (Fin n)) ?_
    intro j _hj
    refine tendsto_finsetSum E ?_
    intro i _hi
    refine tendsto_finsetSum F ?_
    intro k _hk
    have hbase :=
      complex_exp_sub_one_sq_div_tendsto
        (inner Real (dualVectorOfFrequency Λ k) (euclideanStdBasis n j))
    have hmul := hbase.mul
      (tendsto_const_nhds :
        Filter.Tendsto
          (fun _ : Real => ‖UnitAddTorus.mFourierCoeff (φ i) k‖ ^ 2)
          (𝓝[≠] (0 : Real))
          (𝓝 (‖UnitAddTorus.mFourierCoeff (φ i) k‖ ^ 2)))
    refine hmul.congr' (Filter.Eventually.of_forall ?_)
    intro t
    let z : Complex :=
      Complex.exp
        (2 * Real.pi * Complex.I *
          ((t * inner Real (dualVectorOfFrequency Λ k) (euclideanStdBasis n j) : Real) :
            Complex)) - 1
    let c : Complex := UnitAddTorus.mFourierCoeff (φ i) k
    change (‖z‖ ^ 2 / t ^ 2) * ‖c‖ ^ 2 = ‖z * c‖ ^ 2 / t ^ 2
    rw [norm_mul, mul_pow]
    ring
  have htarget :
      (∑ j : Fin n, ∑ i ∈ E, ∑ k ∈ F,
          (4 * Real.pi ^ 2 *
            inner Real (dualVectorOfFrequency Λ k) (euclideanStdBasis n j) ^ 2) *
              ‖UnitAddTorus.mFourierCoeff (φ i) k‖ ^ 2) =
        ∑ i ∈ E, ∑ k ∈ F,
          (4 * Real.pi ^ 2 * ‖dualVectorOfFrequency Λ k‖ ^ 2) *
            ‖UnitAddTorus.mFourierCoeff (φ i) k‖ ^ 2 := by
    calc
      (∑ j : Fin n, ∑ i ∈ E, ∑ k ∈ F,
          (4 * Real.pi ^ 2 *
            inner Real (dualVectorOfFrequency Λ k) (euclideanStdBasis n j) ^ 2) *
              ‖UnitAddTorus.mFourierCoeff (φ i) k‖ ^ 2) =
          ∑ i ∈ E, ∑ j : Fin n, ∑ k ∈ F,
            (4 * Real.pi ^ 2 *
              inner Real (dualVectorOfFrequency Λ k) (euclideanStdBasis n j) ^ 2) *
                ‖UnitAddTorus.mFourierCoeff (φ i) k‖ ^ 2 := by
            rw [Finset.sum_comm]
      _ = ∑ i ∈ E, ∑ k ∈ F, ∑ j : Fin n,
            (4 * Real.pi ^ 2 *
              inner Real (dualVectorOfFrequency Λ k) (euclideanStdBasis n j) ^ 2) *
                ‖UnitAddTorus.mFourierCoeff (φ i) k‖ ^ 2 := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [Finset.sum_comm]
      _ = ∑ i ∈ E, ∑ k ∈ F,
          (4 * Real.pi ^ 2 * ‖dualVectorOfFrequency Λ k‖ ^ 2) *
            ‖UnitAddTorus.mFourierCoeff (φ i) k‖ ^ 2 := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            refine Finset.sum_congr rfl ?_
            intro k _hk
            rw [← Finset.sum_mul]
            rw [← four_pi_sq_dualVector_norm_sq_eq_coordinate_sum Λ k]
  have hlim :
      Filter.Tendsto approx (𝓝[≠] (0 : Real))
        (𝓝 (∑ i ∈ E, ∑ k ∈ F,
          (4 * Real.pi ^ 2 * ‖dualVectorOfFrequency Λ k‖ ^ 2) *
            ‖UnitAddTorus.mFourierCoeff (φ i) k‖ ^ 2)) := by
    simpa [htarget] using hlimRaw
  have hbound : ∀ᶠ t in 𝓝[≠] (0 : Real), approx t ≤ (n : Real) * L ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t ≠ 0 := by simpa using ht
    have htSq_nonneg : 0 ≤ t ^ 2 := sq_nonneg t
    have hperDirection :
        ∀ j : Fin n,
          (∑ i ∈ E, ∑ k ∈ F,
            ‖(Complex.exp
                (2 * Real.pi * Complex.I *
                  ((t * inner Real (dualVectorOfFrequency Λ k) (euclideanStdBasis n j) :
                    Real) : Complex)) - 1) *
              UnitAddTorus.mFourierCoeff (φ i) k‖ ^ 2 / t ^ 2) ≤ L ^ 2 := by
      intro j
      let a : UnitAddTorus (Fin n) :=
        euclideanToUnitAddTorus n (t • coordinateVectorForPhysicalDirection Λ.basis j)
      have hfourier :=
        unitAddTorus_finset_sum_hilbertCoordinate_mFourierCoeff_translate_sub_sq_le_integral
          Λ b E f hf a F
      have hphysical :=
        unitAddTorus_lipschitz_physicalDirection_hilbertBasis_integral_sq_le
          Λ b E f hL hf hfLip j t
      have hsum_mfourier :
          (∑ i ∈ E, ∑ k ∈ F,
              ‖(UnitAddTorus.mFourier k a - 1) *
                UnitAddTorus.mFourierCoeff (φ i) k‖ ^ 2) ≤
            L ^ 2 * t ^ 2 := by
        exact hfourier.trans (by simpa [a, φ] using hphysical)
      have hsum_exp :
          (∑ i ∈ E, ∑ k ∈ F,
              ‖(Complex.exp
                  (2 * Real.pi * Complex.I *
                    ((t * inner Real (dualVectorOfFrequency Λ k) (euclideanStdBasis n j) :
                      Real) : Complex)) - 1) *
                UnitAddTorus.mFourierCoeff (φ i) k‖ ^ 2) ≤
            L ^ 2 * t ^ 2 := by
        simpa [a, unitAddTorus_mFourier_physicalDirection Λ, φ] using hsum_mfourier
      calc
        (∑ i ∈ E, ∑ k ∈ F,
            ‖(Complex.exp
                (2 * Real.pi * Complex.I *
                  ((t * inner Real (dualVectorOfFrequency Λ k) (euclideanStdBasis n j) :
                    Real) : Complex)) - 1) *
              UnitAddTorus.mFourierCoeff (φ i) k‖ ^ 2 / t ^ 2) =
            (∑ i ∈ E, ∑ k ∈ F,
              ‖(Complex.exp
                  (2 * Real.pi * Complex.I *
                    ((t * inner Real (dualVectorOfFrequency Λ k) (euclideanStdBasis n j) :
                      Real) : Complex)) - 1) *
                UnitAddTorus.mFourierCoeff (φ i) k‖ ^ 2) / t ^ 2 := by
              simp [Finset.sum_div]
        _ ≤ (L ^ 2 * t ^ 2) / t ^ 2 :=
            div_le_div_of_nonneg_right hsum_exp htSq_nonneg
        _ = L ^ 2 := by
            field_simp [ht']
    calc
      approx t ≤ ∑ _j : Fin n, L ^ 2 := by
        dsimp [approx]
        exact Finset.sum_le_sum fun j _hj => hperDirection j
      _ = (n : Real) * L ^ 2 := by
        simp [Finset.card_univ, nsmul_eq_mul]
  exact le_of_tendsto hlim hbound

private lemma mFourierCoeff_zero_eq_integral
    {n : Nat} (g : C(UnitAddTorus (Fin n), ℂ)) :
    UnitAddTorus.mFourierCoeff g 0 =
      ∫ z, g z ∂(volume : Measure (UnitAddTorus (Fin n))) := by
  unfold UnitAddTorus.mFourierCoeff
  simp [UnitAddTorus.mFourier, volume, AddCircle.haarAddCircle]

private lemma unitAddTorus_hasSum_sq_mFourierCoeff
    {n : Nat} (g : C(UnitAddTorus (Fin n), ℂ)) :
    HasSum
      (fun k : Fin n -> Int => ‖UnitAddTorus.mFourierCoeff g k‖ ^ 2)
      (∫ z, ‖g z‖ ^ 2 ∂(volume : Measure (UnitAddTorus (Fin n)))) := by
  letI : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
  letI : MeasureTheory.Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
    inferInstanceAs (MeasureTheory.Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
  letI : MeasureTheory.IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
    inferInstanceAs (MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle)
  have hparse := UnitAddTorus.hasSum_sq_mFourierCoeff (g.toLp 2 volume ℂ)
  have hparseLocal :
      HasSum
        (fun k : Fin n -> Int => ‖UnitAddTorus.mFourierCoeff g k‖ ^ 2)
        (∫ z, ‖g z‖ ^ 2 ∂(volume : Measure (UnitAddTorus (Fin n)))) := by
    convert hparse using 1
    · ext k
      rw [UnitAddTorus.mFourierCoeff_toLp (f := g) k]
    · apply integral_congr_ae
      filter_upwards [g.coeFn_toLp (p := 2) (μ := volume) (𝕜 := ℂ)] with z hz
      rw [hz]
  rw [unitAddTorus_integral_fourierVolume_eq_default (n := n)
    (fun z : UnitAddTorus (Fin n) => ‖g z‖ ^ 2)] at hparseLocal
  exact hparseLocal

private noncomputable def centeredFlatTorusHilbertCoordinateOnUnitTorus
    {n : Nat} (Λ : KNFullRankLattice n)
    {ι : Type*} {H : Type v} [NormedAddCommGroup H] [InnerProductSpace Real H]
    [CompleteSpace H] (b : HilbertBasis ι Real H) (f : Λ.torus -> H)
    (hf :
      letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
      Continuous f)
    (i : ι) : C(UnitAddTorus (Fin n), ℂ) where
  toFun z :=
    letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
    letI : MeasurableSpace Λ.torus := borel Λ.torus
    ((b.repr
      (f ((coordinateTorusAddEquivUnitAddTorus n).symm z) -
        ∫ x, f x ∂torusHaarMeasure Λ) i : Real) : ℂ)
  continuous_toFun := by
    letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
    letI : MeasurableSpace Λ.torus := borel Λ.torus
    have hsymm := continuous_symm_coordinateTorusAddEquivUnitAddTorus Λ
    let mean : H := ∫ x, f x ∂torusHaarMeasure Λ
    have hinner :
        Continuous fun z : UnitAddTorus (Fin n) =>
          ((inner Real (b i) (f ((coordinateTorusAddEquivUnitAddTorus n).symm z) - mean) :
            Real) : ℂ) := by
      refine Complex.continuous_ofReal.comp ?_
      exact (continuous_const.inner (𝕜 := Real) (hf.sub continuous_const)).comp hsymm
    exact hinner.congr fun z => by
      simpa using
        (HilbertBasis.repr_apply_apply b
          (f ((coordinateTorusAddEquivUnitAddTorus n).symm z) - mean) i).symm

private lemma centered_hilbert_coordinate_integral_zero
    {n : Nat} (Λ : KNFullRankLattice n)
    {ι : Type*} {H : Type v} [NormedAddCommGroup H] [InnerProductSpace Real H]
    [CompleteSpace H] (b : HilbertBasis ι Real H) (f : Λ.torus -> H)
    (hf :
      letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
      Continuous f)
    (i : ι) :
    (∫ z,
        centeredFlatTorusHilbertCoordinateOnUnitTorus Λ b f hf i z
        ∂(volume : Measure (UnitAddTorus (Fin n)))) = 0 := by
  classical
  letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
  letI : MeasurableSpace Λ.torus := borel Λ.torus
  haveI : CompactSpace Λ.torus := Λ.torus_compactSpace
  letI : BorelSpace Λ.torus := ⟨rfl⟩
  haveI : MeasureTheory.IsProbabilityMeasure (torusHaarMeasure Λ) :=
    torusHaarMeasure_isProbability Λ
  have hFinite : IsFiniteMeasure (torusHaarMeasure Λ) := by infer_instance
  letI : IsFiniteMeasure (torusHaarMeasure Λ) := hFinite
  let mean : H := ∫ x, f x ∂torusHaarMeasure Λ
  let coord : Λ.torus -> Real := fun x => (b.repr (f x - mean) i : Real)
  have hreal_transfer :
      (∫ z : UnitAddTorus (Fin n),
          coord ((coordinateTorusAddEquivUnitAddTorus n).symm z)
          ∂(volume : Measure (UnitAddTorus (Fin n)))) =
        ∫ x : Λ.torus, coord x ∂torusHaarMeasure Λ := by
    simpa [coord] using (integral_flatTorus_eq_integral_unitTorus Λ coord).symm
  have hfInt : Integrable f (torusHaarMeasure Λ) := by
    exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have hcoord_integral :
      (∫ x : Λ.torus, coord x ∂torusHaarMeasure Λ) = 0 := by
    let L : H →L[Real] Real := innerSL Real (b i)
    have hcoord_eq : ∀ x : Λ.torus, coord x = L (f x - mean) := by
      intro x
      simpa [coord, L] using (HilbertBasis.repr_apply_apply b (f x - mean) i)
    calc
      (∫ x : Λ.torus, coord x ∂torusHaarMeasure Λ) =
          ∫ x : Λ.torus, L (f x - mean) ∂torusHaarMeasure Λ := by
            exact integral_congr_ae (ae_of_all _ hcoord_eq)
      _ = L (∫ x : Λ.torus, f x - mean ∂torusHaarMeasure Λ) := by
            exact L.integral_comp_comm (hfInt.sub (integrable_const (c := mean)))
      _ = L ((∫ x : Λ.torus, f x ∂torusHaarMeasure Λ) - mean) := by
            rw [integral_sub hfInt (integrable_const (c := mean))]
            simp
      _ = 0 := by
            simp [L, mean]
  have hcomplex_transfer :
      (∫ z : UnitAddTorus (Fin n),
          (coord ((coordinateTorusAddEquivUnitAddTorus n).symm z) : ℂ)
          ∂(volume : Measure (UnitAddTorus (Fin n)))) =
        ∫ x : Λ.torus, (coord x : ℂ) ∂torusHaarMeasure Λ := by
    rw [integral_complex_ofReal, integral_complex_ofReal]
    exact congrArg (fun r : Real => (r : ℂ)) hreal_transfer
  calc
    (∫ z,
        centeredFlatTorusHilbertCoordinateOnUnitTorus Λ b f hf i z
        ∂(volume : Measure (UnitAddTorus (Fin n)))) =
        ∫ z : UnitAddTorus (Fin n),
          (coord ((coordinateTorusAddEquivUnitAddTorus n).symm z) : ℂ)
          ∂(volume : Measure (UnitAddTorus (Fin n))) := by
          exact integral_congr_ae (ae_of_all _ fun z => by
            simp [centeredFlatTorusHilbertCoordinateOnUnitTorus, coord, mean])
    _ = ∫ x : Λ.torus, (coord x : ℂ) ∂torusHaarMeasure Λ := hcomplex_transfer
    _ = 0 := by
          rw [integral_complex_ofReal, hcoord_integral]
          norm_num

private lemma centered_hilbert_coordinate_zero_coeff
    {n : Nat} (Λ : KNFullRankLattice n)
    {ι : Type*} {H : Type v} [NormedAddCommGroup H] [InnerProductSpace Real H]
    [CompleteSpace H] (b : HilbertBasis ι Real H) (f : Λ.torus -> H)
    (hf :
      letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
      Continuous f)
    (i : ι) :
    UnitAddTorus.mFourierCoeff
        (centeredFlatTorusHilbertCoordinateOnUnitTorus Λ b f hf i) 0 = 0 := by
  rw [mFourierCoeff_zero_eq_integral]
  exact centered_hilbert_coordinate_integral_zero Λ b f hf i

private lemma flatTorus_finite_coordinate_variance_le
    {n : Nat} (hn : 1 ≤ n) (Λ : KNFullRankLattice n)
    {ι : Type*} {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
    (b : HilbertBasis ι Real H) (E : Finset ι)
    (f : Λ.torus -> H) {L : Real} (hL : 0 ≤ L)
    (hf :
      letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
      Continuous f)
    (hfLip :
      letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
      ∀ x y : Λ.torus, ‖f x - f y‖ ≤ L * dist x y) :
    letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
    letI : MeasurableSpace Λ.torus := borel Λ.torus
    (∫ x,
        ∑ i ∈ E,
          ‖b.repr
            (f x - (∫ y, f y ∂torusHaarMeasure Λ)) i‖ ^ 2
        ∂torusHaarMeasure Λ) ≤
      (n : Real) * L ^ 2 /
        (4 * Real.pi ^ 2 * shortestVectorLength (knDualLattice Λ) ^ 2) := by
  classical
  letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
  letI : MeasurableSpace Λ.torus := borel Λ.torus
  haveI : CompactSpace Λ.torus := Λ.torus_compactSpace
  letI : BorelSpace Λ.torus := ⟨rfl⟩
  haveI : MeasureTheory.IsProbabilityMeasure (torusHaarMeasure Λ) :=
    torusHaarMeasure_isProbability Λ
  let mean : H := ∫ y, f y ∂torusHaarMeasure Λ
  let g : Λ.torus -> H := fun x => f x - mean
  have hg : Continuous g := hf.sub continuous_const
  have hgLip :
      letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
      ∀ x y : Λ.torus, ‖g x - g y‖ ≤ L * dist x y := by
    letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
    intro x y
    have hxy := hfLip x y
    simpa [g, mean, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hxy
  let φ : ι -> C(UnitAddTorus (Fin n), ℂ) :=
    fun i => flatTorusHilbertCoordinateOnUnitTorus Λ b g hg i
  have hzero : ∀ i : ι, UnitAddTorus.mFourierCoeff (φ i) 0 = 0 := by
    intro i
    have hcenter := centered_hilbert_coordinate_zero_coeff Λ b f hf i
    have hφ :
        φ i = centeredFlatTorusHilbertCoordinateOnUnitTorus Λ b f hf i := by
      ext z
      simp [φ, flatTorusHilbertCoordinateOnUnitTorus,
        centeredFlatTorusHilbertCoordinateOnUnitTorus, g, mean]
    simpa [hφ] using hcenter
  let c0 : Real := 4 * Real.pi ^ 2 * shortestVectorLength (knDualLattice Λ) ^ 2
  have hc0pos : 0 < c0 := by
    dsimp [c0]
    have hNpos := dual_shortestVectorLength_pos hn Λ
    positivity
  have hpartial :
      ∀ F : Finset (Fin n -> Int),
        (∑ i ∈ E, ∑ k ∈ F,
          ‖UnitAddTorus.mFourierCoeff (φ i) k‖ ^ 2) ≤
          (n : Real) * L ^ 2 / c0 := by
    intro F
    let Fnz : Finset (Fin n -> Int) := F.erase 0
    have hFnz : ∀ k ∈ Fnz, k ≠ 0 := by
      intro k hk
      exact (Finset.mem_erase.mp hk).1
    have hspectral :=
      flatTorus_finite_spectral_estimate hn Λ b E Fnz g hL hg hgLip
    have hshort :
        c0 * (∑ i ∈ E, ∑ k ∈ Fnz,
            ‖UnitAddTorus.mFourierCoeff (φ i) k‖ ^ 2) ≤
          ∑ i ∈ E, ∑ k ∈ Fnz,
            (4 * Real.pi ^ 2 * ‖dualVectorOfFrequency Λ k‖ ^ 2) *
              ‖UnitAddTorus.mFourierCoeff (φ i) k‖ ^ 2 := by
      calc
        c0 * (∑ i ∈ E, ∑ k ∈ Fnz,
            ‖UnitAddTorus.mFourierCoeff (φ i) k‖ ^ 2) =
            ∑ i ∈ E, ∑ k ∈ Fnz,
              c0 * ‖UnitAddTorus.mFourierCoeff (φ i) k‖ ^ 2 := by
              simp [Finset.mul_sum]
        _ ≤ ∑ i ∈ E, ∑ k ∈ Fnz,
            (4 * Real.pi ^ 2 * ‖dualVectorOfFrequency Λ k‖ ^ 2) *
              ‖UnitAddTorus.mFourierCoeff (φ i) k‖ ^ 2 := by
              refine Finset.sum_le_sum ?_
              intro i _hi
              simpa [c0] using
                finset_sum_shortest_weighted_le_dualVector_weighted hn Λ Fnz
                  (fun k => ‖UnitAddTorus.mFourierCoeff (φ i) k‖ ^ 2)
                  (fun k => sq_nonneg _) hFnz
    have hFnz_bound :
        (∑ i ∈ E, ∑ k ∈ Fnz,
          ‖UnitAddTorus.mFourierCoeff (φ i) k‖ ^ 2) ≤
          (n : Real) * L ^ 2 / c0 := by
      rw [mul_comm] at hshort
      exact (le_div_iff₀ hc0pos).2 (hshort.trans (by simpa [φ] using hspectral))
    have hErase :
        (∑ i ∈ E, ∑ k ∈ F,
          ‖UnitAddTorus.mFourierCoeff (φ i) k‖ ^ 2) =
          ∑ i ∈ E, ∑ k ∈ Fnz,
            ‖UnitAddTorus.mFourierCoeff (φ i) k‖ ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      symm
      refine Finset.sum_subset (Finset.erase_subset 0 F) ?_
      intro k hkF hknot
      have hk0 : k = 0 := by
        by_contra hkne
        exact hknot (Finset.mem_erase.mpr ⟨hkne, hkF⟩)
      simp [hk0, hzero i]
    simpa [hErase] using hFnz_bound
  have hparse :
      Filter.Tendsto
        (fun F : Finset (Fin n -> Int) =>
          ∑ k ∈ F, ∑ i ∈ E,
            ‖UnitAddTorus.mFourierCoeff (φ i) k‖ ^ 2)
        Filter.atTop
        (𝓝 (∑ i ∈ E,
          ∫ z : UnitAddTorus (Fin n), ‖φ i z‖ ^ 2
            ∂(volume : Measure (UnitAddTorus (Fin n))))) := by
    have hparse' :
        Filter.Tendsto
          (fun F : Finset (Fin n -> Int) =>
            ∑ i ∈ E, ∑ k ∈ F,
              ‖UnitAddTorus.mFourierCoeff (φ i) k‖ ^ 2)
          Filter.atTop
          (𝓝 (∑ i ∈ E,
            ∫ z : UnitAddTorus (Fin n), ‖φ i z‖ ^ 2
              ∂(volume : Measure (UnitAddTorus (Fin n))))) := by
      exact tendsto_finsetSum E fun i _hi =>
        unitAddTorus_hasSum_sq_mFourierCoeff (φ i)
    refine hparse'.congr' (Filter.Eventually.of_forall ?_)
    intro F
    rw [Finset.sum_comm]
  have hunit :
      (∑ i ∈ E,
        ∫ z : UnitAddTorus (Fin n), ‖φ i z‖ ^ 2
          ∂(volume : Measure (UnitAddTorus (Fin n)))) ≤
        (n : Real) * L ^ 2 / c0 := by
    exact le_of_tendsto hparse (Filter.Eventually.of_forall fun F => by
      have hF := hpartial F
      rw [Finset.sum_comm] at hF
      exact hF)
  have hflat_eq_unit :
      (∫ x,
          ∑ i ∈ E, ‖b.repr (g x) i‖ ^ 2
          ∂torusHaarMeasure Λ) =
        ∑ i ∈ E,
          ∫ z : UnitAddTorus (Fin n), ‖φ i z‖ ^ 2
            ∂(volume : Measure (UnitAddTorus (Fin n))) := by
    have htransfer :=
      integral_flatTorus_eq_integral_unitTorus Λ
        (fun x : Λ.torus => ∑ i ∈ E, ‖b.repr (g x) i‖ ^ 2)
    rw [htransfer]
    have hint :
        ∀ i ∈ E,
          Integrable (fun z : UnitAddTorus (Fin n) => ‖φ i z‖ ^ 2)
            (volume : Measure (UnitAddTorus (Fin n))) := by
      intro i _hi
      exact (by fun_prop : Continuous (fun z : UnitAddTorus (Fin n) => ‖φ i z‖ ^ 2))
        |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    calc
      (∫ z : UnitAddTorus (Fin n),
          (fun x : Λ.torus => ∑ i ∈ E, ‖b.repr (g x) i‖ ^ 2)
            ((coordinateTorusAddEquivUnitAddTorus n).symm z)
          ∂(volume : Measure (UnitAddTorus (Fin n)))) =
          ∫ z : UnitAddTorus (Fin n), ∑ i ∈ E, ‖φ i z‖ ^ 2
            ∂(volume : Measure (UnitAddTorus (Fin n))) := by
            apply integral_congr_ae
            refine ae_of_all _ ?_
            intro z
            refine Finset.sum_congr rfl ?_
            intro i _hi
            simp [φ, flatTorusHilbertCoordinateOnUnitTorus, g]
      _ = ∑ i ∈ E,
          ∫ z : UnitAddTorus (Fin n), ‖φ i z‖ ^ 2
            ∂(volume : Measure (UnitAddTorus (Fin n))) := by
            exact MeasureTheory.integral_finsetSum E hint
  calc
    (∫ x,
        ∑ i ∈ E,
          ‖b.repr (f x - (∫ y, f y ∂torusHaarMeasure Λ)) i‖ ^ 2
        ∂torusHaarMeasure Λ) =
        ∫ x, ∑ i ∈ E, ‖b.repr (g x) i‖ ^ 2 ∂torusHaarMeasure Λ := by
          simp [g, mean]
    _ = ∑ i ∈ E,
          ∫ z : UnitAddTorus (Fin n), ‖φ i z‖ ^ 2
            ∂(volume : Measure (UnitAddTorus (Fin n))) := hflat_eq_unit
    _ ≤ (n : Real) * L ^ 2 / c0 := hunit
    _ = (n : Real) * L ^ 2 /
        (4 * Real.pi ^ 2 * shortestVectorLength (knDualLattice Λ) ^ 2) := rfl

private theorem flatTorus_hilbert_variance_poincare
    {n : Nat} (hn : 1 ≤ n) (Λ : KNFullRankLattice n)
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
    (f : Λ.torus -> H) {L : Real} (hL : 0 ≤ L)
    (hfLip :
      letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
      ∀ x y : Λ.torus, ‖f x - f y‖ ≤ L * dist x y) :
    letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
    letI : MeasurableSpace Λ.torus := borel Λ.torus
    (∫ x, ‖f x - (∫ y, f y ∂torusHaarMeasure Λ)‖ ^ 2
        ∂torusHaarMeasure Λ) ≤
      (n : Real) * L ^ 2 /
        (4 * Real.pi ^ 2 * shortestVectorLength (knDualLattice Λ) ^ 2) := by
  classical
  letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
  letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
  letI : MeasurableSpace Λ.torus := borel Λ.torus
  haveI : CompactSpace Λ.torus := Λ.torus_compactSpace
  letI : BorelSpace Λ.torus := ⟨rfl⟩
  haveI : MeasureTheory.IsProbabilityMeasure (torusHaarMeasure Λ) :=
    torusHaarMeasure_isProbability Λ
  have hFinite : IsFiniteMeasure (torusHaarMeasure Λ) := by infer_instance
  letI : IsFiniteMeasure (torusHaarMeasure Λ) := hFinite
  obtain ⟨ι, b, _hb⟩ := exists_hilbertBasis (𝕜 := Real) (E := H)
  let mean : H := ∫ y, f y ∂torusHaarMeasure Λ
  let g : Λ.torus -> H := fun x => f x - mean
  have hf_metric :
      letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
      Continuous f := continuous_of_flatTorus_lipschitz_bound Λ f hL hfLip
  have hf : Continuous f := by
    simpa [KNFullRankLattice.torusSeminormedAddCommGroup, KNFullRankLattice.torusMetric] using
      hf_metric
  have hg : Continuous g := hf.sub continuous_const
  have hfin :
      ∀ s : Finset ι,
        (∫ x, ∑ i ∈ s, ‖b.repr (g x) i‖ ^ 2 ∂torusHaarMeasure Λ) ≤
          (n : Real) * L ^ 2 /
            (4 * Real.pi ^ 2 * shortestVectorLength (knDualLattice Λ) ^ 2) := by
    intro s
    simpa [g, mean] using
      flatTorus_finite_coordinate_variance_le hn Λ b s f hL hf hfLip
  have hmain :
      (∫ x, ‖g x‖ ^ 2 ∂torusHaarMeasure Λ) ≤
        (n : Real) * L ^ 2 /
          (4 * Real.pi ^ 2 * shortestVectorLength (knDualLattice Λ) ^ 2) :=
    @hilbertBasis_integral_norm_sq_le_of_finset_integral_le
      Λ.torus inferInstance inferInstance (borel Λ.torus) (⟨rfl⟩ : BorelSpace Λ.torus)
      (torusHaarMeasure Λ) hFinite (torusHaarMeasure_isProbability Λ)
      ι H inferInstance inferInstance inferInstance b g hg
      ((n : Real) * L ^ 2 /
        (4 * Real.pi ^ 2 * shortestVectorLength (knDualLattice Λ) ^ 2))
      hfin
  simpa [g, mean] using hmain

private lemma pairwise_energy_eq_two_variance_compactSpace
    {X : Type u} [PseudoMetricSpace X] [CompactSpace X] [MeasurableSpace X]
    (hB : BorelSpace X)
    {μ : Measure X} (hFinite : IsFiniteMeasure μ) (hProb : IsProbabilityMeasure μ)
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
    {f : X -> H} (hf : Continuous f) :
    (∫ x, ∫ y, ‖f x - f y‖ ^ 2 ∂μ ∂μ) =
      2 * ∫ x, ‖f x - (∫ y, f y ∂μ)‖ ^ 2 ∂μ := by
  letI : BorelSpace X := hB
  letI : IsFiniteMeasure μ := hFinite
  letI : IsProbabilityMeasure μ := hProb
  let mean : H := ∫ y, f y ∂μ
  let g : X -> H := fun x => f x - mean
  have hfInt : Integrable f μ := by
    exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have hgInt : Integrable g μ := hfInt.sub (integrable_const (c := mean))
  have hg : Continuous g := hf.sub continuous_const
  have hμuniv : μ.real Set.univ = 1 := by
    simp [Measure.real]
  have hgMean : (∫ x, g x ∂μ) = 0 := by
    calc
      (∫ x, g x ∂μ) = (∫ x, f x - mean ∂μ) := rfl
      _ = (∫ x, f x ∂μ) - (∫ _x : X, mean ∂μ) := by
            rw [integral_sub hfInt (integrable_const (c := mean))]
      _ = mean - μ.real Set.univ • mean := by
            rw [integral_const]
      _ = 0 := by
            simp [mean, hμuniv]
  have hvarInt : Integrable (fun x : X => ‖g x‖ ^ 2) μ := by
    exact integrable_of_continuous_compactSpace (μ := μ) (by fun_prop)
  have hfiber :
      ∀ x : X, (∫ y, ‖f x - f y‖ ^ 2 ∂μ) =
        ‖g x‖ ^ 2 + ∫ y, ‖g y‖ ^ 2 ∂μ := by
    intro x
    have hAInt : Integrable (fun _y : X => ‖g x‖ ^ 2) μ := integrable_const _
    have hBInt : Integrable (fun y : X => 2 * inner Real (g x) (g y)) μ := by
      exact integrable_of_continuous_compactSpace (μ := μ) (by fun_prop)
    have hCInt : Integrable (fun y : X => ‖g y‖ ^ 2) μ := hvarInt
    calc
      (∫ y, ‖f x - f y‖ ^ 2 ∂μ) =
          ∫ y, ‖g x - g y‖ ^ 2 ∂μ := by
            apply integral_congr_ae
            refine ae_of_all _ ?_
            intro y
            change ‖f x - f y‖ ^ 2 = ‖g x - g y‖ ^ 2
            have hsub : f x - f y = g x - g y := by
              simp [g, mean, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
            rw [hsub]
      _ = ∫ y, (‖g x‖ ^ 2 - 2 * inner Real (g x) (g y) + ‖g y‖ ^ 2) ∂μ := by
            apply integral_congr_ae
            refine ae_of_all _ ?_
            intro y
            change ‖g x - g y‖ ^ 2 =
              ‖g x‖ ^ 2 - 2 * inner Real (g x) (g y) + ‖g y‖ ^ 2
            rw [norm_sub_sq_real]
      _ = (∫ _y : X, ‖g x‖ ^ 2 ∂μ) -
            ∫ y, 2 * inner Real (g x) (g y) ∂μ + ∫ y, ‖g y‖ ^ 2 ∂μ := by
            change (∫ y, (((fun _y : X => ‖g x‖ ^ 2) -
                fun y : X => 2 * inner Real (g x) (g y)) y +
                (fun y : X => ‖g y‖ ^ 2) y) ∂μ) = _
            rw [integral_add (hAInt.sub hBInt) hCInt]
            exact congrArg (fun r : Real => r + ∫ y, ‖g y‖ ^ 2 ∂μ)
              (integral_sub hAInt hBInt)
      _ = μ.real Set.univ * ‖g x‖ ^ 2 -
            2 * inner Real (g x) (∫ y, g y ∂μ) + ∫ y, ‖g y‖ ^ 2 ∂μ := by
            rw [integral_const]
            simp [smul_eq_mul, integral_const_mul, integral_inner hgInt]
      _ = ‖g x‖ ^ 2 + ∫ y, ‖g y‖ ^ 2 ∂μ := by
            simp [hμuniv, hgMean]
  calc
    (∫ x, ∫ y, ‖f x - f y‖ ^ 2 ∂μ ∂μ) =
        ∫ x, (‖g x‖ ^ 2 + ∫ y, ‖g y‖ ^ 2 ∂μ) ∂μ := by
          apply integral_congr_ae
          exact ae_of_all _ hfiber
    _ = (∫ x, ‖g x‖ ^ 2 ∂μ) +
          ∫ _x : X, (∫ y, ‖g y‖ ^ 2 ∂μ) ∂μ := by
          rw [integral_add hvarInt (integrable_const _)]
    _ = (∫ x, ‖g x‖ ^ 2 ∂μ) + ∫ y, ‖g y‖ ^ 2 ∂μ := by
          rw [integral_const]
          simp [hμuniv, smul_eq_mul]
    _ = 2 * ∫ x, ‖g x‖ ^ 2 ∂μ := by ring
    _ = 2 * ∫ x, ‖f x - (∫ y, f y ∂μ)‖ ^ 2 ∂μ := by rfl

private theorem flatTorus_pairwise_energy_eq_two_variance
    {n : Nat} (Λ : KNFullRankLattice n)
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
    (f : Λ.torus -> H)
    (hf :
      letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
      Continuous f) :
    letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
    letI : MeasurableSpace Λ.torus := borel Λ.torus
    (∫ x, ∫ y, ‖f x - f y‖ ^ 2
        ∂torusHaarMeasure Λ ∂torusHaarMeasure Λ) =
      2 * ∫ x, ‖f x - (∫ y, f y ∂torusHaarMeasure Λ)‖ ^ 2
        ∂torusHaarMeasure Λ := by
  letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
  letI : MeasurableSpace Λ.torus := borel Λ.torus
  haveI : CompactSpace Λ.torus := Λ.torus_compactSpace
  haveI : BorelSpace Λ.torus := ⟨rfl⟩
  haveI : MeasureTheory.IsProbabilityMeasure (torusHaarMeasure Λ) :=
    torusHaarMeasure_isProbability Λ
  have hFinite : IsFiniteMeasure (torusHaarMeasure Λ) := by infer_instance
  letI : IsFiniteMeasure (torusHaarMeasure Λ) := hFinite
  exact pairwise_energy_eq_two_variance_compactSpace
    (X := Λ.torus) (μ := torusHaarMeasure Λ) (f := f)
    (hB := (⟨rfl⟩ : BorelSpace Λ.torus))
    (hFinite := hFinite) (hProb := torusHaarMeasure_isProbability Λ) hf

private theorem flatTorus_hilbert_poincare
    {n : Nat} (hn : 1 ≤ n) (Λ : KNFullRankLattice n)
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
    (f : Λ.torus -> H) {L : Real} (hL : 0 ≤ L)
    (hfLip :
      letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
      ∀ x y : Λ.torus, ‖f x - f y‖ ≤ L * dist x y) :
    letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
    letI : MeasurableSpace Λ.torus := borel Λ.torus
    (∫ x, ∫ y, ‖f x - f y‖ ^ 2
        ∂torusHaarMeasure Λ ∂torusHaarMeasure Λ) ≤
      (n : Real) * L ^ 2 /
        (2 * Real.pi ^ 2 * shortestVectorLength (knDualLattice Λ) ^ 2) := by
  letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
  letI : MeasurableSpace Λ.torus := borel Λ.torus
  have hf : Continuous f := continuous_of_flatTorus_lipschitz_bound Λ f hL hfLip
  have hpair := flatTorus_pairwise_energy_eq_two_variance Λ f hf
  have hvar := flatTorus_hilbert_variance_poincare hn Λ f hL hfLip
  calc
    (∫ x, ∫ y, ‖f x - f y‖ ^ 2 ∂torusHaarMeasure Λ ∂torusHaarMeasure Λ) =
        2 * ∫ x, ‖f x - (∫ y, f y ∂torusHaarMeasure Λ)‖ ^ 2
          ∂torusHaarMeasure Λ := hpair
    _ ≤ 2 *
        ((n : Real) * L ^ 2 /
          (4 * Real.pi ^ 2 * shortestVectorLength (knDualLattice Λ) ^ 2)) := by
        exact mul_le_mul_of_nonneg_left hvar (by norm_num)
    _ = (n : Real) * L ^ 2 /
        (2 * Real.pi ^ 2 * shortestVectorLength (knDualLattice Λ) ^ 2) := by
        ring

private lemma integral_ge_const_mul_measureReal_of_ge_on
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {s : Set X} (hs : MeasurableSet s) {φ : X -> Real} (hφInt : Integrable φ μ)
    (hφ_nonneg : ∀ x, 0 ≤ φ x) {a : Real} (_ha : 0 ≤ a)
    (hge : ∀ x ∈ s, a ≤ φ x) :
    μ.real s * a ≤ ∫ x, φ x ∂μ := by
  have hconstInt : IntegrableOn (fun _ : X => a) s μ :=
    integrableOn_const (μ := μ) (s := s) (C := a)
  have hφIntOn : IntegrableOn φ s μ := hφInt.integrableOn
  have hset : (∫ x in s, (fun _ : X => a) x ∂μ) ≤ ∫ x in s, φ x ∂μ := by
    exact setIntegral_mono_on hconstInt hφIntOn hs hge
  have hset_le : (∫ x in s, φ x ∂μ) ≤ ∫ x, φ x ∂μ := by
    exact setIntegral_le_integral hφInt (ae_of_all μ hφ_nonneg)
  calc
    μ.real s * a = ∫ x in s, (fun _ : X => a) x ∂μ := by
      rw [setIntegral_const]
      simp [smul_eq_mul]
    _ ≤ ∫ x in s, φ x ∂μ := hset
    _ ≤ ∫ x, φ x ∂μ := hset_le

private lemma integral_ge_const_mul_of_measureReal_ge
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {s : Set X} (hs : MeasurableSet s) {φ : X -> Real} (hφInt : Integrable φ μ)
    (hφ_nonneg : ∀ x, 0 ≤ φ x) {a c : Real} (ha : 0 ≤ a) (hc : c ≤ μ.real s)
    (hge : ∀ x ∈ s, a ≤ φ x) :
    c * a ≤ ∫ x, φ x ∂μ := by
  exact (mul_le_mul_of_nonneg_right hc ha).trans
    (integral_ge_const_mul_measureReal_of_ge_on hs hφInt hφ_nonneg ha hge)

private lemma integral_dist_zero_sq_ge_of_measureReal_large_set
    {X : Type*} [PseudoMetricSpace X] [Zero X] [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {s : Set X} (hs : MeasurableSet s)
    (hInt : Integrable (fun z : X => dist z 0 ^ 2) μ) {a c : Real} (ha : 0 ≤ a)
    (hc : c ≤ μ.real s) (hlarge : ∀ z ∈ s, a ≤ dist z 0) :
    c * a ^ 2 ≤ ∫ z, dist z 0 ^ 2 ∂μ := by
  refine integral_ge_const_mul_of_measureReal_ge hs hInt (fun z => sq_nonneg (dist z 0))
    (sq_nonneg a) hc ?_
  intro z hz
  have hdz_nonneg : 0 ≤ dist z 0 := dist_nonneg
  have hle := hlarge z hz
  nlinarith [mul_nonneg (sub_nonneg.mpr hle) (add_nonneg hdz_nonneg ha)]

private lemma measureReal_univ_eq_one_of_probability
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ] :
    μ.real Set.univ = 1 := by
  simp [Measure.real]

private lemma measureReal_compl_ge_of_measureReal_le
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    [IsProbabilityMeasure μ] {s : Set X} (hs : MeasurableSet s) {p c : Real}
    (hp : μ.real s ≤ p) (hc : c ≤ 1 - p) :
    c ≤ μ.real sᶜ := by
  rw [measureReal_compl hs]
  have huniv : μ.real Set.univ = 1 := measureReal_univ_eq_one_of_probability
  linarith

private noncomputable def EuclideanUnitBallVolume (n : Nat) : Real :=
  (volume (Metric.ball (0 : RealEuclideanSpace n) 1)).toReal

private lemma EuclideanUnitBallVolume_nonneg (n : Nat) :
    0 ≤ EuclideanUnitBallVolume n :=
  ENNReal.toReal_nonneg

private lemma EuclideanUnitBallVolume_pos (n : Nat) :
    0 < EuclideanUnitBallVolume n := by
  unfold EuclideanUnitBallVolume
  have hpos :
      0 < (volume : Measure (RealEuclideanSpace n))
        (Metric.ball (0 : RealEuclideanSpace n) 1) :=
    Metric.measure_ball_pos (volume : Measure (RealEuclideanSpace n))
      (0 : RealEuclideanSpace n) zero_lt_one
  exact ENNReal.toReal_pos (ne_of_gt hpos) measure_ball_ne_top

private lemma volume_closedBall_toReal_eq_unitBall_mul_pow
    (n : Nat) {s : Real} (hs : 0 ≤ s) :
    (volume (Metric.closedBall (0 : RealEuclideanSpace n) s)).toReal =
      EuclideanUnitBallVolume n * s ^ n := by
  have h :=
    Measure.addHaar_real_closedBall (μ := (volume : Measure (RealEuclideanSpace n)))
      (x := (0 : RealEuclideanSpace n)) hs
  simpa [EuclideanUnitBallVolume, Measure.real, RealEuclideanSpace, mul_comm] using h

private lemma volume_ball_toReal_le_unitBall_mul_pow
    (n : Nat) {s : Real} (hs : 0 ≤ s) :
    (volume (Metric.ball (0 : RealEuclideanSpace n) s)).toReal ≤
      EuclideanUnitBallVolume n * s ^ n := by
  have hle :
      (volume (Metric.ball (0 : RealEuclideanSpace n) s)).toReal ≤
        (volume (Metric.closedBall (0 : RealEuclideanSpace n) s)).toReal :=
    ENNReal.toReal_mono measure_closedBall_lt_top.ne
      (measure_mono (fun _ hx => Metric.ball_subset_closedBall hx))
  have hclosed := volume_closedBall_toReal_eq_unitBall_mul_pow n hs
  simpa [hclosed] using hle

private theorem volume_preimage_matrix_ball_le
    {n : Nat} (Λ : KNFullRankLattice n) {s : Real} (hs : 0 ≤ s) :
    (volume {x : RealEuclideanSpace n |
      ‖Matrix.toEuclideanLin Λ.basis.matrix x‖ < s}).toReal ≤
      EuclideanUnitBallVolume n * s ^ n / Λ.det := by
  let B : Set (RealEuclideanSpace n) := Metric.ball (0 : RealEuclideanSpace n) s
  have hset :
      {x : RealEuclideanSpace n | ‖Matrix.toEuclideanLin Λ.basis.matrix x‖ < s} =
        (Matrix.toEuclideanLin Λ.basis.matrix) ⁻¹' B := by
    ext x
    simp [B, Metric.mem_ball, dist_eq_norm]
  have hpre :
      (volume ((Matrix.toEuclideanLin Λ.basis.matrix) ⁻¹' B)).toReal =
        (volume B).toReal / Λ.det := by
    have hvol := volume_preimage_matrix_toEuclideanLin Λ (S := B)
    rw [hvol, ENNReal.toReal_mul, ENNReal.toReal_ofReal]
    · field_simp [ne_of_gt (KNFullRankLattice.det_pos Λ)]
    · exact inv_nonneg.mpr (KNFullRankLattice.det_pos Λ).le
  have hball := volume_ball_toReal_le_unitBall_mul_pow n hs
  have hdet_nonneg : 0 ≤ Λ.det := (KNFullRankLattice.det_pos Λ).le
  rw [hset, hpre]
  exact div_le_div_of_nonneg_right (by simpa [B] using hball) hdet_nonneg

private lemma distanceToLattice_le_coveringRadius {n : Nat}
    (Λ : KNFullRankLattice n) (x : RealEuclideanSpace n) :
    distanceToLattice Λ x ≤ coveringRadius Λ := by
  unfold coveringRadius
  exact le_csSup (distanceToLattice_range_bddAbove Λ) (Set.mem_range_self x)

private lemma flatTorus_matrix_preimage_closedBall_image_eq_univ_of_coveringRadius_le
    {n : Nat} (Λ : KNFullRankLattice n) {s : Real}
    (hs : coveringRadius Λ ≤ s) :
    (QuotientAddGroup.mk' (integerLattice n) ''
      ((Matrix.toEuclideanLin Λ.basis.matrix) ⁻¹'
        Metric.closedBall (0 : RealEuclideanSpace n) s) : Set Λ.torus) =
      Set.univ := by
  ext z
  constructor
  · intro _hz
    trivial
  · intro _hz
    refine QuotientAddGroup.induction_on z ?_
    intro x
    let y : RealEuclideanSpace n := Matrix.toEuclideanLin Λ.basis.matrix x
    obtain ⟨γ, hγ, hγdist⟩ := nearest_lattice_vector_attained Λ y
    have hdist_le : ‖y - γ‖ ≤ s := by
      rw [← hγdist]
      exact (distanceToLattice_le_coveringRadius Λ y).trans hs
    change γ ∈ matrixIntegerLattice n Λ.basis at hγ
    simp [matrixIntegerLattice, integerLattice] at hγ
    rcases hγ with ⟨k, rfl⟩
    let u : RealEuclideanSpace n := x - integerVector n k
    refine ⟨u, ?_, ?_⟩
    · dsimp [u, y]
      simpa [Metric.mem_closedBall, dist_eq_norm, map_sub] using hdist_le
    · change (QuotientAddGroup.mk' (integerLattice n) u :
          RealEuclideanSpace n ⧸ integerLattice n) =
        QuotientAddGroup.mk' (integerLattice n) x
      rw [QuotientAddGroup.mk'_eq_mk']
      refine ⟨integerVector n k, ?_, ?_⟩
      · exact ⟨k, rfl⟩
      · dsimp [u]
        abel

private theorem det_le_coveringRadius_pow_mul_ballVolume
    {n : Nat} (Λ : KNFullRankLattice n) :
    Λ.det ≤ coveringRadius Λ ^ n * EuclideanUnitBallVolume n := by
  classical
  letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
  letI : MeasurableSpace Λ.torus := borel Λ.torus
  haveI : MeasureTheory.IsProbabilityMeasure (torusHaarMeasure Λ) :=
    torusHaarMeasure_isProbability Λ
  let R : Real := coveringRadius Λ
  let S : Set (RealEuclideanSpace n) := Metric.closedBall (0 : RealEuclideanSpace n) R
  have hRnonneg : 0 ≤ R := by
    simpa [R] using (coveringRadius_finite_attained Λ).1
  have himage :
      (QuotientAddGroup.mk' (integerLattice n) ''
        ((Matrix.toEuclideanLin Λ.basis.matrix) ⁻¹' S) : Set Λ.torus) =
        Set.univ := by
    simpa [S, R] using
      flatTorus_matrix_preimage_closedBall_image_eq_univ_of_coveringRadius_le Λ
        (le_rfl : coveringRadius Λ ≤ coveringRadius Λ)
  have hbound :=
    flatTorus_matrix_preimage_quotient_image_measureReal_le_volume_div_det Λ
      (S := S) measurableSet_closedBall measure_closedBall_lt_top.ne
  have hleft :
      (torusHaarMeasure Λ).real
        (QuotientAddGroup.mk' (integerLattice n) ''
          ((Matrix.toEuclideanLin Λ.basis.matrix) ⁻¹' S) : Set Λ.torus) = 1 := by
    rw [himage]
    exact measureReal_univ_eq_one_of_probability (μ := torusHaarMeasure Λ)
  have hle : 1 ≤ (volume S).toReal / Λ.det := by
    rw [hleft] at hbound
    exact hbound
  have hdet_pos : 0 < Λ.det := KNFullRankLattice.det_pos Λ
  have hmul := mul_le_mul_of_nonneg_right hle hdet_pos.le
  have hvol := volume_closedBall_toReal_eq_unitBall_mul_pow n hRnonneg
  field_simp [hdet_pos.ne'] at hmul
  rw [hvol] at hmul
  nlinarith

private theorem dual_det_le_coveringRadius_pow_mul_ballVolume
    {n : Nat} (_hn : 1 ≤ n) (Λ : KNFullRankLattice n) :
    (knDualLattice Λ).det ≤
      coveringRadius (knDualLattice Λ) ^ n * EuclideanUnitBallVolume n :=
  det_le_coveringRadius_pow_mul_ballVolume (knDualLattice Λ)

private theorem det_lower_from_dual_coveringRadius
    {n : Nat} (hn : 1 ≤ n) (Λ : KNFullRankLattice n) :
    1 / (coveringRadius (knDualLattice Λ) ^ n * EuclideanUnitBallVolume n) ≤
      Λ.det := by
  have hdual := dual_det_le_coveringRadius_pow_mul_ballVolume hn Λ
  have hdual_pos : 0 < (knDualLattice Λ).det :=
    KNFullRankLattice.det_pos (knDualLattice Λ)
  have hrecip :
      1 / (coveringRadius (knDualLattice Λ) ^ n * EuclideanUnitBallVolume n) ≤
        1 / (knDualLattice Λ).det :=
    one_div_le_one_div_of_le hdual_pos hdual
  have hdet_eq : 1 / (knDualLattice Λ).det = Λ.det := by
    rw [one_div]
    exact (eq_inv_of_mul_eq_one_left (knDet_mul_dualDet Λ)).symm
  simpa [hdet_eq] using hrecip

private lemma one_div_eight_pow_le_one_div_eight
    {n : Nat} (hn : 1 ≤ n) :
    (1 / 8 : Real) ^ n ≤ 1 / 8 := by
  cases n with
  | zero => omega
  | succ k =>
      have hpow : (1 / 8 : Real) ^ k ≤ 1 :=
        pow_le_one₀ (by norm_num) (by norm_num)
      calc
        (1 / 8 : Real) ^ (k + 1) = (1 / 8 : Real) ^ k * (1 / 8 : Real) := by
          rw [pow_succ]
        _ ≤ 1 * (1 / 8 : Real) := mul_le_mul_of_nonneg_right hpow (by norm_num)
        _ = 1 / 8 := by ring

private lemma EuclideanUnitBallVolume_sq_mul_scaled_radius_pow_le
    {n : Nat} (hn : 1 ≤ n) :
    EuclideanUnitBallVolume n ^ 2 *
        ((n : Real) / (16 * Real.pi * Real.exp 1)) ^ n ≤
      (1 / 8 : Real) ^ n := by
  classical
  let b : Real := (n : Real) / 2
  let a : Real := Real.pi / b
  let A : Real := a ^ ((n : Real) / 2)
  have hnpos : 0 < (n : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hbpos : 0 < b := by
    dsimp [b]
    positivity
  have hapos : 0 < a := by
    dsimp [a]
    positivity
  let φ : RealEuclideanSpace n -> Real := fun x => Real.exp (-b * ‖x‖ ^ 2)
  have hφInt : Integrable φ (volume : Measure (RealEuclideanSpace n)) := by
    have hIntC :
        Integrable
          (fun x : RealEuclideanSpace n =>
            Complex.exp (-(b : Complex) * (‖x‖ : Complex) ^ 2 +
              (0 : Complex) * inner ℝ (0 : RealEuclideanSpace n) x)) :=
      GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
        (V := RealEuclideanSpace n) (b := (b : Complex)) (c := 0)
        (w := (0 : RealEuclideanSpace n)) (by simpa using hbpos)
    have hRe := hIntC.re
    convert hRe using 1
    ext x
    dsimp [φ]
    rw [show -↑b * (↑‖x‖ : Complex) ^ 2 + 0 * ↑(inner ℝ 0 x) =
        ((-b * ‖x‖ ^ 2 : Real) : Complex) by
      simp [Complex.ofReal_mul, Complex.ofReal_pow]]
    exact (Complex.exp_ofReal_re (-b * ‖x‖ ^ 2)).symm
  let B : Set (RealEuclideanSpace n) := Metric.ball (0 : RealEuclideanSpace n) 1
  have hφLower :
      ∀ x ∈ B, Real.exp (-b) ≤ φ x := by
    intro x hx
    have hxnorm : ‖x‖ < 1 := by
      simpa [B, Metric.mem_ball, dist_eq_norm] using hx
    have hxnorm_sq : ‖x‖ ^ 2 ≤ 1 := by
      have hxnorm_le : ‖x‖ ≤ 1 := hxnorm.le
      have hprod :=
        mul_nonneg (sub_nonneg.mpr hxnorm_le) (add_nonneg (norm_nonneg x) zero_le_one)
      nlinarith
    have hmul : -b ≤ -b * ‖x‖ ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hxnorm_sq hbpos.le]
    exact Real.exp_le_exp.mpr hmul
  have hgaussLower :
      EuclideanUnitBallVolume n * Real.exp (-b) ≤
        ∫ x, φ x ∂(volume : Measure (RealEuclideanSpace n)) := by
    have hconstInt :
        IntegrableOn (fun _ : RealEuclideanSpace n => Real.exp (-b)) B
          (volume : Measure (RealEuclideanSpace n)) :=
      integrableOn_const
        (μ := (volume : Measure (RealEuclideanSpace n))) (s := B)
        (C := Real.exp (-b)) (by simpa [B] using measure_ball_ne_top)
    have hφIntOn : IntegrableOn φ B (volume : Measure (RealEuclideanSpace n)) :=
      hφInt.integrableOn
    have hset :
        (∫ x in B, (fun _ : RealEuclideanSpace n => Real.exp (-b)) x
            ∂(volume : Measure (RealEuclideanSpace n))) ≤
          ∫ x in B, φ x ∂(volume : Measure (RealEuclideanSpace n)) :=
      setIntegral_mono_on hconstInt hφIntOn measurableSet_ball hφLower
    have hset_le :
        (∫ x in B, φ x ∂(volume : Measure (RealEuclideanSpace n))) ≤
          ∫ x, φ x ∂(volume : Measure (RealEuclideanSpace n)) :=
      setIntegral_le_integral hφInt (ae_of_all _ fun x => Real.exp_nonneg _)
    calc
      EuclideanUnitBallVolume n * Real.exp (-b) =
          ∫ x in B, (fun _ : RealEuclideanSpace n => Real.exp (-b)) x
            ∂(volume : Measure (RealEuclideanSpace n)) := by
            rw [setIntegral_const]
            simp [B, EuclideanUnitBallVolume, Measure.real, smul_eq_mul, mul_comm]
      _ ≤ ∫ x in B, φ x ∂(volume : Measure (RealEuclideanSpace n)) := hset
      _ ≤ ∫ x, φ x ∂(volume : Measure (RealEuclideanSpace n)) := hset_le
  have hgaussEval :
      (∫ x, φ x ∂(volume : Measure (RealEuclideanSpace n))) = A := by
    have h :=
      GaussianFourier.integral_rexp_neg_mul_sq_norm
        (V := RealEuclideanSpace n) (b := b) hbpos
    simpa [φ, A, a, b, RealEuclideanSpace] using h
  have hVle : EuclideanUnitBallVolume n ≤ A / Real.exp (-b) := by
    rw [hgaussEval] at hgaussLower
    exact (le_div_iff₀ (Real.exp_pos _)).mpr hgaussLower
  have hAnonneg : 0 ≤ A := by
    dsimp [A]
    exact Real.rpow_nonneg hapos.le _
  have hVnonneg : 0 ≤ EuclideanUnitBallVolume n := EuclideanUnitBallVolume_nonneg n
  have hV_sq_le : EuclideanUnitBallVolume n ^ 2 ≤ (A / Real.exp (-b)) ^ 2 := by
    have hquot_nonneg : 0 ≤ A / Real.exp (-b) := div_nonneg hAnonneg (Real.exp_pos _).le
    nlinarith [mul_nonneg (sub_nonneg.mpr hVle) (add_nonneg hVnonneg hquot_nonneg)]
  have hA_sq : A ^ 2 = (2 * Real.pi / (n : Real)) ^ n := by
    have ha_nonneg : 0 ≤ a := hapos.le
    have hpow : A ^ 2 = a ^ (n : Real) := by
      dsimp [A]
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha_nonneg]
      ring
    have ha_eq : a = 2 * Real.pi / (n : Real) := by
      dsimp [a, b]
      field_simp [ne_of_gt hnpos]
    rw [hpow, ha_eq, Real.rpow_natCast]
  have hExp_sq : Real.exp (-b) ^ 2 = Real.exp (-(n : Real)) := by
    rw [sq, ← Real.exp_add]
    congr 1
    dsimp [b]
    ring
  have hscale :
      (A / Real.exp (-b)) ^ 2 =
        Real.exp (n : Real) * (2 * Real.pi / (n : Real)) ^ n := by
    rw [div_pow, hA_sq, hExp_sq, Real.exp_neg]
    field_simp [Real.exp_ne_zero]
  have hV_bound :
      EuclideanUnitBallVolume n ^ 2 ≤
        Real.exp (n : Real) * (2 * Real.pi / (n : Real)) ^ n := by
    simpa [hscale] using hV_sq_le
  calc
    EuclideanUnitBallVolume n ^ 2 *
        ((n : Real) / (16 * Real.pi * Real.exp 1)) ^ n
        ≤ (Real.exp (n : Real) * (2 * Real.pi / (n : Real)) ^ n) *
            ((n : Real) / (16 * Real.pi * Real.exp 1)) ^ n := by
          exact mul_le_mul_of_nonneg_right hV_bound (by positivity)
    _ = (1 / 8 : Real) ^ n := by
          have hexp : Real.exp (n : Real) = Real.exp 1 ^ n := by
            simpa [mul_comm] using (Real.exp_nat_mul 1 n)
          have hbase :
              Real.exp 1 * (2 * Real.pi / (n : Real)) *
                  ((n : Real) / (16 * Real.pi * Real.exp 1)) = (1 / 8 : Real) := by
            field_simp [ne_of_gt hnpos, Real.pi_ne_zero, Real.exp_ne_zero]
            norm_num
          rw [hexp]
          calc
            (Real.exp 1 ^ n * (2 * Real.pi / (n : Real)) ^ n) *
                ((n : Real) / (16 * Real.pi * Real.exp 1)) ^ n =
                (Real.exp 1 * (2 * Real.pi / (n : Real)) *
                  ((n : Real) / (16 * Real.pi * Real.exp 1))) ^ n := by
                  rw [mul_pow, mul_pow]
            _ = (1 / 8 : Real) ^ n := by rw [hbase]

private lemma flatTorus_metric_ball_subset_matrix_preimage_quotient_image
    {n : Nat} (Λ : KNFullRankLattice n) {s : Real} :
    letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
    {z : Λ.torus | dist z 0 < s} ⊆
      QuotientAddGroup.mk' (integerLattice n) ''
        {x : RealEuclideanSpace n | ‖Matrix.toEuclideanLin Λ.basis.matrix x‖ < s} := by
  letI : SeminormedAddCommGroup (RealEuclideanSpace n) :=
    flatTorusAmbientSeminorm n Λ.basis
  letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
  intro z hz
  have hnorm : ‖z‖ < s := by
    simpa [dist_eq_norm] using hz
  have heps : 0 < s - ‖z‖ := sub_pos.mpr hnorm
  obtain ⟨x, hxq, hxnorm⟩ :=
    QuotientAddGroup.exists_norm_mk_lt (S := integerLattice n) z heps
  have hxnorm_s :
      @norm (RealEuclideanSpace n) (flatTorusAmbientSeminorm n Λ.basis).toNorm x < s := by
    have hsum : ‖z‖ + (s - ‖z‖) = s := by ring
    exact lt_of_lt_of_eq hxnorm hsum
  refine ⟨x, ?_, ?_⟩
  · simpa [flatTorusAmbientSeminorm, SeminormedAddCommGroup.induced,
      SeminormedAddGroup.induced] using hxnorm_s
  · simpa [KNFullRankLattice.torus, flatTorus] using hxq

private theorem flatTorus_small_ball_measure_le_one_eighth_semigroup
    {n : Nat} (hn : 1 ≤ n) (Λ : KNFullRankLattice n) :
    letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
    letI : MeasurableSpace Λ.torus := borel Λ.torus
    (torusHaarMeasure Λ).real
      {z : Λ.torus |
        dist z 0 <
          (n : Real) /
            (16 * Real.pi * Real.exp 1 *
              coveringRadius (knDualLattice Λ))} ≤
      (1 / 8 : Real) := by
  classical
  letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
  letI : MeasurableSpace Λ.torus := borel Λ.torus
  let R : Real := coveringRadius (knDualLattice Λ)
  let s : Real := (n : Real) / (16 * Real.pi * Real.exp 1 * R)
  let S : Set (RealEuclideanSpace n) :=
    {x | ‖Matrix.toEuclideanLin Λ.basis.matrix x‖ < s}
  let B : Set Λ.torus := {z | dist z 0 < s}
  have hRpos : 0 < R := by
    simpa [R] using dual_coveringRadius_pos hn Λ
  have hsnonneg : 0 ≤ s := by
    dsimp [s]
    positivity
  have hSmeas : MeasurableSet S := by
    have hcont : Continuous
        (fun x : RealEuclideanSpace n => ‖Matrix.toEuclideanLin Λ.basis.matrix x‖) := by
      fun_prop
    exact (isOpen_lt hcont continuous_const).measurableSet
  have hsubset :
      B ⊆ QuotientAddGroup.mk' (integerLattice n) '' S := by
    simpa [B, S] using
      flatTorus_metric_ball_subset_matrix_preimage_quotient_image Λ (s := s)
  have hmeasure_le :
      (torusHaarMeasure Λ) B ≤ (volume : Measure (RealEuclideanSpace n)) S := by
    exact (measure_mono hsubset).trans (flatTorus_quotient_image_measure_le_volume Λ hSmeas)
  have hS_eq :
      S =
        (Matrix.toEuclideanLin Λ.basis.matrix) ⁻¹'
          Metric.ball (0 : RealEuclideanSpace n) s := by
    ext x
    simp [S, Metric.mem_ball, dist_eq_norm]
  have hSfin : (volume : Measure (RealEuclideanSpace n)) S ≠ ⊤ := by
    have hvol :=
      volume_preimage_matrix_toEuclideanLin Λ
        (S := Metric.ball (0 : RealEuclideanSpace n) s)
    rw [hS_eq, hvol]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_ne_top
  have hreal_le :
      (torusHaarMeasure Λ).real B ≤
        ((volume : Measure (RealEuclideanSpace n)) S).toReal :=
    ENNReal.toReal_mono hSfin hmeasure_le
  have hvol_le :
      ((volume : Measure (RealEuclideanSpace n)) S).toReal ≤
        EuclideanUnitBallVolume n * s ^ n / Λ.det := by
    simpa [S] using volume_preimage_matrix_ball_le Λ hsnonneg
  have hdet_lower :
      1 / (R ^ n * EuclideanUnitBallVolume n) ≤ Λ.det := by
    simpa [R] using det_lower_from_dual_coveringRadius hn Λ
  have hdenpos : 0 < R ^ n * EuclideanUnitBallVolume n := by
    exact mul_pos (pow_pos hRpos n) (EuclideanUnitBallVolume_pos n)
  have hinv_det_le : Λ.det⁻¹ ≤ R ^ n * EuclideanUnitBallVolume n := by
    have hrecip := one_div_le_one_div_of_le (one_div_pos.mpr hdenpos) hdet_lower
    have hrecip_eq : 1 / (1 / (R ^ n * EuclideanUnitBallVolume n)) =
        R ^ n * EuclideanUnitBallVolume n := by
      field_simp [ne_of_gt hdenpos]
    simpa [one_div, hrecip_eq] using hrecip
  have hvol_small :
      EuclideanUnitBallVolume n * s ^ n / Λ.det ≤ (1 / 8 : Real) := by
    have hcoeff_nonneg : 0 ≤ EuclideanUnitBallVolume n * s ^ n := by
      exact mul_nonneg (EuclideanUnitBallVolume_nonneg n) (pow_nonneg hsnonneg n)
    have hcore :
        EuclideanUnitBallVolume n * s ^ n / Λ.det ≤
          EuclideanUnitBallVolume n ^ 2 * (s * R) ^ n := by
      calc
        EuclideanUnitBallVolume n * s ^ n / Λ.det =
            (EuclideanUnitBallVolume n * s ^ n) * Λ.det⁻¹ := by
              ring
        _ ≤ (EuclideanUnitBallVolume n * s ^ n) *
              (R ^ n * EuclideanUnitBallVolume n) :=
            mul_le_mul_of_nonneg_left hinv_det_le hcoeff_nonneg
        _ = EuclideanUnitBallVolume n ^ 2 * (s * R) ^ n := by
            rw [mul_pow]
            ring
    have hsR : s * R = (n : Real) / (16 * Real.pi * Real.exp 1) := by
      dsimp [s]
      field_simp [ne_of_gt hRpos]
    calc
      EuclideanUnitBallVolume n * s ^ n / Λ.det
          ≤ EuclideanUnitBallVolume n ^ 2 * (s * R) ^ n := hcore
      _ = EuclideanUnitBallVolume n ^ 2 *
            ((n : Real) / (16 * Real.pi * Real.exp 1)) ^ n := by
          rw [hsR]
      _ ≤ (1 / 8 : Real) ^ n :=
          EuclideanUnitBallVolume_sq_mul_scaled_radius_pow_le hn
      _ ≤ 1 / 8 := one_div_eight_pow_le_one_div_eight hn
  calc
    (torusHaarMeasure Λ).real
        {z : Λ.torus |
          dist z 0 <
            (n : Real) /
              (16 * Real.pi * Real.exp 1 *
                coveringRadius (knDualLattice Λ))}
        = (torusHaarMeasure Λ).real B := by
          rfl
    _ ≤ ((volume : Measure (RealEuclideanSpace n)) S).toReal := hreal_le
    _ ≤ EuclideanUnitBallVolume n * s ^ n / Λ.det := hvol_le
    _ ≤ 1 / 8 := hvol_small

private theorem flatTorus_small_ball_measure_le_one_eighth
    {n : Nat} (hn : 1 ≤ n) (Λ : KNFullRankLattice n) :
    letI : AddCommGroup Λ.torus := flatTorusAddCommGroup n Λ.basis
    letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
    letI : MeasurableSpace Λ.torus := borel Λ.torus
    (torusHaarMeasure Λ).real
      {z : Λ.torus |
        dist z 0 <
          (n : Real) /
            (16 * Real.pi * Real.exp 1 *
              coveringRadius (knDualLattice Λ))} ≤
      (1 / 8 : Real) := by
  change
    letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
    letI : MeasurableSpace Λ.torus := borel Λ.torus
    (torusHaarMeasure Λ).real
      {z : Λ.torus |
        dist z 0 <
          (n : Real) /
            (16 * Real.pi * Real.exp 1 *
              coveringRadius (knDualLattice Λ))} ≤
      (1 / 8 : Real)
  exact flatTorus_small_ball_measure_le_one_eighth_semigroup hn Λ

private theorem flatTorus_average_distance_sq_lower_of_small_ball
    {n : Nat} (hn : 1 ≤ n) (Λ : KNFullRankLattice n) {s : Real}
    (hs :
      s =
        (n : Real) /
          (16 * Real.pi * Real.exp 1 * coveringRadius (knDualLattice Λ)))
    (hsmall :
      letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
      (torusHaarMeasure Λ).real {z : Λ.torus | dist z 0 < s} ≤ (1 / 8 : Real)) :
    letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
    letI : MeasurableSpace Λ.torus := borel Λ.torus
    khotNaorAverageDistanceConstant * (n : Real) ^ 2 /
        coveringRadius (knDualLattice Λ) ^ 2 ≤
      ∫ x, ∫ y, dist x y ^ 2 ∂torusHaarMeasure Λ ∂torusHaarMeasure Λ := by
  classical
  letI : SeminormedAddCommGroup Λ.torus := Λ.torusSeminormedAddCommGroup
  letI : MeasurableSpace Λ.torus := borel Λ.torus
  haveI : CompactSpace Λ.torus := Λ.torus_compactSpace
  haveI : BorelSpace Λ.torus := ⟨rfl⟩
  haveI : MeasureTheory.IsProbabilityMeasure (torusHaarMeasure Λ) :=
    torusHaarMeasure_isProbability Λ
  let B : Set Λ.torus := {z | dist z 0 < s}
  have hBmeas : MeasurableSet B := by
    have hcont : Continuous (fun z : Λ.torus => dist z 0) := by fun_prop
    exact isOpen_lt hcont continuous_const |>.measurableSet
  have hdistInt : Integrable (fun z : Λ.torus => dist z 0 ^ 2) (torusHaarMeasure Λ) :=
    integrable_of_continuous_compactSpace (X := Λ.torus) (μ := torusHaarMeasure Λ)
      (by fun_prop)
  have hRpos : 0 < coveringRadius (knDualLattice Λ) := dual_coveringRadius_pos hn Λ
  have hs_nonneg : 0 ≤ s := by
    rw [hs]
    positivity
  have htailMeasure :
      (7 / 8 : Real) ≤ (torusHaarMeasure Λ).real Bᶜ := by
    refine measureReal_compl_ge_of_measureReal_le (μ := torusHaarMeasure Λ)
      (s := B) (p := (1 / 8 : Real)) (c := (7 / 8 : Real)) hBmeas ?_ ?_
    · simpa [B] using hsmall
    · norm_num
  have hlarge : ∀ z ∈ Bᶜ, s ≤ dist z 0 := by
    intro z hz
    exact le_of_not_gt (by simpa [B] using hz)
  have htail :
      (7 / 8 : Real) * s ^ 2 ≤
        ∫ z, dist z 0 ^ 2 ∂torusHaarMeasure Λ := by
    exact integral_dist_zero_sq_ge_of_measureReal_large_set (μ := torusHaarMeasure Λ)
      (s := Bᶜ) hBmeas.compl hdistInt hs_nonneg htailMeasure hlarge
  have hconst :
      khotNaorAverageDistanceConstant * (n : Real) ^ 2 /
          coveringRadius (knDualLattice Λ) ^ 2 =
        (7 / 8 : Real) * s ^ 2 := by
    rw [hs]
    unfold khotNaorAverageDistanceConstant
    field_simp [hRpos.ne', Real.pi_ne_zero, Real.exp_ne_zero]
  calc
    khotNaorAverageDistanceConstant * (n : Real) ^ 2 /
        coveringRadius (knDualLattice Λ) ^ 2 =
        (7 / 8 : Real) * s ^ 2 := hconst
    _ ≤ ∫ z, dist z 0 ^ 2 ∂torusHaarMeasure Λ := htail
    _ = ∫ x, ∫ y, dist x y ^ 2 ∂torusHaarMeasure Λ ∂torusHaarMeasure Λ :=
        (flatTorus_haar_difference_dist_sq Λ).symm

private theorem flatTorus_average_distance_sq_lower
    {n : Nat} (hn : 1 ≤ n) (Λ : KNFullRankLattice n) :
    letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
    letI : MeasurableSpace Λ.torus := borel Λ.torus
    khotNaorAverageDistanceConstant * (n : Real) ^ 2 /
        coveringRadius (knDualLattice Λ) ^ 2 ≤
      ∫ x, ∫ y, dist x y ^ 2
        ∂torusHaarMeasure Λ ∂torusHaarMeasure Λ := by
  refine flatTorus_average_distance_sq_lower_of_small_ball hn Λ (s := ?_) ?_ ?_
  · exact (n : Real) /
      (16 * Real.pi * Real.exp 1 * coveringRadius (knDualLattice Λ))
  · rfl
  · simpa [KNFullRankLattice.torusMetric, KNFullRankLattice.torusSeminormedAddCommGroup] using
      flatTorus_small_ball_measure_le_one_eighth hn Λ

private lemma distortion_lower_energy_bound_of_average_distance
    {X : Type u} [PseudoMetricSpace X] [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    {H : Type v} [NormedAddCommGroup H] (f : X -> H) {scale A : Real}
    (hscale : 0 < scale)
    (hlower : ∀ x y : X, scale * dist x y ≤ ‖f x - f y‖)
    (hAverage : A ≤ ∫ x, ∫ y, dist x y ^ 2 ∂μ ∂μ)
    (hScaledDistInt :
      Integrable (Function.uncurry fun x y : X => (scale * dist x y) ^ 2) (μ.prod μ))
    (hEnergyInt :
      Integrable (Function.uncurry fun x y : X => ‖f x - f y‖ ^ 2) (μ.prod μ)) :
    scale ^ 2 * A ≤ ∫ x, ∫ y, ‖f x - f y‖ ^ 2 ∂μ ∂μ := by
  have hmono :
      (∫ x, ∫ y, (scale * dist x y) ^ 2 ∂μ ∂μ) ≤
        ∫ x, ∫ y, ‖f x - f y‖ ^ 2 ∂μ ∂μ := by
    exact integral_integral_mono_of_integrable hScaledDistInt hEnergyInt
      (fun x y => by
        have hle := hlower x y
        have hleft_nonneg : 0 ≤ scale * dist x y := mul_nonneg hscale.le dist_nonneg
        have hright_nonneg : 0 ≤ ‖f x - f y‖ := norm_nonneg _
        have hdiff : 0 ≤ ‖f x - f y‖ - scale * dist x y := sub_nonneg.mpr hle
        have hsum : 0 ≤ ‖f x - f y‖ + scale * dist x y :=
          add_nonneg hright_nonneg hleft_nonneg
        nlinarith [mul_nonneg hdiff hsum])
  have hscaleIntegral :
      (∫ x, ∫ y, (scale * dist x y) ^ 2 ∂μ ∂μ) =
        scale ^ 2 * ∫ x, ∫ y, dist x y ^ 2 ∂μ ∂μ := by
    simp_rw [mul_pow]
    exact integral_integral_const_mul (μ := μ) (scale ^ 2)
      (fun x y : X => dist x y ^ 2)
  calc
    scale ^ 2 * A ≤ scale ^ 2 * ∫ x, ∫ y, dist x y ^ 2 ∂μ ∂μ := by
      exact mul_le_mul_of_nonneg_left hAverage (sq_nonneg scale)
    _ = (∫ x, ∫ y, (scale * dist x y) ^ 2 ∂μ ∂μ) := hscaleIntegral.symm
    _ ≤ ∫ x, ∫ y, ‖f x - f y‖ ^ 2 ∂μ ∂μ := hmono

private lemma distortion_lower_energy_bound_of_average_distance_compact
    {X : Type u} [PseudoMetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [BorelSpace (X × X)] {μ : Measure X} [IsFiniteMeasure μ]
    {H : Type v} [NormedAddCommGroup H] (f : X -> H) {scale A : Real}
    (hscale : 0 < scale) (hf : Continuous f)
    (hlower : ∀ x y : X, scale * dist x y ≤ ‖f x - f y‖)
    (hAverage : A ≤ ∫ x, ∫ y, dist x y ^ 2 ∂μ ∂μ) :
    scale ^ 2 * A ≤ ∫ x, ∫ y, ‖f x - f y‖ ^ 2 ∂μ ∂μ := by
  exact distortion_lower_energy_bound_of_average_distance (X := X) (μ := μ) f hscale hlower
    hAverage
    (integrable_scaled_dist_sq_of_compactSpace (X := X) (μ := μ) scale)
    (integrable_energy_sq_of_continuous_compactSpace (X := X) (μ := μ) hf)

private theorem dualLattice_distortion_witness_lower_of_average_and_poincare_compact_space
    {X : Type u} [PseudoMetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [BorelSpace (X × X)] {n : Nat} (hn : 1 ≤ n) (Λ : KNFullRankLattice n)
    {H : Type v} [NormedAddCommGroup H] (f : X -> H)
    {scale D : Real} {μ : Measure X} [IsFiniteMeasure μ]
    (hscale : 0 < scale) (hD : 1 ≤ D) (hf : Continuous f)
    (hlower : ∀ x y : X, scale * dist x y ≤ ‖f x - f y‖)
    (hAverage :
      khotNaorAverageDistanceConstant * (n : Real) ^ 2 /
          coveringRadius (knDualLattice Λ) ^ 2 ≤
        ∫ x, ∫ y, dist x y ^ 2 ∂μ ∂μ)
    (hPoincare :
      (∫ x, ∫ y, ‖f x - f y‖ ^ 2 ∂μ ∂μ) ≤
        (n : Real) * (D * scale) ^ 2 /
          (2 * Real.pi ^ 2 * shortestVectorLength (knDualLattice Λ) ^ 2)) :
    khotNaorAnalyticConstant *
        (shortestVectorLength (knDualLattice Λ) /
          coveringRadius (knDualLattice Λ)) *
        Real.sqrt (n : Real) ≤ D := by
  have hLowerEnergy :
      scale ^ 2 *
          (khotNaorAverageDistanceConstant * (n : Real) ^ 2 /
            coveringRadius (knDualLattice Λ) ^ 2) ≤
        ∫ x, ∫ y, ‖f x - f y‖ ^ 2 ∂μ ∂μ := by
    exact distortion_lower_energy_bound_of_average_distance_compact
      (X := X) (μ := μ) f hscale hf hlower hAverage
  exact dualLattice_distortion_witness_lower_of_dual_energy_bounds (n := n) hn Λ
    (scale := scale) (D := D)
    hscale hD hLowerEnergy hPoincare

private theorem dualLattice_distortion_witness_lower_of_average_and_poincare
    {n : Nat} (hn : 1 ≤ n) (Λ : KNFullRankLattice n)
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
    [MeasurableSpace Λ.torus] (f : Λ.torus -> H)
    {scale D : Real} {μ : Measure Λ.torus} [SFinite μ]
    (hscale : 0 < scale) (hD : 1 ≤ D)
    (hlower :
      letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
      ∀ x y : Λ.torus, scale * dist x y ≤ ‖f x - f y‖)
    (hAverage :
      letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
      khotNaorAverageDistanceConstant * (n : Real) ^ 2 /
          coveringRadius (knDualLattice Λ) ^ 2 ≤
        ∫ x, ∫ y, dist x y ^ 2 ∂μ ∂μ)
    (hPoincare :
      letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
      (∫ x, ∫ y, ‖f x - f y‖ ^ 2 ∂μ ∂μ) ≤
        (n : Real) * (D * scale) ^ 2 /
          (2 * Real.pi ^ 2 * shortestVectorLength (knDualLattice Λ) ^ 2))
    (hScaledDistInt :
      letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
      Integrable (Function.uncurry fun x y : Λ.torus => (scale * dist x y) ^ 2) (μ.prod μ))
    (hEnergyInt :
      letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
      Integrable (Function.uncurry fun x y : Λ.torus => ‖f x - f y‖ ^ 2) (μ.prod μ)) :
    khotNaorAnalyticConstant *
        (shortestVectorLength (knDualLattice Λ) /
          coveringRadius (knDualLattice Λ)) *
        Real.sqrt (n : Real) ≤ D := by
  letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
  have hLowerEnergy :
      scale ^ 2 *
          (khotNaorAverageDistanceConstant * (n : Real) ^ 2 /
            coveringRadius (knDualLattice Λ) ^ 2) ≤
        ∫ x, ∫ y, ‖f x - f y‖ ^ 2 ∂μ ∂μ := by
    exact distortion_lower_energy_bound_of_average_distance
      (X := Λ.torus) (μ := μ) f hscale hlower hAverage hScaledDistInt hEnergyInt
  exact dualLattice_distortion_witness_lower_of_dual_energy_bounds (n := n) hn Λ
    (scale := scale) (D := D)
    hscale hD hLowerEnergy hPoincare

private theorem dualLattice_distortion_witness_lower_of_torus_average_and_poincare
    {n : Nat} (hn : 1 ≤ n) (Λ : KNFullRankLattice n)
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
    (f : Λ.torus -> H) {scale D : Real}
    (hscale : 0 < scale) (hD : 1 ≤ D)
    (hf :
      letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
      Continuous f)
    (hlower :
      letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
      ∀ x y : Λ.torus, scale * dist x y ≤ ‖f x - f y‖)
    (hAverage :
      letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
      letI : MeasurableSpace Λ.torus := borel Λ.torus
      khotNaorAverageDistanceConstant * (n : Real) ^ 2 /
          coveringRadius (knDualLattice Λ) ^ 2 ≤
        ∫ x, ∫ y, dist x y ^ 2 ∂torusHaarMeasure Λ ∂torusHaarMeasure Λ)
    (hPoincare :
      letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
      letI : MeasurableSpace Λ.torus := borel Λ.torus
      (∫ x, ∫ y, ‖f x - f y‖ ^ 2 ∂torusHaarMeasure Λ ∂torusHaarMeasure Λ) ≤
        (n : Real) * (D * scale) ^ 2 /
          (2 * Real.pi ^ 2 * shortestVectorLength (knDualLattice Λ) ^ 2)) :
    khotNaorAnalyticConstant *
        (shortestVectorLength (knDualLattice Λ) /
          coveringRadius (knDualLattice Λ)) *
        Real.sqrt (n : Real) ≤ D := by
  letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
  letI : MeasurableSpace Λ.torus := borel Λ.torus
  haveI : CompactSpace Λ.torus := flatTorusMetric_compactSpace Λ.basis
  haveI : SecondCountableTopology Λ.torus := flatTorusMetric_secondCountableTopology Λ.basis
  haveI : BorelSpace Λ.torus := ⟨rfl⟩
  haveI : BorelSpace (Λ.torus × Λ.torus) := by infer_instance
  haveI : MeasureTheory.IsProbabilityMeasure (torusHaarMeasure Λ) :=
    torusHaarMeasure_isProbability Λ
  let μ : Measure Λ.torus := torusHaarMeasure Λ
  have hFinite : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    dsimp [μ]
    have hprob : (torusHaarMeasure Λ) Set.univ = 1 := measure_univ
    calc
      (torusHaarMeasure Λ) Set.univ = 1 := hprob
      _ < (⊤ : ENNReal) := by norm_num
  haveI : IsFiniteMeasure (torusHaarMeasure Λ) := hFinite
  have hAverageμ :
      khotNaorAverageDistanceConstant * (n : Real) ^ 2 /
          coveringRadius (knDualLattice Λ) ^ 2 ≤
        ∫ x, ∫ y, dist x y ^ 2 ∂μ ∂μ := by
    simpa [μ] using hAverage
  have hPoincareμ :
      (∫ x, ∫ y, ‖f x - f y‖ ^ 2 ∂μ ∂μ) ≤
        (n : Real) * (D * scale) ^ 2 /
          (2 * Real.pi ^ 2 * shortestVectorLength (knDualLattice Λ) ^ 2) := by
    simpa [μ] using hPoincare
  exact dualLattice_distortion_witness_lower_of_average_and_poincare_compact_space
    (X := Λ.torus) (μ := μ) hn Λ f hscale hD hf hlower
    hAverageμ hPoincareμ

private theorem dualLattice_distortion_witness_lower
    {n : Nat} (hn : 1 ≤ n) (Λ : KNFullRankLattice n)
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
    (f : Λ.torus -> H) {scale D : Real}
    (hscale : 0 < scale) (hD : 1 ≤ D)
    (hlower :
      letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
      ∀ x y : Λ.torus, scale * dist x y ≤ ‖f x - f y‖)
    (hupper :
      letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
      ∀ x y : Λ.torus, ‖f x - f y‖ ≤ D * (scale * dist x y)) :
    khotNaorAnalyticConstant *
        (shortestVectorLength (knDualLattice Λ) /
          coveringRadius (knDualLattice Λ)) *
        Real.sqrt (n : Real) ≤ D := by
  classical
  letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
  letI : MeasurableSpace Λ.torus := borel Λ.torus
  have hDnonneg : 0 ≤ D := le_trans zero_le_one hD
  have hLnonneg : 0 ≤ D * scale := mul_nonneg hDnonneg hscale.le
  have hf : Continuous f := continuous_of_distortion_upper Λ f hscale hD hupper
  have hupper' :
      ∀ x y : Λ.torus, ‖f x - f y‖ ≤ (D * scale) * dist x y := by
    intro x y
    calc
      ‖f x - f y‖ ≤ D * (scale * dist x y) := hupper x y
      _ = (D * scale) * dist x y := by ring
  have hAverage := flatTorus_average_distance_sq_lower hn Λ
  have hPoincare := flatTorus_hilbert_poincare hn Λ f hLnonneg hupper'
  exact dualLattice_distortion_witness_lower_of_torus_average_and_poincare
    hn Λ f hscale hD hf hlower hAverage
    (by simpa [mul_assoc] using hPoincare)

/-- Analytic lower bound for a torus in terms of the dual lattice data. -/
theorem dualLatticeHilbertLowerBound {n : Nat}
    (hn : 1 ≤ n) (Λ : KNFullRankLattice n) :
    ENNReal.ofReal
        (khotNaorAnalyticConstant *
          (shortestVectorLength (knDualLattice Λ) / coveringRadius (knDualLattice Λ)) *
            Real.sqrt (n : Real)) ≤
      (letI : PseudoMetricSpace Λ.torus := Λ.torusMetric;
        hilbertDistortion Λ.torus) := by
  classical
  letI : PseudoMetricSpace Λ.torus := Λ.torusMetric
  set K : Real :=
    khotNaorAnalyticConstant *
      (shortestVectorLength (knDualLattice Λ) / coveringRadius (knDualLattice Λ)) *
        Real.sqrt (n : Real)
  unfold hilbertDistortion
  refine le_sInf ?_
  intro D hDmem
  change ENNReal.ofReal K ≤ D
  by_cases hDtop : D = ⊤
  · rw [hDtop]
    exact le_top
  rcases hDmem with ⟨hDone, H, hNorm, hInner, hComplete, f, scale, hscale, hf⟩
  letI : NormedAddCommGroup H := hNorm
  letI : InnerProductSpace Real H := hInner
  letI : CompleteSpace H := hComplete
  have hDofReal : ENNReal.ofReal D.toReal = D := ENNReal.ofReal_toReal hDtop
  have hDone_ofReal : (1 : ENNReal) ≤ ENNReal.ofReal D.toReal := by
    simpa [hDofReal] using hDone
  have hDreal : (1 : Real) ≤ D.toReal := ENNReal.one_le_ofReal.mp hDone_ofReal
  have hDnonneg : 0 ≤ D.toReal := le_trans zero_le_one hDreal
  have hlowerReal :
      ∀ x y : Λ.torus, scale * dist x y ≤ ‖f x - f y‖ := by
    intro x y
    exact (ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)).mp (hf x y).1
  have hupperReal :
      ∀ x y : Λ.torus, ‖f x - f y‖ ≤ D.toReal * (scale * dist x y) := by
    intro x y
    have hscaled_nonneg : 0 ≤ scale * dist x y := mul_nonneg hscale.le dist_nonneg
    have htarget_nonneg : 0 ≤ D.toReal * (scale * dist x y) :=
      mul_nonneg hDnonneg hscaled_nonneg
    have hENN :
        ENNReal.ofReal ‖f x - f y‖ ≤
          ENNReal.ofReal (D.toReal * (scale * dist x y)) := by
      rw [ENNReal.ofReal_mul hDnonneg]
      simpa [hDofReal] using (hf x y).2
    exact (ENNReal.ofReal_le_ofReal_iff htarget_nonneg).mp hENN
  have hKreal : K ≤ D.toReal := by
    simpa [K] using
      dualLattice_distortion_witness_lower (n := n) hn Λ (f := f)
        (scale := scale) (D := D.toReal) hscale hDreal
        (by simpa using hlowerReal) (by simpa using hupperReal)
  calc
    ENNReal.ofReal K ≤ ENNReal.ofReal D.toReal := ENNReal.ofReal_le_ofReal hKreal
    _ = D := hDofReal

/-- The lower-bound principle converting real distortion estimates into `hilbertDistortion`. -/
theorem ofReal_le_hilbertDistortion_of_embedding_lower_bound
    {X : Type u} [PseudoMetricSpace X] {K : Real} (_hK : 0 ≤ K)
    (hLower : ∀ D : ENNReal, hilbertDistortion.{u, v} X ≤ D -> ENNReal.ofReal K ≤ D) :
    ENNReal.ofReal K ≤ hilbertDistortion.{u, v} X := by
  exact hLower (hilbertDistortion.{u, v} X) le_rfl

/-- Coordinatewise reduction of an integer vector modulo `q`. -/
def intVectorMod (q n : Nat) (z : Fin n -> Int) : Fin n -> ZMod q :=
  fun i => z i

/-- Dot product over `ZMod q`. -/
def finiteFieldDot (q n : Nat) (x y : Fin n -> ZMod q) : ZMod q :=
  ∑ i : Fin n, x i * y i

private def finiteFieldDotAddHom (q n : Nat) (a : Fin n -> ZMod q) :
    (Fin n -> ZMod q) →+ ZMod q where
  toFun h := finiteFieldDot q n h a
  map_zero' := by
    simp [finiteFieldDot]
  map_add' x y := by
    simp [finiteFieldDot, Finset.sum_add_distrib, add_mul]

/-- Matrix-vector multiplication over `ZMod q`, written out to keep the scaffold local. -/
def finiteFieldMatVec (q s n : Nat)
    (H : Matrix (Fin s) (Fin n) (ZMod q)) (x : Fin n -> ZMod q) : Fin s -> ZMod q :=
  fun i => ∑ j : Fin n, H i j * x j

/-- The syndrome of an integer vector for a parity-check matrix. -/
def constructionASyndrome (q s n : Nat)
    (H : Matrix (Fin s) (Fin n) (ZMod q)) (z : Fin n -> Int) : Fin s -> ZMod q :=
  finiteFieldMatVec q s n H (intVectorMod q n z)

private noncomputable def kernelSyndromeRowsEquiv
    (q s n : Nat) (z : Fin n -> Int) :
    {H : Matrix (Fin s) (Fin n) (ZMod q) // constructionASyndrome q s n H z = 0} ≃
      (Fin s -> {h : Fin n -> ZMod q // finiteFieldDot q n h (intVectorMod q n z) = 0}) where
  toFun H i := ⟨fun j => H.1 i j, by
    have h := congr_fun H.2 i
    simpa [constructionASyndrome, finiteFieldMatVec, finiteFieldDot] using h⟩
  invFun rows := ⟨fun i j => (rows i).1 j, by
    funext i
    simpa [constructionASyndrome, finiteFieldMatVec, finiteFieldDot] using (rows i).2⟩
  left_inv H := by
    ext i j
    rfl
  right_inv rows := by
    ext i j
    rfl

/-- Boolean vectors over `ZMod q`. -/
def IsBooleanVector {q n : Nat} (ε : Fin n -> ZMod q) : Prop :=
  ∀ i : Fin n, ε i = 0 ∨ ε i = 1

private def booleanVectorEquiv (q n : Nat) (h01 : (0 : ZMod q) ≠ 1) :
    (Fin n -> Bool) ≃ {ε : Fin n -> ZMod q // IsBooleanVector ε} where
  toFun b := ⟨fun i => if b i then 1 else 0, by
    intro i
    by_cases hb : b i
    · right
      simp [hb]
    · left
      simp [hb]⟩
  invFun ε := fun i => if ε.1 i = 0 then false else true
  left_inv b := by
    funext i
    have h10 : (1 : ZMod q) ≠ 0 := fun h => h01 h.symm
    by_cases hb : b i
    · simp [hb, h10]
    · simp [hb]
  right_inv ε := by
    ext i
    dsimp
    have h10 : (1 : ZMod q) ≠ 0 := fun h => h01 h.symm
    rcases ε.2 i with hzero | hone
    · simp [hzero]
    · simp [hone, h10]

private lemma zmod_zero_ne_one_of_prime (q : Nat) (hq : Nat.Prime q) :
    (0 : ZMod q) ≠ 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  exact zero_ne_one

private theorem booleanVector_card (q n : Nat) (hq : Nat.Prime q) :
    Nat.card {ε : Fin n -> ZMod q // IsBooleanVector ε} = 2 ^ n := by
  rw [← Nat.card_congr (booleanVectorEquiv q n (zmod_zero_ne_one_of_prime q hq))]
  simp

private theorem nonzeroBooleanVector_card (q n : Nat) (hq : Nat.Prime q) :
    Nat.card {ε : Fin n -> ZMod q // IsBooleanVector ε ∧ ε ≠ 0} = 2 ^ n - 1 := by
  classical
  let h01 := zmod_zero_ne_one_of_prime q hq
  let B := {ε : Fin n -> ZMod q // IsBooleanVector ε}
  let z : B := ⟨0, by intro i; left; rfl⟩
  let e : {ε : Fin n -> ZMod q // IsBooleanVector ε ∧ ε ≠ 0} ≃ {b : B // b ≠ z} :=
    { toFun := fun ε => ⟨⟨ε.1, ε.2.1⟩, by
        intro hz
        exact ε.2.2 (congrArg Subtype.val hz)⟩
      invFun := fun b => ⟨b.1.1, ⟨b.1.2, by
        intro hzero
        apply b.2
        ext i
        exact congr_fun hzero i⟩⟩
      left_inv := by
        intro ε
        ext i
        rfl
      right_inv := by
        intro b
        ext i
        rfl }
  haveI : Fintype B := Fintype.ofEquiv (Fin n -> Bool) (booleanVectorEquiv q n h01)
  rw [Nat.card_congr e]
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl (fun b : B => b = z)]
  have hsingleton : Fintype.card {b : B // b = z} = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨z, rfl⟩, ?_⟩
    intro y
    exact Subtype.ext y.2
  rw [hsingleton]
  have hB : Fintype.card B = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact booleanVector_card q n hq
  rw [hB]

private abbrev NonzeroBooleanVector (q n : Nat) :=
  {ε : Fin n -> ZMod q // IsBooleanVector ε ∧ ε ≠ 0}

private noncomputable instance nonzeroBooleanVectorFintype (q n : Nat) [NeZero q] :
    Fintype (NonzeroBooleanVector q n) := by
  classical
  infer_instance

private theorem nonzeroBooleanVector_fintype_card (q n : Nat) [NeZero q] (hq : Nat.Prime q) :
    Fintype.card (NonzeroBooleanVector q n) = 2 ^ n - 1 := by
  rw [← Nat.card_eq_fintype_card]
  exact nonzeroBooleanVector_card q n hq

private noncomputable def fixedSyndromeIncidence
    (q s n : Nat) (y : Fin s -> ZMod q) :=
  {p : Matrix (Fin s) (Fin n) (ZMod q) × NonzeroBooleanVector q n //
    finiteFieldMatVec q s n p.1 p.2.1 = y}

private noncomputable def fixedSyndromeFiber
    (q s n : Nat) (y : Fin s -> ZMod q) (ε : NonzeroBooleanVector q n) :=
  {H : Matrix (Fin s) (Fin n) (ZMod q) //
    finiteFieldMatVec q s n H ε.1 = y}

private noncomputable instance fixedSyndromeIncidenceFintype
    (q s n : Nat) [NeZero q] (y : Fin s -> ZMod q) :
    Fintype (fixedSyndromeIncidence q s n y) := by
  classical
  refine Fintype.subtype
    (Finset.univ.filter fun p : Matrix (Fin s) (Fin n) (ZMod q) ×
        NonzeroBooleanVector q n => finiteFieldMatVec q s n p.1 p.2.1 = y) ?_
  intro p
  simp

private noncomputable instance fixedSyndromeFiberFintype
    (q s n : Nat) [NeZero q] (y : Fin s -> ZMod q) (ε : NonzeroBooleanVector q n) :
    Fintype (fixedSyndromeFiber q s n y ε) := by
  classical
  refine Fintype.subtype
    (Finset.univ.filter fun H : Matrix (Fin s) (Fin n) (ZMod q) =>
      finiteFieldMatVec q s n H ε.1 = y) ?_
  intro H
  simp

/-- One nontrivial finite-field linear equation has uniform fibers. -/
theorem oneRowUniform
    (q n : Nat) [NeZero q] (hq : Nat.Prime q) (a : Fin n -> ZMod q) (ha : a ≠ 0)
    (b : ZMod q) :
    Fintype.card {h : Fin n -> ZMod q // finiteFieldDot q n h a = b} * q =
      Fintype.card (Fin n -> ZMod q) := by
  classical
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  let f := finiteFieldDotAddHom q n a
  have hsurj : Function.Surjective f := by
    intro b
    have hcoord : ∃ i : Fin n, a i ≠ 0 := by
      by_contra h
      apply ha
      funext i
      by_contra hi
      exact h ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hcoord
    refine ⟨Pi.single i (b / a i), ?_⟩
    change finiteFieldDot q n (Pi.single i (b / a i)) a = b
    rw [finiteFieldDot, Finset.sum_eq_single i]
    · simp [hi]
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · intro hi_univ
      exact False.elim (hi_univ (Finset.mem_univ i))
  have hb_range : b ∈ Set.range f := hsurj b
  have hzero_range : (0 : ZMod q) ∈ Set.range f :=
    ⟨0, by simp [f, finiteFieldDotAddHom, finiteFieldDot]⟩
  have hfib := AddMonoidHom.card_fiber_eq_of_mem_range f hb_range hzero_range
  have hindex : f.ker.index = Fintype.card (ZMod q) := by
    rw [AddSubgroup.index_ker]
    have hrange_top : f.range = ⊤ := AddMonoidHom.range_eq_top.mpr hsurj
    rw [hrange_top]
    simp
  have hker_card :
      Fintype.card {h : Fin n -> ZMod q // f h = 0} * Fintype.card (ZMod q) =
        Fintype.card (Fin n -> ZMod q) := by
    have h := f.ker.card_mul_index
    rw [hindex] at h
    simpa [AddMonoidHom.mem_ker] using h
  have hfib_card :
      Fintype.card {h : Fin n -> ZMod q // f h = b} =
        Fintype.card {h : Fin n -> ZMod q // f h = 0} := by
    simpa [Fintype.card_subtype] using hfib
  change Fintype.card {h : Fin n -> ZMod q // f h = b} * q =
    Fintype.card (Fin n -> ZMod q)
  rw [hfib_card]
  simpa [Nat.card_zmod] using hker_card

/-- Kernel probability/counting for one nonzero vector and a random parity-check matrix. -/
theorem kernelSyndromeFiber_card
    (q s n : Nat) [NeZero q] (hq : Nat.Prime q) (z : Fin n -> Int)
    (hz : intVectorMod q n z ≠ 0) :
    Fintype.card
        {H : Matrix (Fin s) (Fin n) (ZMod q) //
          constructionASyndrome q s n H z = 0} * q ^ s =
      Fintype.card (Matrix (Fin s) (Fin n) (ZMod q)) := by
  classical
  let a := intVectorMod q n z
  have hone := oneRowUniform q n hq a hz (0 : ZMod q)
  have hcard_rows :
      Fintype.card
          {H : Matrix (Fin s) (Fin n) (ZMod q) //
            constructionASyndrome q s n H z = 0} =
        Fintype.card (Fin s -> {h : Fin n -> ZMod q // finiteFieldDot q n h a = 0}) := by
    exact Fintype.card_congr (kernelSyndromeRowsEquiv q s n z)
  rw [hcard_rows]
  simp only [Fintype.card_fun, Fintype.card_fin]
  change Fintype.card {h : Fin n -> ZMod q // finiteFieldDot q n h a = 0} ^ s * q ^ s =
    Fintype.card (Fin s -> Fin n -> ZMod q)
  rw [Fintype.card_fun]
  simp only [Fintype.card_fin]
  rw [← mul_pow]
  rw [hone]

private noncomputable def syndromeRowsEquiv
    (q s n : Nat) (a : Fin n -> ZMod q) (y : Fin s -> ZMod q) :
    {H : Matrix (Fin s) (Fin n) (ZMod q) //
      finiteFieldMatVec q s n H a = y} ≃
      ((i : Fin s) -> {h : Fin n -> ZMod q // finiteFieldDot q n h a = y i}) where
  toFun H i := ⟨fun j => H.1 i j, by
    have h := congr_fun H.2 i
    simpa [finiteFieldMatVec, finiteFieldDot] using h⟩
  invFun rows := ⟨fun i j => (rows i).1 j, by
    funext i
    simpa [finiteFieldMatVec, finiteFieldDot] using (rows i).2⟩
  left_inv H := by
    ext i j
    rfl
  right_inv rows := by
    ext i j
    rfl

private theorem syndromeFiber_card
    (q s n : Nat) [NeZero q] (hq : Nat.Prime q)
    (a : Fin n -> ZMod q) (ha : a ≠ 0) (y : Fin s -> ZMod q) :
    Fintype.card
        {H : Matrix (Fin s) (Fin n) (ZMod q) //
          finiteFieldMatVec q s n H a = y} * q ^ s =
      Fintype.card (Matrix (Fin s) (Fin n) (ZMod q)) := by
  classical
  have hcard_rows :
      Fintype.card
          {H : Matrix (Fin s) (Fin n) (ZMod q) //
            finiteFieldMatVec q s n H a = y} =
        Fintype.card
          ((i : Fin s) -> {h : Fin n -> ZMod q // finiteFieldDot q n h a = y i}) := by
    exact Fintype.card_congr (syndromeRowsEquiv q s n a y)
  rw [hcard_rows]
  let rowFiber : Fin s -> Type :=
    fun i => {h : Fin n -> ZMod q // finiteFieldDot q n h a = y i}
  let rowType : Type := Fin n -> ZMod q
  have hrow : ∀ i : Fin s, Nat.card (rowFiber i) * q = Nat.card rowType := by
    intro i
    simpa [rowFiber, rowType, Nat.card_eq_fintype_card] using
      oneRowUniform q n hq a ha (y i)
  rw [← Nat.card_eq_fintype_card]
  rw [← Nat.card_eq_fintype_card]
  change Nat.card ((i : Fin s) -> rowFiber i) * q ^ s =
    Nat.card (Matrix (Fin s) (Fin n) (ZMod q))
  rw [Nat.card_pi]
  change (∏ i : Fin s, Nat.card (rowFiber i)) * q ^ s =
    Nat.card (Fin s -> rowType)
  rw [Nat.card_pi]
  change (∏ i : Fin s, Nat.card (rowFiber i)) * q ^ s =
    ∏ _i : Fin s, Nat.card rowType
  calc
    (∏ i : Fin s, Nat.card (rowFiber i)) * q ^ s =
        (∏ i : Fin s, Nat.card (rowFiber i)) * (∏ _i : Fin s, q) := by
          simp
    _ = ∏ i : Fin s, Nat.card (rowFiber i) * q := by
          rw [Finset.prod_mul_distrib]
    _ = ∏ _i : Fin s, Nat.card rowType := by
          exact Finset.prod_congr rfl fun i _hi => hrow i

private def finiteFieldPairDotAddHom (q n : Nat)
    (a b : Fin n -> ZMod q) : (Fin n -> ZMod q) →+ (ZMod q × ZMod q) where
  toFun h := (finiteFieldDot q n h a, finiteFieldDot q n h b)
  map_zero' := by
    simp [finiteFieldDot]
  map_add' x y := by
    ext <;> simp [finiteFieldDot, Finset.sum_add_distrib, add_mul]

private lemma finiteFieldDot_single
    (q n : Nat) (i : Fin n) (c : ZMod q) (a : Fin n -> ZMod q) :
    finiteFieldDot q n (Pi.single i c) a = c * a i := by
  rw [finiteFieldDot, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Pi.single_eq_of_ne]
    · simp
    · exact hj
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

private lemma finiteFieldDot_add_left
    (q n : Nat) (x y a : Fin n -> ZMod q) :
    finiteFieldDot q n (x + y) a =
      finiteFieldDot q n x a + finiteFieldDot q n y a := by
  simp [finiteFieldDot, Finset.sum_add_distrib, add_mul]

private lemma finiteFieldPair_exists_det_ne_zero
    (q n : Nat) [NeZero q] (hq : Nat.Prime q) (a b : Fin n -> ZMod q)
    (hindependent : ∀ α β : ZMod q, α • a + β • b = 0 -> α = 0 ∧ β = 0) :
    ∃ i j : Fin n, a i * b j - a j * b i ≠ 0 := by
  classical
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  have ha : a ≠ 0 := by
    intro ha
    have hlin : (1 : ZMod q) • a + (0 : ZMod q) • b = 0 := by
      ext i
      simp [ha]
    exact one_ne_zero (hindependent 1 0 hlin).1
  obtain ⟨i, hi⟩ : ∃ i : Fin n, a i ≠ 0 := by
    by_contra h
    apply ha
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  by_contra hdet
  have hdet_zero : ∀ j : Fin n, a i * b j - a j * b i = 0 := by
    intro j
    by_contra h
    exact hdet ⟨i, j, h⟩
  have hb_eq : b = (b i / a i) • a := by
    funext j
    have hmul : a i * b j = a j * b i := sub_eq_zero.mp (hdet_zero j)
    calc
      b j = (a i)⁻¹ * (a i * b j) := by
        rw [← mul_assoc, inv_mul_cancel₀ hi, one_mul]
      _ = (a i)⁻¹ * (a j * b i) := by rw [hmul]
      _ = (b i / a i) * a j := by
        field_simp [hi]
      _ = ((b i / a i) • a) j := by
        rfl
  have hlin : (-(b i / a i)) • a + (1 : ZMod q) • b = 0 := by
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, one_smul]
    rw [congr_fun hb_eq j]
    simp
  exact one_ne_zero (hindependent (-(b i / a i)) 1 hlin).2

private lemma finiteFieldPairDotAddHom_surjective
    (q n : Nat) [NeZero q] (hq : Nat.Prime q) (a b : Fin n -> ZMod q)
    (hindependent : ∀ α β : ZMod q, α • a + β • b = 0 -> α = 0 ∧ β = 0) :
    Function.Surjective (finiteFieldPairDotAddHom q n a b) := by
  classical
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  obtain ⟨i, j, hdet⟩ := finiteFieldPair_exists_det_ne_zero q n hq a b hindependent
  intro yz
  rcases yz with ⟨y, z⟩
  let d : ZMod q := a i * b j - a j * b i
  let xCoeff : ZMod q := (y * b j - z * a j) / d
  let yCoeff : ZMod q := (a i * z - b i * y) / d
  let h : Fin n -> ZMod q := Pi.single i xCoeff + Pi.single j yCoeff
  refine ⟨h, ?_⟩
  have hd : d ≠ 0 := hdet
  have hdot_a : finiteFieldDot q n h a = y := by
    calc
      finiteFieldDot q n h a =
          xCoeff * a i + yCoeff * a j := by
            simp [h, finiteFieldDot_add_left, finiteFieldDot_single]
      _ = y := by
            apply (mul_right_inj' hd).mp
            simp [xCoeff, yCoeff]
            field_simp [d, hd]
            left
            simp [d]
            ring
  have hdot_b : finiteFieldDot q n h b = z := by
    calc
      finiteFieldDot q n h b =
          xCoeff * b i + yCoeff * b j := by
            simp [h, finiteFieldDot_add_left, finiteFieldDot_single]
      _ = z := by
            apply (mul_right_inj' hd).mp
            simp [xCoeff, yCoeff]
            field_simp [d, hd]
            left
            simp [d]
            ring
  ext <;> simp [finiteFieldPairDotAddHom, hdot_a, hdot_b]

private theorem pairRowUniform_card
    (q n : Nat) [NeZero q] (hq : Nat.Prime q) (a b : Fin n -> ZMod q)
    (hindependent : ∀ α β : ZMod q, α • a + β • b = 0 -> α = 0 ∧ β = 0)
    (y z : ZMod q) :
    Fintype.card {h : Fin n -> ZMod q //
        finiteFieldDot q n h a = y ∧ finiteFieldDot q n h b = z} * q ^ 2 =
      Fintype.card (Fin n -> ZMod q) := by
  classical
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  let f := finiteFieldPairDotAddHom q n a b
  have hsurj : Function.Surjective f :=
    finiteFieldPairDotAddHom_surjective q n hq a b hindependent
  have hyz_range : (y, z) ∈ Set.range f := hsurj (y, z)
  have hzero_range : (0 : ZMod q × ZMod q) ∈ Set.range f :=
    ⟨0, by simp [f, finiteFieldPairDotAddHom, finiteFieldDot]⟩
  have hfib := AddMonoidHom.card_fiber_eq_of_mem_range f hyz_range hzero_range
  have hindex : f.ker.index = Fintype.card (ZMod q × ZMod q) := by
    rw [AddSubgroup.index_ker]
    have hrange_top : f.range = ⊤ := AddMonoidHom.range_eq_top.mpr hsurj
    rw [hrange_top]
    simp
  have hker_card :
      Fintype.card {h : Fin n -> ZMod q // f h = 0} *
          Fintype.card (ZMod q × ZMod q) =
        Fintype.card (Fin n -> ZMod q) := by
    have h := f.ker.card_mul_index
    rw [hindex] at h
    simpa [AddMonoidHom.mem_ker] using h
  have hfib_card :
      Fintype.card {h : Fin n -> ZMod q // f h = (y, z)} =
        Fintype.card {h : Fin n -> ZMod q // f h = 0} := by
    simpa [Fintype.card_subtype] using hfib
  have hsubtype :
      Fintype.card {h : Fin n -> ZMod q //
          finiteFieldDot q n h a = y ∧ finiteFieldDot q n h b = z} =
        Fintype.card {h : Fin n -> ZMod q // f h = (y, z)} := by
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun h => by
      simp [f, finiteFieldPairDotAddHom, Prod.ext_iff])
  rw [hsubtype, hfib_card]
  simpa [Nat.card_zmod, pow_two] using hker_card

private noncomputable def pairSyndromeRowsEquiv
    (q s n : Nat) (a b : Fin n -> ZMod q) (y z : Fin s -> ZMod q) :
    {H : Matrix (Fin s) (Fin n) (ZMod q) //
      finiteFieldMatVec q s n H a = y ∧ finiteFieldMatVec q s n H b = z} ≃
      ((i : Fin s) ->
        {h : Fin n -> ZMod q //
          finiteFieldDot q n h a = y i ∧ finiteFieldDot q n h b = z i}) where
  toFun H i := ⟨fun j => H.1 i j, by
    constructor
    · have h := congr_fun H.2.1 i
      simpa [finiteFieldMatVec, finiteFieldDot] using h
    · have h := congr_fun H.2.2 i
      simpa [finiteFieldMatVec, finiteFieldDot] using h⟩
  invFun rows := ⟨fun i j => (rows i).1 j, by
    constructor <;> funext i
    · simpa [finiteFieldMatVec, finiteFieldDot] using (rows i).2.1
    · simpa [finiteFieldMatVec, finiteFieldDot] using (rows i).2.2⟩
  left_inv H := by
    ext i j
    rfl
  right_inv rows := by
    ext i j
    rfl

private theorem pairSyndromeFiber_card
    (q s n : Nat) [NeZero q] (hq : Nat.Prime q) (a b : Fin n -> ZMod q)
    (hindependent : ∀ α β : ZMod q, α • a + β • b = 0 -> α = 0 ∧ β = 0)
    (y z : Fin s -> ZMod q) :
    Fintype.card
        {H : Matrix (Fin s) (Fin n) (ZMod q) //
          finiteFieldMatVec q s n H a = y ∧ finiteFieldMatVec q s n H b = z} *
        q ^ (2 * s) =
      Fintype.card (Matrix (Fin s) (Fin n) (ZMod q)) := by
  classical
  have hcard_rows :
      Fintype.card
          {H : Matrix (Fin s) (Fin n) (ZMod q) //
            finiteFieldMatVec q s n H a = y ∧ finiteFieldMatVec q s n H b = z} =
        Fintype.card
          ((i : Fin s) ->
            {h : Fin n -> ZMod q //
              finiteFieldDot q n h a = y i ∧ finiteFieldDot q n h b = z i}) := by
    exact Fintype.card_congr (pairSyndromeRowsEquiv q s n a b y z)
  rw [hcard_rows]
  let rowFiber : Fin s -> Type :=
    fun i => {h : Fin n -> ZMod q //
      finiteFieldDot q n h a = y i ∧ finiteFieldDot q n h b = z i}
  let rowType : Type := Fin n -> ZMod q
  have hrow :
      ∀ i : Fin s, Nat.card (rowFiber i) * q ^ 2 = Nat.card rowType := by
    intro i
    simpa [rowFiber, rowType, Nat.card_eq_fintype_card] using
      pairRowUniform_card q n hq a b hindependent (y i) (z i)
  rw [← Nat.card_eq_fintype_card]
  rw [← Nat.card_eq_fintype_card]
  change Nat.card ((i : Fin s) -> rowFiber i) * q ^ (2 * s) =
    Nat.card (Matrix (Fin s) (Fin n) (ZMod q))
  rw [Nat.card_pi]
  change (∏ i : Fin s, Nat.card (rowFiber i)) * q ^ (2 * s) =
    Nat.card (Fin s -> rowType)
  rw [Nat.card_pi]
  change (∏ i : Fin s, Nat.card (rowFiber i)) * q ^ (2 * s) =
    ∏ _i : Fin s, Nat.card rowType
  calc
    (∏ i : Fin s, Nat.card (rowFiber i)) * q ^ (2 * s) =
        (∏ i : Fin s, Nat.card (rowFiber i)) * (q ^ 2) ^ s := by
          rw [pow_mul]
    _ = (∏ i : Fin s, Nat.card (rowFiber i)) * (∏ _i : Fin s, q ^ 2) := by
          simp
    _ = ∏ i : Fin s, Nat.card (rowFiber i) * q ^ 2 := by
          rw [Finset.prod_mul_distrib]
    _ = ∏ _i : Fin s, Nat.card rowType := by
          exact Finset.prod_congr rfl fun i _hi => hrow i

/-- Distinct nonzero Boolean vectors are linearly independent over odd prime fields. -/
theorem booleanVectors_linearIndependent
    (q n : Nat) (_hq : Nat.Prime q) (_hqodd : Odd q)
    {ε η : Fin n -> ZMod q} (hε : IsBooleanVector ε) (hη : IsBooleanVector η)
    (hε0 : ε ≠ 0) (hη0 : η ≠ 0) (hneq : ε ≠ η) :
    ∀ α β : ZMod q, α • ε + β • η = 0 -> α = 0 ∧ β = 0 := by
  intro α β hlin
  have hdiff : ∃ i : Fin n, ε i ≠ η i := by
    by_contra h
    apply hneq
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hdiff
  have hcoord_i := congr_fun hlin i
  rcases hε i with hεi | hεi <;> rcases hη i with hηi | hηi
  · exact False.elim (hi (hεi.trans hηi.symm))
  · have hβ : β = 0 := by
      simpa [hεi, hηi] using hcoord_i
    have hε_nonzero_coord : ∃ j : Fin n, ε j ≠ 0 := by
      by_contra h
      apply hε0
      funext j
      by_contra hj
      exact h ⟨j, hj⟩
    obtain ⟨j, hjε⟩ := hε_nonzero_coord
    have hεj : ε j = 1 := by
      rcases hε j with h | h
      · exact False.elim (hjε h)
      · exact h
    have hcoord_j := congr_fun hlin j
    have hα : α = 0 := by
      simpa [hβ, hεj] using hcoord_j
    exact ⟨hα, hβ⟩
  · have hα : α = 0 := by
      simpa [hεi, hηi] using hcoord_i
    have hη_nonzero_coord : ∃ j : Fin n, η j ≠ 0 := by
      by_contra h
      apply hη0
      funext j
      by_contra hj
      exact h ⟨j, hj⟩
    obtain ⟨j, hjη⟩ := hη_nonzero_coord
    have hηj : η j = 1 := by
      rcases hη j with h | h
      · exact False.elim (hjη h)
      · exact h
    have hcoord_j := congr_fun hlin j
    have hβ : β = 0 := by
      simpa [hα, hηj] using hcoord_j
    exact ⟨hα, hβ⟩
  · exact False.elim (hi (hεi.trans hηi.symm))

private theorem nonzeroBooleanSyndromeFiber_card
    (q s n : Nat) [NeZero q] (hq : Nat.Prime q)
    {ε : Fin n -> ZMod q} (_hε : IsBooleanVector ε) (hε0 : ε ≠ 0)
    (y : Fin s -> ZMod q) :
    Fintype.card
        {H : Matrix (Fin s) (Fin n) (ZMod q) //
          finiteFieldMatVec q s n H ε = y} * q ^ s =
      Fintype.card (Matrix (Fin s) (Fin n) (ZMod q)) :=
  syndromeFiber_card q s n hq ε hε0 y

private theorem nonzeroBooleanSyndromeFiber_nat_card
    (q s n : Nat) [NeZero q] (hq : Nat.Prime q)
    {ε : Fin n -> ZMod q} (hε : IsBooleanVector ε) (hε0 : ε ≠ 0)
    (y : Fin s -> ZMod q) :
    Nat.card
        {H : Matrix (Fin s) (Fin n) (ZMod q) //
          finiteFieldMatVec q s n H ε = y} * q ^ s =
      Nat.card (Matrix (Fin s) (Fin n) (ZMod q)) := by
  classical
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact nonzeroBooleanSyndromeFiber_card q s n hq hε hε0 y

private theorem fixedSyndromeIncidence_card_mul
    (q s n : Nat) [NeZero q] (hq : Nat.Prime q) (y : Fin s -> ZMod q) :
    Fintype.card (fixedSyndromeIncidence q s n y) * q ^ s =
      Fintype.card (NonzeroBooleanVector q n) *
        Fintype.card (Matrix (Fin s) (Fin n) (ZMod q)) := by
  classical
  let Ω := Matrix (Fin s) (Fin n) (ZMod q)
  let B := NonzeroBooleanVector q n
  let Inc := fixedSyndromeIncidence q s n y
  let Fiber := fixedSyndromeFiber q s n y
  let e : Inc ≃ Sigma Fiber :=
    { toFun := fun p : Inc => ⟨p.1.2, ⟨p.1.1, p.2⟩⟩
      invFun := fun p : Sigma Fiber => ⟨(p.2.1, p.1), p.2.2⟩
      left_inv := by
        intro p
        rcases p with ⟨⟨H, ε⟩, hHε⟩
        rfl
      right_inv := by
        intro p
        rcases p with ⟨ε, H, hHε⟩
        rfl }
  have hcard :
      Fintype.card Inc = Fintype.card (Sigma Fiber) :=
    Fintype.card_congr e
  rw [hcard, Fintype.card_sigma]
  calc
    (∑ ε : B, Fintype.card (Fiber ε)) * q ^ s =
        ∑ ε : B, Fintype.card (Fiber ε) * q ^ s := by
          rw [Finset.sum_mul]
    _ = ∑ _ε : B, Fintype.card Ω := by
          apply Finset.sum_congr rfl
          intro ε _hε
          simpa [Fiber, Ω] using
            nonzeroBooleanSyndromeFiber_card q s n hq ε.2.1 ε.2.2 y
    _ = Fintype.card B * Fintype.card Ω := by
          simp

private theorem distinctBooleanPairSyndromeFiber_card
    (q s n : Nat) [NeZero q] (hq : Nat.Prime q) (hqodd : Odd q)
    {ε η : Fin n -> ZMod q} (hε : IsBooleanVector ε) (hη : IsBooleanVector η)
    (hε0 : ε ≠ 0) (hη0 : η ≠ 0) (hneq : ε ≠ η)
    (y z : Fin s -> ZMod q) :
    Fintype.card
        {H : Matrix (Fin s) (Fin n) (ZMod q) //
          finiteFieldMatVec q s n H ε = y ∧ finiteFieldMatVec q s n H η = z} *
        q ^ (2 * s) =
      Fintype.card (Matrix (Fin s) (Fin n) (ZMod q)) :=
  pairSyndromeFiber_card q s n hq ε η
    (booleanVectors_linearIndependent q n hq hqodd hε hη hε0 hη0 hneq) y z

private theorem distinctBooleanPairSyndromeFiber_nat_card
    (q s n : Nat) [NeZero q] (hq : Nat.Prime q) (hqodd : Odd q)
    {ε η : Fin n -> ZMod q} (hε : IsBooleanVector ε) (hη : IsBooleanVector η)
    (hε0 : ε ≠ 0) (hη0 : η ≠ 0) (hneq : ε ≠ η)
    (y z : Fin s -> ZMod q) :
    Nat.card
        {H : Matrix (Fin s) (Fin n) (ZMod q) //
          finiteFieldMatVec q s n H ε = y ∧ finiteFieldMatVec q s n H η = z} *
        q ^ (2 * s) =
      Nat.card (Matrix (Fin s) (Fin n) (ZMod q)) := by
  classical
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact distinctBooleanPairSyndromeFiber_card q s n hq hqodd hε hη hε0 hη0 hneq y z

private abbrev DistinctNonzeroBooleanPair (q n : Nat) :=
  {p : NonzeroBooleanVector q n × NonzeroBooleanVector q n // p.1 ≠ p.2}

private noncomputable instance distinctNonzeroBooleanPairFintype
    (q n : Nat) [NeZero q] : Fintype (DistinctNonzeroBooleanPair q n) := by
  classical
  refine Fintype.subtype
    (Finset.univ.filter fun p : NonzeroBooleanVector q n × NonzeroBooleanVector q n =>
      p.1 ≠ p.2) ?_
  intro p
  simp

private theorem distinctNonzeroBooleanPair_card (q n : Nat) [NeZero q] :
    Fintype.card (DistinctNonzeroBooleanPair q n) =
      Fintype.card (NonzeroBooleanVector q n) *
        (Fintype.card (NonzeroBooleanVector q n) - 1) := by
  classical
  let B := NonzeroBooleanVector q n
  let Pair := DistinctNonzeroBooleanPair q n
  let e : Pair ≃ Sigma (fun ε : B => {η : B // ε ≠ η}) :=
    { toFun := fun p : Pair => ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
      invFun := fun p : Sigma (fun ε : B => {η : B // ε ≠ η}) =>
        ⟨(p.1, p.2.1), p.2.2⟩
      left_inv := by
        intro p
        rcases p with ⟨⟨ε, η⟩, hne⟩
        rfl
      right_inv := by
        intro p
        rcases p with ⟨ε, η, hne⟩
        rfl }
  rw [show Fintype.card Pair = Fintype.card (Sigma fun ε : B => {η : B // ε ≠ η}) by
    exact Fintype.card_congr e]
  rw [Fintype.card_sigma]
  calc
    (∑ ε : B, Fintype.card {η : B // ε ≠ η}) =
        (∑ _ε : B, (Fintype.card B - 1)) := by
          apply Finset.sum_congr rfl
          intro ε _hε
          have hsingle : Fintype.card {η : B // η = ε} = 1 := by
            rw [Fintype.card_eq_one_iff]
            refine ⟨⟨ε, rfl⟩, ?_⟩
            intro η
            exact Subtype.ext η.2
          have hsingle' : Fintype.card {η : B // ε = η} = 1 := by
            rw [Fintype.card_eq_one_iff]
            refine ⟨⟨ε, rfl⟩, ?_⟩
            intro η
            exact Subtype.ext η.2.symm
          rw [Fintype.card_subtype_compl (fun η : B => ε = η), hsingle']
    _ = Fintype.card B * (Fintype.card B - 1) := by
          simp

private noncomputable def fixedSyndromePairIncidence
    (q s n : Nat) (y : Fin s -> ZMod q) :=
  {p : Matrix (Fin s) (Fin n) (ZMod q) × DistinctNonzeroBooleanPair q n //
    finiteFieldMatVec q s n p.1 p.2.1.1.1 = y ∧
      finiteFieldMatVec q s n p.1 p.2.1.2.1 = y}

private noncomputable def fixedSyndromePairFiber
    (q s n : Nat) (y : Fin s -> ZMod q) (p : DistinctNonzeroBooleanPair q n) :=
  {H : Matrix (Fin s) (Fin n) (ZMod q) //
    finiteFieldMatVec q s n H p.1.1.1 = y ∧
      finiteFieldMatVec q s n H p.1.2.1 = y}

private noncomputable instance fixedSyndromePairIncidenceFintype
    (q s n : Nat) [NeZero q] (y : Fin s -> ZMod q) :
    Fintype (fixedSyndromePairIncidence q s n y) := by
  classical
  refine Fintype.subtype
    (Finset.univ.filter fun p : Matrix (Fin s) (Fin n) (ZMod q) ×
        DistinctNonzeroBooleanPair q n =>
      finiteFieldMatVec q s n p.1 p.2.1.1.1 = y ∧
        finiteFieldMatVec q s n p.1 p.2.1.2.1 = y) ?_
  intro p
  simp

private noncomputable instance fixedSyndromePairFiberFintype
    (q s n : Nat) [NeZero q] (y : Fin s -> ZMod q)
    (p : DistinctNonzeroBooleanPair q n) :
    Fintype (fixedSyndromePairFiber q s n y p) := by
  classical
  refine Fintype.subtype
    (Finset.univ.filter fun H : Matrix (Fin s) (Fin n) (ZMod q) =>
      finiteFieldMatVec q s n H p.1.1.1 = y ∧
        finiteFieldMatVec q s n H p.1.2.1 = y) ?_
  intro H
  simp

private theorem fixedSyndromePairIncidence_card_mul
    (q s n : Nat) [NeZero q] (hq : Nat.Prime q) (hqodd : Odd q)
    (y : Fin s -> ZMod q) :
    Fintype.card (fixedSyndromePairIncidence q s n y) * q ^ (2 * s) =
      Fintype.card (DistinctNonzeroBooleanPair q n) *
        Fintype.card (Matrix (Fin s) (Fin n) (ZMod q)) := by
  classical
  let Ω := Matrix (Fin s) (Fin n) (ZMod q)
  let Pair := DistinctNonzeroBooleanPair q n
  let Inc := fixedSyndromePairIncidence q s n y
  let Fiber := fixedSyndromePairFiber q s n y
  let e : Inc ≃ Sigma Fiber :=
    { toFun := fun p : Inc => ⟨p.1.2, ⟨p.1.1, p.2⟩⟩
      invFun := fun p : Sigma Fiber => ⟨(p.2.1, p.1), p.2.2⟩
      left_inv := by
        intro p
        rcases p with ⟨⟨H, pair⟩, hp⟩
        rfl
      right_inv := by
        intro p
        rcases p with ⟨pair, H, hp⟩
        rfl }
  have hcard :
      Fintype.card Inc = Fintype.card (Sigma Fiber) :=
    Fintype.card_congr e
  rw [hcard, Fintype.card_sigma]
  calc
    (∑ p : Pair, Fintype.card (Fiber p)) * q ^ (2 * s) =
        ∑ p : Pair, Fintype.card (Fiber p) * q ^ (2 * s) := by
          rw [Finset.sum_mul]
    _ = ∑ _p : Pair, Fintype.card Ω := by
          apply Finset.sum_congr rfl
          intro p _hp
          have hneq : p.1.1.1 ≠ p.1.2.1 := by
            intro hval
            exact p.2 (Subtype.ext hval)
          simpa [Fiber, Ω] using
            distinctBooleanPairSyndromeFiber_card q s n hq hqodd
              p.1.1.2.1 p.1.2.2.1 p.1.1.2.2 p.1.2.2.2 hneq y y
    _ = Fintype.card Pair * Fintype.card Ω := by
          simp

private noncomputable def fixedSyndromePreimage
    (q s n : Nat) (y : Fin s -> ZMod q)
    (H : Matrix (Fin s) (Fin n) (ZMod q)) :=
  {ε : NonzeroBooleanVector q n // finiteFieldMatVec q s n H ε.1 = y}

private noncomputable instance fixedSyndromePreimageFintype
    (q s n : Nat) [NeZero q] (y : Fin s -> ZMod q)
    (H : Matrix (Fin s) (Fin n) (ZMod q)) :
    Fintype (fixedSyndromePreimage q s n y H) := by
  classical
  refine Fintype.subtype
    (Finset.univ.filter fun ε : NonzeroBooleanVector q n =>
      finiteFieldMatVec q s n H ε.1 = y) ?_
  intro ε
  simp

private noncomputable def fixedSyndromeSquareIncidence
    (q s n : Nat) (y : Fin s -> ZMod q) :=
  {p : Matrix (Fin s) (Fin n) (ZMod q) ×
      (NonzeroBooleanVector q n × NonzeroBooleanVector q n) //
    finiteFieldMatVec q s n p.1 p.2.1.1 = y ∧
      finiteFieldMatVec q s n p.1 p.2.2.1 = y}

private noncomputable instance fixedSyndromeSquareIncidenceFintype
    (q s n : Nat) [NeZero q] (y : Fin s -> ZMod q) :
    Fintype (fixedSyndromeSquareIncidence q s n y) := by
  classical
  refine Fintype.subtype
    (Finset.univ.filter fun p : Matrix (Fin s) (Fin n) (ZMod q) ×
        (NonzeroBooleanVector q n × NonzeroBooleanVector q n) =>
      finiteFieldMatVec q s n p.1 p.2.1.1 = y ∧
        finiteFieldMatVec q s n p.1 p.2.2.1 = y) ?_
  intro p
  simp

private theorem fixedSyndromeSquareIncidence_card
    (q s n : Nat) [NeZero q] (y : Fin s -> ZMod q) :
    Fintype.card (fixedSyndromeSquareIncidence q s n y) =
      Fintype.card (fixedSyndromeIncidence q s n y) +
        Fintype.card (fixedSyndromePairIncidence q s n y) := by
  classical
  let Square := fixedSyndromeSquareIncidence q s n y
  let Inc := fixedSyndromeIncidence q s n y
  let PairInc := fixedSyndromePairIncidence q s n y
  let e : Square ≃ Inc ⊕ PairInc :=
    { toFun := fun p : Square =>
        if h : p.1.2.1 = p.1.2.2 then
          Sum.inl ⟨(p.1.1, p.1.2.1), p.2.1⟩
        else
          Sum.inr ⟨(p.1.1, ⟨(p.1.2.1, p.1.2.2), h⟩), p.2⟩
      invFun := fun p : Inc ⊕ PairInc =>
        match p with
        | Sum.inl h =>
            ⟨(h.1.1, (h.1.2, h.1.2)), h.2, h.2⟩
        | Sum.inr h =>
            ⟨(h.1.1, (h.1.2.1.1, h.1.2.1.2)), h.2⟩
      left_inv := by
        intro p
        rcases p with ⟨⟨H, ε, η⟩, hε, hη⟩
        dsimp
        by_cases h : ε = η
        · subst η
          simp
        · simp [h]
      right_inv := by
        intro p
        cases p with
        | inl h =>
            rcases h with ⟨⟨H, ε⟩, hε⟩
            simp
        | inr h =>
            rcases h with ⟨⟨H, pair⟩, hε, hη⟩
            simp [pair.2] }
  rw [show Fintype.card Square = Fintype.card (Inc ⊕ PairInc) by
    exact Fintype.card_congr e]
  rw [Fintype.card_sum]

private theorem fixedSyndromeSquareIncidence_card_mul
    (q s n : Nat) [NeZero q] (hq : Nat.Prime q) (hqodd : Odd q)
    (hn : 1 ≤ n) (y : Fin s -> ZMod q) :
    Fintype.card (fixedSyndromeSquareIncidence q s n y) * q ^ (2 * s) =
      Fintype.card (Matrix (Fin s) (Fin n) (ZMod q)) *
        Fintype.card (NonzeroBooleanVector q n) *
          (Fintype.card (NonzeroBooleanVector q n) + q ^ s - 1) := by
  classical
  let Ω := Matrix (Fin s) (Fin n) (ZMod q)
  let B := Fintype.card (NonzeroBooleanVector q n)
  let Q := q ^ s
  let Square := fixedSyndromeSquareIncidence q s n y
  let Inc := fixedSyndromeIncidence q s n y
  let PairInc := fixedSyndromePairIncidence q s n y
  let Pair := DistinctNonzeroBooleanPair q n
  have hQ2 : q ^ (2 * s) = Q * Q := by
    rw [show 2 * s = s + s by omega, pow_add]
  have hInc : Fintype.card Inc * Q = B * Fintype.card Ω := by
    simpa [Inc, B, Ω, Q] using fixedSyndromeIncidence_card_mul q s n hq y
  have hPair : Fintype.card PairInc * q ^ (2 * s) = Fintype.card Pair * Fintype.card Ω := by
    simpa [PairInc, Pair, Ω] using fixedSyndromePairIncidence_card_mul q s n hq hqodd y
  have hPairQ : Fintype.card PairInc * (Q * Q) = Fintype.card Pair * Fintype.card Ω := by
    simpa [← hQ2] using hPair
  have hPairCard : Fintype.card Pair = B * (B - 1) := by
    simpa [Pair, B] using distinctNonzeroBooleanPair_card q n
  have hBpos : 0 < B := by
    have hBcard : B = 2 ^ n - 1 := by
      simpa [B] using nonzeroBooleanVector_fintype_card q n hq
    have hpow : 1 < 2 ^ n := by
      cases n with
      | zero => omega
      | succ k =>
          have hpos : 0 < 2 ^ k := pow_pos (by norm_num : 0 < (2 : Nat)) k
          change 1 < 2 ^ k * 2
          calc
            1 < 1 * 2 := by norm_num
            _ ≤ 2 ^ k * 2 := Nat.mul_le_mul_right 2 hpos
    rw [hBcard]
    omega
  calc
    Fintype.card Square * q ^ (2 * s) =
        (Fintype.card Inc + Fintype.card PairInc) * q ^ (2 * s) := by
          rw [fixedSyndromeSquareIncidence_card q s n y]
    _ = Fintype.card Inc * q ^ (2 * s) +
          Fintype.card PairInc * q ^ (2 * s) := by
          ring
    _ = (B * Fintype.card Ω) * Q + (B * (B - 1)) * Fintype.card Ω := by
          rw [hQ2]
          rw [show Fintype.card Inc * (Q * Q) = (Fintype.card Inc * Q) * Q by ring]
          rw [hInc, hPairQ, hPairCard]
    _ = Fintype.card Ω * B * (B + Q - 1) := by
          have hBQ : B + Q - 1 = (B - 1) + Q := by omega
          rw [hBQ]
          ring

/-- A Construction-A kernel predicate on integer vectors. -/
def InConstructionAKernel (q s n : Nat)
    (H : Matrix (Fin s) (Fin n) (ZMod q)) (z : Fin n -> Int) : Prop :=
  constructionASyndrome q s n H z = 0

private lemma constructionASyndrome_add
    (q s n : Nat) (H : Matrix (Fin s) (Fin n) (ZMod q))
    (z w : Fin n -> Int) :
    constructionASyndrome q s n H (z + w) =
      constructionASyndrome q s n H z + constructionASyndrome q s n H w := by
  funext i
  simp [constructionASyndrome, finiteFieldMatVec, intVectorMod,
    Finset.sum_add_distrib, mul_add]

private lemma constructionASyndrome_neg
    (q s n : Nat) (H : Matrix (Fin s) (Fin n) (ZMod q)) (z : Fin n -> Int) :
    constructionASyndrome q s n H (-z) = -constructionASyndrome q s n H z := by
  funext i
  simp [constructionASyndrome, finiteFieldMatVec, intVectorMod]

private lemma intVectorMod_q_mul (q n : Nat) (z : Fin n -> Int) :
    intVectorMod q n (fun i => (q : Int) * z i) = 0 := by
  funext i
  simp [intVectorMod]

private lemma constructionASyndrome_q_mul
    (q s n : Nat) (H : Matrix (Fin s) (Fin n) (ZMod q)) (z : Fin n -> Int) :
    constructionASyndrome q s n H (fun i => (q : Int) * z i) = 0 := by
  funext i
  simp [constructionASyndrome, finiteFieldMatVec, intVectorMod]

private noncomputable def constructionASyndromeLinearMap
    (q s n : Nat) (H : Matrix (Fin s) (Fin n) (ZMod q)) :
    (Fin n -> Int) →ₗ[Int] (Fin s -> ZMod q) where
  toFun := constructionASyndrome q s n H
  map_add' z w := by
    funext i
    simp [constructionASyndrome, finiteFieldMatVec, intVectorMod, Finset.sum_add_distrib,
      mul_add]
  map_smul' a z := by
    funext i
    simp [constructionASyndrome, finiteFieldMatVec, intVectorMod, Finset.mul_sum,
      mul_left_comm]

private noncomputable def constructionAKernelIntSubmodule
    (q s n : Nat) (H : Matrix (Fin s) (Fin n) (ZMod q)) :
    Submodule Int (Fin n -> Int) :=
  (constructionASyndromeLinearMap q s n H).ker

private lemma constructionAKernelIntSubmodule_finite_quotient
    (q s n : Nat) [NeZero q] (H : Matrix (Fin s) (Fin n) (ZMod q)) :
    Finite ((Fin n -> Int) ⧸ constructionAKernelIntSubmodule q s n H) := by
  let f := constructionASyndromeLinearMap q s n H
  change Finite ((Fin n -> Int) ⧸ f.ker)
  haveI : Finite (Fin s -> ZMod q) := Finite.of_fintype (Fin s -> ZMod q)
  haveI : Finite (LinearMap.range f) :=
    Finite.of_injective (fun y : LinearMap.range f => (y : Fin s -> ZMod q))
      Subtype.val_injective
  exact Finite.of_equiv (LinearMap.range f) (LinearMap.quotKerEquivRange f).toEquiv.symm

private lemma constructionAKernelIntSubmodule_finrank
    (q s n : Nat) [NeZero q] (H : Matrix (Fin s) (Fin n) (ZMod q)) :
    Module.finrank Int (constructionAKernelIntSubmodule q s n H) =
      Module.finrank Int (Fin n -> Int) := by
  exact (Submodule.finiteQuotient_iff (constructionAKernelIntSubmodule q s n H)).1
    (constructionAKernelIntSubmodule_finite_quotient q s n H)

private noncomputable def constructionAKernelIntBasis
    (q s n : Nat) [NeZero q] (H : Matrix (Fin s) (Fin n) (ZMod q)) :
    Module.Basis (Fin n) Int (constructionAKernelIntSubmodule q s n H) :=
  Submodule.smithNormalFormBotBasis (Pi.basisFun Int (Fin n))
    (constructionAKernelIntSubmodule_finrank q s n H)

private noncomputable def constructionAKernelBasisMatrix
    (q s n : Nat) [NeZero q] (H : Matrix (Fin s) (Fin n) (ZMod q)) :
    Matrix (Fin n) (Fin n) Real :=
  fun i j =>
    (((constructionAKernelIntBasis q s n H j :
      constructionAKernelIntSubmodule q s n H) : Fin n -> Int) i : Real)

private lemma constructionAKernelIntBasis_det_ne_zero
    (q s n : Nat) [NeZero q] (H : Matrix (Fin s) (Fin n) (ZMod q)) :
    (Pi.basisFun Int (Fin n)).det
        ((↑) ∘ constructionAKernelIntBasis q s n H) ≠ 0 := by
  let N := constructionAKernelIntSubmodule q s n H
  let bN := constructionAKernelIntBasis q s n H
  haveI : Finite ((Fin n -> Int) ⧸ N) :=
    constructionAKernelIntSubmodule_finite_quotient q s n H
  have hcard_ne : Nat.card ((Fin n -> Int) ⧸ N) ≠ 0 :=
    Nat.card_pos.ne'
  have hdet_card :
      ((Pi.basisFun Int (Fin n)).det ((↑) ∘ bN)).natAbs =
        Nat.card ((Fin n -> Int) ⧸ N) :=
    Submodule.natAbs_det_basis_change (Pi.basisFun Int (Fin n)) N bN
  intro hdet
  have hdet' : (Matrix.of ((↑) ∘ bN) : Matrix (Fin n) (Fin n) Int).det = 0 := by
    rw [← Pi.basisFun_det_apply]
    simpa [bN] using hdet
  apply hcard_ne
  rw [← hdet_card]
  rw [Pi.basisFun_det_apply]
  simp [hdet']

private lemma constructionAKernelBasisMatrix_det_ne_zero
    (q s n : Nat) [NeZero q] (H : Matrix (Fin s) (Fin n) (ZMod q)) :
    (constructionAKernelBasisMatrix q s n H).det ≠ 0 := by
  let N := constructionAKernelIntSubmodule q s n H
  let bN := constructionAKernelIntBasis q s n H
  let B : Matrix (Fin n) (Fin n) Int := Matrix.of ((↑) ∘ bN)
  have hBdet : B.det ≠ 0 := by
    simpa [B, bN] using constructionAKernelIntBasis_det_ne_zero q s n H
  have hdet_cast :
      (constructionAKernelBasisMatrix q s n H).det = (B.det : Real) := by
    have hmatrix :
        constructionAKernelBasisMatrix q s n H =
          B.transpose.map (Int.castRingHom Real) := by
      ext i j
      simp [constructionAKernelBasisMatrix, B, bN]
    calc
      (constructionAKernelBasisMatrix q s n H).det =
          ((B.transpose.map (Int.castRingHom Real)).det) := by
            rw [hmatrix]
      _ = ((B.map (Int.castRingHom Real)).transpose).det := by
            have hmap :
                B.transpose.map (Int.castRingHom Real) =
                  (B.map (Int.castRingHom Real)).transpose := by
              ext i j
              simp
            rw [hmap]
      _ = (B.map (Int.castRingHom Real)).det := by
            rw [Matrix.det_transpose]
      _ = (B.det : Real) := by
            simpa using (Int.cast_det (R := Real) B).symm
  intro hzero
  have hBzero : (B.det : Real) = 0 := by
    simpa [hdet_cast] using hzero
  exact hBdet (Int.cast_injective (α := Real) (by simpa using hBzero))

private noncomputable def constructionAKernelLatticeBasis
    (q s n : Nat) [NeZero q] (H : Matrix (Fin s) (Fin n) (ZMod q)) :
    LatticeBasis n where
  matrix := constructionAKernelBasisMatrix q s n H
  invertible :=
    isUnit_iff_ne_zero.mpr (constructionAKernelBasisMatrix_det_ne_zero q s n H)

private lemma constructionAKernelBasisMatrix_mul_integerVector
    (q s n : Nat) [NeZero q] (H : Matrix (Fin s) (Fin n) (ZMod q))
    (k : Fin n -> Int) :
    Matrix.toEuclideanLin (constructionAKernelBasisMatrix q s n H) (integerVector n k) =
      integerVector n
        (((∑ j : Fin n, k j • constructionAKernelIntBasis q s n H j) :
          constructionAKernelIntSubmodule q s n H) : Fin n -> Int) := by
  ext i
  simp [Matrix.toEuclideanLin, Matrix.mulVec, dotProduct, constructionAKernelBasisMatrix,
    integerVector, mul_comm]

private lemma mem_constructionAKernelIntSubmodule_iff
    (q s n : Nat) (H : Matrix (Fin s) (Fin n) (ZMod q)) (z : Fin n -> Int) :
    z ∈ constructionAKernelIntSubmodule q s n H ↔ InConstructionAKernel q s n H z := by
  rfl

private lemma constructionAKernelBasisMatrix_repr_integerVector
    (q s n : Nat) [NeZero q] (H : Matrix (Fin s) (Fin n) (ZMod q))
    (z : Fin n -> Int) (hz : InConstructionAKernel q s n H z) :
    Matrix.toEuclideanLin (constructionAKernelBasisMatrix q s n H)
        (integerVector n
          (fun j => (constructionAKernelIntBasis q s n H).repr
            ⟨z, (mem_constructionAKernelIntSubmodule_iff q s n H z).2 hz⟩ j)) =
      integerVector n z := by
  let N := constructionAKernelIntSubmodule q s n H
  let bN := constructionAKernelIntBasis q s n H
  let zN : N := ⟨z, (mem_constructionAKernelIntSubmodule_iff q s n H z).2 hz⟩
  have hsum : (∑ j : Fin n, bN.repr zN j • bN j : N) = zN := by
    simpa [bN] using (bN.sum_repr zN)
  calc
    Matrix.toEuclideanLin (constructionAKernelBasisMatrix q s n H)
        (integerVector n (fun j => (constructionAKernelIntBasis q s n H).repr
          ⟨z, (mem_constructionAKernelIntSubmodule_iff q s n H z).2 hz⟩ j)) =
        integerVector n
          (((∑ j : Fin n, bN.repr zN j • bN j) : N) : Fin n -> Int) := by
          simpa [bN, zN] using
            constructionAKernelBasisMatrix_mul_integerVector q s n H
              (fun j => bN.repr zN j)
    _ = integerVector n z := by
          rw [hsum]

private lemma q_smul_mem_constructionAKernelIntSubmodule
    (q s n : Nat) (H : Matrix (Fin s) (Fin n) (ZMod q)) (z : Fin n -> Int) :
    (q : Int) • z ∈ constructionAKernelIntSubmodule q s n H := by
  rw [mem_constructionAKernelIntSubmodule_iff]
  change constructionASyndrome q s n H ((q : Int) • z) = 0
  simpa using constructionASyndrome_q_mul q s n H z

private noncomputable def constructionAKernelAddSubgroup
    (q s n : Nat) (H : Matrix (Fin s) (Fin n) (ZMod q)) :
    AddSubgroup (RealEuclideanSpace n) where
  carrier := {x | ∃ z : Fin n -> Int, x = integerVector n z ∧ InConstructionAKernel q s n H z}
  zero_mem' := by
    refine ⟨0, ?_, ?_⟩
    · ext i
      simp [integerVector]
    · funext i
      simp [constructionASyndrome, finiteFieldMatVec, intVectorMod]
  add_mem' := by
    intro x y hx hy
    rcases hx with ⟨z, rfl, hz⟩
    rcases hy with ⟨w, rfl, hw⟩
    refine ⟨z + w, ?_, ?_⟩
    · ext i
      simp [integerVector]
    · unfold InConstructionAKernel at hz hw ⊢
      rw [constructionASyndrome_add]
      simp [hz, hw]
  neg_mem' := by
    intro x hx
    rcases hx with ⟨z, rfl, hz⟩
    refine ⟨-z, ?_, ?_⟩
    · ext i
      simp [integerVector]
    · unfold InConstructionAKernel at hz ⊢
      rw [constructionASyndrome_neg, hz, neg_zero]

private lemma constructionAKernel_lattice_carrier_eq
    (q s n : Nat) [NeZero q] (H : Matrix (Fin s) (Fin n) (ZMod q)) :
    (⟨constructionAKernelLatticeBasis q s n H⟩ : KNFullRankLattice n).carrier =
      constructionAKernelAddSubgroup q s n H := by
  ext x
  constructor
  · intro hx
    simp [KNFullRankLattice.carrier, matrixIntegerLattice, integerLattice,
      constructionAKernelLatticeBasis] at hx
    rcases hx with ⟨k, rfl⟩
    let zN : constructionAKernelIntSubmodule q s n H :=
      ∑ j : Fin n, k j • constructionAKernelIntBasis q s n H j
    refine ⟨(zN : Fin n -> Int), ?_, ?_⟩
    · exact constructionAKernelBasisMatrix_mul_integerVector q s n H k
    · exact (mem_constructionAKernelIntSubmodule_iff q s n H (zN : Fin n -> Int)).1
        zN.property
  · rintro ⟨z, rfl, hz⟩
    simp [KNFullRankLattice.carrier, matrixIntegerLattice, integerLattice,
      constructionAKernelLatticeBasis]
    refine ⟨fun j =>
      (constructionAKernelIntBasis q s n H).repr
        ⟨z, (mem_constructionAKernelIntSubmodule_iff q s n H z).2 hz⟩ j, ?_⟩
    exact constructionAKernelBasisMatrix_repr_integerVector q s n H z hz

private lemma q_integerVector_mem_constructionAKernel
    (q s n : Nat) (H : Matrix (Fin s) (Fin n) (ZMod q)) (z : Fin n -> Int) :
    integerVector n (fun i => (q : Int) * z i) ∈
      constructionAKernelAddSubgroup q s n H := by
  refine ⟨fun i => (q : Int) * z i, rfl, ?_⟩
  exact constructionASyndrome_q_mul q s n H z

private lemma integerVector_mem_constructionAKernelAddSubgroup_iff
    (q s n : Nat) (H : Matrix (Fin s) (Fin n) (ZMod q)) (z : Fin n -> Int) :
    integerVector n z ∈ constructionAKernelAddSubgroup q s n H ↔
      InConstructionAKernel q s n H z := by
  constructor
  · rintro ⟨w, hw, hwker⟩
    have hzw : z = w := by
      funext i
      have hcoord := congrArg (fun x : RealEuclideanSpace n => (x : Fin n -> Real) i) hw
      norm_num [integerVector] at hcoord
      exact_mod_cast hcoord
    simpa [hzw]
  · intro hz
    exact ⟨z, rfl, hz⟩

private lemma integerVector_eq_zero_iff (n : Nat) (z : Fin n -> Int) :
    integerVector n z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    funext i
    have hcoord := congrArg (fun x : RealEuclideanSpace n => (x : Fin n -> Real) i) hz
    norm_num [integerVector] at hcoord
    exact_mod_cast hcoord
  · intro hz
    ext i
    simp [integerVector, hz]

private lemma norm_le_sqrt_card_mul_of_coord_abs_le {n : Nat}
    (x : RealEuclideanSpace n) {a : Real} (ha : 0 ≤ a)
    (hx : ∀ i : Fin n, |x i| ≤ a) :
    ‖x‖ ≤ Real.sqrt (n : Real) * a := by
  have hsq : ‖x‖ ^ 2 ≤ (Real.sqrt (n : Real) * a) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      (∑ i : Fin n, ‖x.ofLp i‖ ^ 2) ≤ ∑ _i : Fin n, a ^ 2 := by
        apply Finset.sum_le_sum
        intro i _hi
        have hxi : ‖x.ofLp i‖ ≤ a := by
          simpa [Real.norm_eq_abs] using hx i
        exact sq_le_sq' (by linarith [ha, norm_nonneg (x.ofLp i)]) hxi
      _ = (n : Real) * a ^ 2 := by simp
      _ = (Real.sqrt (n : Real) * a) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by exact_mod_cast Nat.zero_le n)]
  have hright : 0 ≤ Real.sqrt (n : Real) * a :=
    mul_nonneg (Real.sqrt_nonneg _) ha
  have habs := sq_le_sq.mp hsq
  simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hright] using habs

private lemma integerVector_boolean_norm_le_sqrt {n : Nat} (ε : Fin n -> Int)
    (hε : ∀ i : Fin n, ε i = 0 ∨ ε i = 1) :
    ‖integerVector n ε‖ ≤ Real.sqrt (n : Real) := by
  have h := norm_le_sqrt_card_mul_of_coord_abs_le
    (integerVector n ε) (by norm_num : (0 : Real) ≤ 1) ?_
  · simpa using h
  intro i
  rcases hε i with hεi | hεi <;> simp [integerVector, hεi]

private lemma rounded_integerVector_error_norm_le {n : Nat} (x : RealEuclideanSpace n) :
    ‖x - integerVector n (fun i : Fin n => round (x i))‖ ≤
      (1 / 2 : Real) * Real.sqrt (n : Real) := by
  have h := norm_le_sqrt_card_mul_of_coord_abs_le
    (x - integerVector n (fun i : Fin n => round (x i)))
    (by norm_num : (0 : Real) ≤ (1 / 2 : Real)) ?_
  · simpa [mul_comm] using h
  intro i
  simpa [integerVector] using abs_sub_round (x i)

private lemma constructionAKernel_shortest_bound_of_carrier_eq
    {q s n : Nat} {H : Matrix (Fin s) (Fin n) (ZMod q)}
    {Γ : KNFullRankLattice n} (hn : 1 ≤ n)
    (hcarrier : Γ.carrier = constructionAKernelAddSubgroup q s n H) {N : Real}
    (hN : ∀ z : Fin n -> Int, z ≠ 0 -> InConstructionAKernel q s n H z ->
      N ≤ ‖integerVector n z‖) :
    N ≤ shortestVectorLength Γ := by
  refine shortestVectorLength_least hn Γ ?_
  intro γ hγ hγne
  rw [hcarrier] at hγ
  rcases hγ with ⟨z, rfl, hzker⟩
  exact hN z (by
    intro hz
    apply hγne
    rw [hz]
    ext i
    simp [integerVector]) hzker

private lemma constructionAKernel_shortest_bound_of_no_short_vector
    {q s n : Nat} {H : Matrix (Fin s) (Fin n) (ZMod q)}
    {Γ : KNFullRankLattice n} (hn : 1 ≤ n)
    (hcarrier : Γ.carrier = constructionAKernelAddSubgroup q s n H) {N : Real}
    (hN : ∀ z : Fin n -> Int, z ≠ 0 -> InConstructionAKernel q s n H z ->
      ¬ ‖integerVector n z‖ < N) :
    N ≤ shortestVectorLength Γ := by
  refine constructionAKernel_shortest_bound_of_carrier_eq hn hcarrier ?_
  intro z hz0 hzker
  exact le_of_not_gt (hN z hz0 hzker)

private lemma constructionAKernel_covering_bound_of_pointwise
    {q s n : Nat} {H : Matrix (Fin s) (Fin n) (ZMod q)}
    {Γ : KNFullRankLattice n} (hcarrier : Γ.carrier = constructionAKernelAddSubgroup q s n H)
    {R : Real}
    (hR : ∀ x : RealEuclideanSpace n,
      ∃ z : Fin n -> Int, InConstructionAKernel q s n H z ∧
        ‖x - integerVector n z‖ ≤ R) :
    coveringRadius Γ ≤ R := by
  refine coveringRadius_le_of_distanceToLattice_le Γ ?_
  intro x
  rcases hR x with ⟨z, hzker, hzdist⟩
  have hzmem : integerVector n z ∈ Γ.carrier := by
    rw [hcarrier]
    exact (integerVector_mem_constructionAKernelAddSubgroup_iff q s n H z).2 hzker
  exact (distanceToLattice_le_norm_sub Γ x (integerVector n z) hzmem).trans hzdist

private lemma constructionASyndrome_sub
    (q s n : Nat) (H : Matrix (Fin s) (Fin n) (ZMod q))
    (z w : Fin n -> Int) :
    constructionASyndrome q s n H (z - w) =
      constructionASyndrome q s n H z - constructionASyndrome q s n H w := by
  rw [sub_eq_add_neg, constructionASyndrome_add, constructionASyndrome_neg]
  simp [sub_eq_add_neg]

private lemma constructionAKernel_pointwise_covering_of_syndrome_surjective
    {q s n : Nat} {H : Matrix (Fin s) (Fin n) (ZMod q)}
    (hcover : ∀ y : Fin s -> ZMod q,
      ∃ ε : Fin n -> Int,
        (∀ i : Fin n, ε i = 0 ∨ ε i = 1) ∧ constructionASyndrome q s n H ε = y) :
    ∀ x : RealEuclideanSpace n,
      ∃ z : Fin n -> Int, InConstructionAKernel q s n H z ∧
        ‖x - integerVector n z‖ ≤ (3 / 2 : Real) * Real.sqrt (n : Real) := by
  intro x
  let m : Fin n -> Int := fun i => round (x i)
  obtain ⟨ε, hεbool, hεsyn⟩ := hcover (constructionASyndrome q s n H m)
  let z : Fin n -> Int := m - ε
  refine ⟨z, ?_, ?_⟩
  · unfold InConstructionAKernel
    rw [constructionASyndrome_sub, hεsyn]
    simp
  · have hdecomp :
        x - integerVector n z =
          (x - integerVector n m) + integerVector n ε := by
      ext i
      simp [z, m, integerVector]
      ring
    rw [hdecomp]
    calc
      ‖(x - integerVector n m) + integerVector n ε‖ ≤
          ‖x - integerVector n m‖ + ‖integerVector n ε‖ := norm_add_le _ _
      _ ≤ (1 / 2 : Real) * Real.sqrt (n : Real) + Real.sqrt (n : Real) := by
        exact add_le_add (rounded_integerVector_error_norm_le x)
          (integerVector_boolean_norm_le_sqrt ε hεbool)
      _ = (3 / 2 : Real) * Real.sqrt (n : Real) := by ring

private lemma constructionAKernel_lattice_bounds_of_carrier_eq
    {q s n : Nat} {H : Matrix (Fin s) (Fin n) (ZMod q)}
    {Γ : KNFullRankLattice n} (hn : 1 ≤ n)
    (hcarrier : Γ.carrier = constructionAKernelAddSubgroup q s n H) {N R : Real}
    (hN : ∀ z : Fin n -> Int, z ≠ 0 -> InConstructionAKernel q s n H z ->
      N ≤ ‖integerVector n z‖)
    (hR : ∀ x : RealEuclideanSpace n,
      ∃ z : Fin n -> Int, InConstructionAKernel q s n H z ∧
        ‖x - integerVector n z‖ ≤ R) :
    N ≤ shortestVectorLength Γ ∧ coveringRadius Γ ≤ R :=
  ⟨constructionAKernel_shortest_bound_of_carrier_eq hn hcarrier hN,
    constructionAKernel_covering_bound_of_pointwise hcarrier hR⟩

private lemma exists_constructionAKernel_lattice_bounds
    {q s n : Nat} [NeZero q] (H : Matrix (Fin s) (Fin n) (ZMod q))
    (hn : 1 ≤ n) {N R : Real}
    (hN : ∀ z : Fin n -> Int, z ≠ 0 -> InConstructionAKernel q s n H z ->
      N ≤ ‖integerVector n z‖)
    (hR : ∀ x : RealEuclideanSpace n,
      ∃ z : Fin n -> Int, InConstructionAKernel q s n H z ∧
        ‖x - integerVector n z‖ ≤ R) :
    ∃ Γ : KNFullRankLattice n, N ≤ shortestVectorLength Γ ∧ coveringRadius Γ ≤ R := by
  let Γ : KNFullRankLattice n := ⟨constructionAKernelLatticeBasis q s n H⟩
  refine ⟨Γ, ?_⟩
  exact constructionAKernel_lattice_bounds_of_carrier_eq hn
    (constructionAKernel_lattice_carrier_eq q s n H) hN hR

private lemma exists_constructionAKernel_lattice_bounds_of_good_matrix
    {q s n : Nat} [NeZero q] (H : Matrix (Fin s) (Fin n) (ZMod q)) (hn : 1 ≤ n)
    (hshort : ∀ z : Fin n -> Int, z ≠ 0 -> InConstructionAKernel q s n H z ->
      ¬ ‖integerVector n z‖ < (1 / 10 : Real) * Real.sqrt (n : Real))
    (hcover : ∀ y : Fin s -> ZMod q,
      ∃ ε : Fin n -> Int,
        (∀ i : Fin n, ε i = 0 ∨ ε i = 1) ∧ constructionASyndrome q s n H ε = y) :
    ∃ Γ : KNFullRankLattice n,
      (1 / 10 : Real) * Real.sqrt (n : Real) ≤ shortestVectorLength Γ ∧
        coveringRadius Γ ≤ (3 / 2 : Real) * Real.sqrt (n : Real) := by
  refine exists_constructionAKernel_lattice_bounds H hn ?_ ?_
  · intro z hz0 hzker
    exact le_of_not_gt (hshort z hz0 hzker)
  · exact constructionAKernel_pointwise_covering_of_syndrome_surjective hcover

private lemma exists_primeSquare_constructionAKernel_lattice_bounds_of_good_matrix
    {q s : Nat} [NeZero q] (hq : Nat.Prime q)
    (H : Matrix (Fin s) (Fin (q * q)) (ZMod q))
    (hshort : ∀ z : Fin (q * q) -> Int, z ≠ 0 ->
      InConstructionAKernel q s (q * q) H z ->
        ¬ ‖integerVector (q * q) z‖ <
          (1 / 10 : Real) * Real.sqrt ((q * q : Nat) : Real))
    (hcover : ∀ y : Fin s -> ZMod q,
      ∃ ε : Fin (q * q) -> Int,
        (∀ i : Fin (q * q), ε i = 0 ∨ ε i = 1) ∧
          constructionASyndrome q s (q * q) H ε = y) :
    ∃ Γ : KNFullRankLattice (q * q),
      (1 / 10 : Real) * Real.sqrt ((q * q : Nat) : Real) ≤ shortestVectorLength Γ ∧
        coveringRadius Γ ≤ (3 / 2 : Real) * Real.sqrt ((q * q : Nat) : Real) := by
  have hn : 1 ≤ q * q := by
    have hqpos : 0 < q := hq.pos
    exact Nat.succ_le_of_lt (Nat.mul_pos hqpos hqpos)
  exact exists_constructionAKernel_lattice_bounds_of_good_matrix H hn hshort hcover

private abbrev ShortIntegerVector (n : Nat) :=
  {z : Fin n -> Int //
    z ≠ 0 ∧
      ‖integerVector n z‖ < (1 / 10 : Real) * Real.sqrt (n : Real)}

private lemma int_natAbs_le_of_abs_cast_le {m : Int} {M : Nat}
    (h : |(m : Real)| ≤ (M : Real)) :
    m.natAbs ≤ M := by
  have hnatAbs_real : ((m.natAbs : Nat) : Real) = |(m : Real)| := by
    calc
      ((m.natAbs : Nat) : Real) = ((|m| : Int) : Real) := by
        rw [Int.abs_eq_natAbs]
        simp
      _ = |(m : Real)| := Int.cast_abs
  have hreal : ((m.natAbs : Nat) : Real) ≤ (M : Real) := by
    simpa [hnatAbs_real] using h
  exact_mod_cast hreal

private lemma abs_int_coordinate_le_integerVector_norm
    (n : Nat) (z : Fin n -> Int) (i : Fin n) :
    |(z i : Real)| ≤ ‖integerVector n z‖ := by
  have hsq :
      |(z i : Real)| ^ 2 ≤ ‖integerVector n z‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      |(z i : Real)| ^ 2 =
          ‖(integerVector n z).ofLp i‖ ^ 2 := by
            simp [integerVector, Real.norm_eq_abs]
      _ ≤ ∑ j : Fin n, ‖(integerVector n z).ofLp j‖ ^ 2 :=
            Finset.single_le_sum
              (fun j _hj => sq_nonneg (‖(integerVector n z).ofLp j‖))
              (Finset.mem_univ i)
  have h := sq_le_sq.mp hsq
  simpa [abs_of_nonneg (abs_nonneg _), abs_of_nonneg (norm_nonneg _)] using h

private lemma integerVector_norm_sq_eq_sum (n : Nat) (z : Fin n -> Int) :
    ‖integerVector n z‖ ^ 2 = ∑ i : Fin n, (z i : Real) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [integerVector, Real.norm_eq_abs, sq_abs]

private lemma exp_neg_four_lt_one_div_fifty :
    Real.exp (-4) < (1 / 50 : Real) := by
  have h50 : (50 : Real) < Real.exp 4 := by
    have hsum := Real.sum_le_exp_of_nonneg (by norm_num : (0 : Real) ≤ 4) 8
    norm_num at hsum
    nlinarith
  have hpos : 0 < Real.exp (-4) := Real.exp_pos _
  have hmul : (50 : Real) * Real.exp (-4) < 1 := by
    calc
      (50 : Real) * Real.exp (-4) < Real.exp 4 * Real.exp (-4) := by
        exact mul_lt_mul_of_pos_right h50 (Real.exp_pos _)
      _ = 1 := by rw [← Real.exp_add]; norm_num
  nlinarith

private lemma exp_neg_four_sq_le_geometric (k : Nat) :
    Real.exp (-4 * ((k + 1 : Nat) : Real) ^ 2) ≤
      (1 / 50 : Real) ^ (k + 1) := by
  have hbase : Real.exp (-4) ≤ (1 / 50 : Real) := exp_neg_four_lt_one_div_fifty.le
  have hmul : -4 * ((k + 1 : Nat) : Real) ^ 2 ≤ -4 * ((k + 1 : Nat) : Real) := by
    nlinarith [show (1 : Real) ≤ ((k + 1 : Nat) : Real) by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)]
  calc
    Real.exp (-4 * ((k + 1 : Nat) : Real) ^ 2)
        ≤ Real.exp (-4 * ((k + 1 : Nat) : Real)) :=
          Real.exp_monotone hmul
    _ = (Real.exp (-4)) ^ (k + 1) := by
          rw [← Real.exp_nat_mul]
          ring_nf
    _ ≤ (1 / 50 : Real) ^ (k + 1) := by
          gcongr

private lemma finite_int_gaussian_sum_le_geometric (M : Nat) :
    (∑ m ∈ Finset.Icc (-(M : Int)) (M : Int),
        Real.exp (-4 * (m : Real) ^ 2)) ≤
      1 + 2 * ∑ k ∈ Finset.range M, (1 / 50 : Real) ^ (k + 1) := by
  induction M with
  | zero =>
      simp
  | succ M ih =>
      norm_num [Nat.cast_add]
      rw [show (-1 + -(M : Int)) = -((M : Int) + 1) by ring]
      rw [Finset.Icc_succ_succ M M]
      have hdisj : Disjoint (Finset.Icc (-(M : Int)) (M : Int))
          ({-((M : Int) + 1), (M : Int) + 1} : Finset Int) := by
        rw [Finset.disjoint_left]
        intro x hx hxpair
        simp only [Finset.mem_Icc] at hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hxpair
        rcases hxpair with rfl | rfl <;> omega
      rw [Finset.sum_union hdisj]
      have hpair :
          Real.exp (-4 * ((-((M : Int) + 1) : Int) : Real) ^ 2) +
              Real.exp (-4 * (((M : Int) + 1 : Int) : Real) ^ 2) ≤
            2 * (1 / 50 : Real) ^ (M + 1) := by
        have h1neg :
            Real.exp (-4 * ((-((M : Int) + 1) : Int) : Real) ^ 2) ≤
              (1 / 50 : Real) ^ (M + 1) := by
          convert exp_neg_four_sq_le_geometric M using 2
          norm_num [Nat.cast_add]
          ring
        have h2pos :
            Real.exp (-4 * (((M : Int) + 1 : Int) : Real) ^ 2) ≤
              (1 / 50 : Real) ^ (M + 1) := by
          convert exp_neg_four_sq_le_geometric M using 2
        nlinarith
      have hpair_sum :
          (∑ x ∈ ({-((M : Int) + 1), (M : Int) + 1} : Finset Int),
              Real.exp (-4 * (x : Real) ^ 2)) ≤
            2 * (1 / 50 : Real) ^ (M + 1) := by
        rw [Finset.sum_insert]
        · simpa using hpair
        · simp
          omega
      rw [Finset.sum_range_succ]
      have ih' :
          (∑ x ∈ Finset.Icc (-(M : Int)) (M : Int),
              Real.exp (-(4 * (x : Real) ^ 2))) ≤
            1 + 2 * ∑ k ∈ Finset.range M, (1 / 50 : Real) ^ (k + 1) := by
        simpa [neg_mul] using ih
      have hpair_sum' :
          (∑ x ∈ ({-((M : Int) + 1), (M : Int) + 1} : Finset Int),
              Real.exp (-(4 * (x : Real) ^ 2))) ≤
            2 * (1 / 50 : Real) ^ (M + 1) := by
        simpa [neg_mul] using hpair_sum
      calc
        (∑ x ∈ Finset.Icc (-(M : Int)) (M : Int), Real.exp (-(4 * (x : Real) ^ 2))) +
            ∑ x ∈ ({-((M : Int) + 1), (M : Int) + 1} : Finset Int),
              Real.exp (-(4 * (x : Real) ^ 2))
            ≤ (1 + 2 * ∑ k ∈ Finset.range M, (1 / 50 : Real) ^ (k + 1)) +
                2 * (1 / 50 : Real) ^ (M + 1) := by
              exact add_le_add ih' hpair_sum'
        _ = 1 + 2 *
              (∑ k ∈ Finset.range M, (1 / 50 : Real) ^ (k + 1) +
                (1 / 50 : Real) ^ (M + 1)) := by
              ring

private lemma geometric_one_div_fifty_tail_le (M : Nat) :
    (∑ k ∈ Finset.range M, (1 / 50 : Real) ^ (k + 1)) ≤ 1 / 49 := by
  let r : Real := 1 / 50
  have hr0 : 0 ≤ r := by norm_num [r]
  have hr1 : r < 1 := by norm_num [r]
  have hsumm : Summable fun k : Nat => r ^ (k + 1) := by
    simpa [pow_succ'] using (summable_geometric_of_lt_one hr0 hr1).mul_left r
  have hle := hsumm.sum_le_tsum (Finset.range M) (fun k _ => by positivity)
  have htsum : (∑' k : Nat, r ^ (k + 1)) = 1 / 49 := by
    calc
      (∑' k : Nat, r ^ (k + 1)) = ∑' k : Nat, r * r ^ k := by
        congr with k
        rw [pow_succ']
      _ = r * (∑' k : Nat, r ^ k) := by rw [tsum_mul_left]
      _ = r * (1 - r)⁻¹ := by rw [tsum_geometric_of_lt_one hr0 hr1]
      _ = 1 / 49 := by norm_num [r]
  rw [htsum] at hle
  simpa [r] using hle

private lemma finite_int_gaussian_sum_le_exp (M : Nat) :
    (∑ m ∈ Finset.Icc (-(M : Int)) (M : Int),
        Real.exp (-4 * (m : Real) ^ 2)) ≤
      Real.exp (61 / 1000 : Real) := by
  have htheta := finite_int_gaussian_sum_le_geometric M
  have htail := geometric_one_div_fifty_tail_le M
  have hnum : (1 : Real) + 2 * (1 / 49 : Real) ≤ Real.exp (61 / 1000 : Real) := by
    have hbase := Real.add_one_le_exp (61 / 1000 : Real)
    norm_num at hbase ⊢
    nlinarith
  nlinarith

private lemma real_sqrt_nat_mul_self (q : Nat) :
    Real.sqrt ((q * q : Nat) : Real) = (q : Real) := by
  have hq0 : 0 ≤ (q : Real) := by positivity
  rw [show ((q * q : Nat) : Real) = (q : Real) ^ 2 by
    norm_num [Nat.cast_mul, pow_two]]
  rw [Real.sqrt_sq_eq_abs]
  exact abs_of_nonneg hq0

private theorem shortIntegerVector_mod_ne_zero
    (q : Nat) (hq : Nat.Prime q) (z : ShortIntegerVector (q * q)) :
    intVectorMod q (q * q) z.1 ≠ 0 := by
  intro hzmod
  obtain ⟨i, hi⟩ : ∃ i : Fin (q * q), z.1 i ≠ 0 := by
    by_contra h
    apply z.2.1
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  have hcast0 : ((z.1 i : Int) : ZMod q) = 0 := by
    have h := congr_fun hzmod i
    simpa [intVectorMod] using h
  have hdvd : (q : Int) ∣ z.1 i :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (z.1 i) q).1 hcast0
  have hnatdvd : q ∣ (z.1 i).natAbs := by
    have hnatdvd' : (q : Int).natAbs ∣ (z.1 i).natAbs :=
      (Int.natAbs_dvd_natAbs).2 hdvd
    simpa using hnatdvd'
  have hq_le_natAbs : q ≤ (z.1 i).natAbs :=
    Nat.le_of_dvd ((Int.natAbs_pos).2 hi) hnatdvd
  have hnatAbs_real : ((z.1 i).natAbs : Real) = |(z.1 i : Real)| := by
    calc
      ((z.1 i).natAbs : Real) = ((|z.1 i| : Int) : Real) := by
        rw [Int.abs_eq_natAbs]
        simp
      _ = |(z.1 i : Real)| := Int.cast_abs
  have hq_le_abs : (q : Real) ≤ |(z.1 i : Real)| := by
    rw [← hnatAbs_real]
    exact_mod_cast hq_le_natAbs
  have habs_le_norm : |(z.1 i : Real)| ≤ ‖integerVector (q * q) z.1‖ := by
    have hsq :
        |(z.1 i : Real)| ^ 2 ≤ ‖integerVector (q * q) z.1‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      calc
        |(z.1 i : Real)| ^ 2 =
            ‖(integerVector (q * q) z.1).ofLp i‖ ^ 2 := by
              simp [integerVector, Real.norm_eq_abs]
        _ ≤ ∑ j : Fin (q * q), ‖(integerVector (q * q) z.1).ofLp j‖ ^ 2 :=
              Finset.single_le_sum
                (fun j _hj => sq_nonneg (‖(integerVector (q * q) z.1).ofLp j‖))
                (Finset.mem_univ i)
    have h := sq_le_sq.mp hsq
    simpa [abs_of_nonneg (abs_nonneg _), abs_of_nonneg (norm_nonneg _)] using h
  have hq_le_norm : (q : Real) ≤ ‖integerVector (q * q) z.1‖ :=
    hq_le_abs.trans habs_le_norm
  have hshort :
      ‖integerVector (q * q) z.1‖ < (1 / 10 : Real) * (q : Real) := by
    simpa [real_sqrt_nat_mul_self q] using z.2.2
  have hqpos : 0 < (q : Real) := by
    exact_mod_cast hq.pos
  nlinarith

private theorem shortIntegerVector_finite (n : Nat) :
    Finite (ShortIntegerVector n) := by
  classical
  let R : Real := (1 / 10 : Real) * Real.sqrt (n : Real)
  let S : Set (RealEuclideanSpace n) := Metric.ball (0 : RealEuclideanSpace n) R
  let T : Set (RealEuclideanSpace n) := S ∩ (integerLattice n : Set (RealEuclideanSpace n))
  have hTfinite : T.Finite := by
    simpa [T, S] using integerLattice_finite_inter_isBounded (n := n)
      (s := Metric.ball (0 : RealEuclideanSpace n) R) Metric.isBounded_ball
  let f : ShortIntegerVector n -> T := fun z =>
    ⟨integerVector n z.1, by
      constructor
      · simpa [S, R, Metric.mem_ball, dist_eq_norm] using z.2.2
      · exact ⟨z.1, rfl⟩⟩
  have hf : Function.Injective f := by
    intro z w hzw
    apply Subtype.ext
    funext i
    have hcoord :=
      congrArg (fun x : T => ((x.1 : RealEuclideanSpace n) : Fin n -> Real) i) hzw
    norm_num [f, integerVector] at hcoord
    exact_mod_cast hcoord
  haveI : Fintype T := hTfinite.fintype
  exact Finite.of_injective f hf

private theorem shortIntegerVector_card_exp_bound (n : Nat) (_hn : 1 ≤ n) :
    (Nat.card (ShortIntegerVector n) : Real) ≤
      Real.exp ((101 / 1000 : Real) * (n : Real)) := by
  classical
  haveI : Finite (ShortIntegerVector n) := shortIntegerVector_finite n
  haveI : Fintype (ShortIntegerVector n) := Fintype.ofFinite (ShortIntegerVector n)
  let R : Real := (1 / 10 : Real) * Real.sqrt (n : Real)
  let M : Nat := Nat.ceil R
  let box : Finset (Fin n -> Int) :=
    Fintype.piFinset fun _ : Fin n => Finset.Icc (-(M : Int)) (M : Int)
  let weight : (Fin n -> Int) -> Real := fun p =>
    Real.exp (4 * ((n : Real) / 100 - ∑ i : Fin n, (p i : Real) ^ 2))
  have hRleM : R ≤ (M : Real) := by
    simpa [M] using Nat.le_ceil R
  have hmem_box (z : ShortIntegerVector n) : z.1 ∈ box := by
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have hcoord := abs_int_coordinate_le_integerVector_norm n z.1 i
    have hcoord_lt : |(z.1 i : Real)| < R := lt_of_le_of_lt hcoord z.2.2
    have hcoord_le_M : |(z.1 i : Real)| ≤ (M : Real) := hcoord_lt.le.trans hRleM
    have hnatAbs : (z.1 i).natAbs ≤ M := int_natAbs_le_of_abs_cast_le hcoord_le_M
    have hInt : (((z.1 i).natAbs : Nat) : Int) ≤ (M : Int) := by exact_mod_cast hnatAbs
    have habs : |z.1 i| ≤ (M : Int) := by
      rw [Int.abs_eq_natAbs]
      exact hInt
    exact abs_le.mp habs
  have hcard_le_weight :
      (Nat.card (ShortIntegerVector n) : Real) ≤ ∑ z : ShortIntegerVector n, weight z.1 := by
    rw [Nat.card_eq_fintype_card]
    calc
      (Fintype.card (ShortIntegerVector n) : Real) =
          ∑ _z : ShortIntegerVector n, (1 : Real) := by simp
      _ ≤ ∑ z : ShortIntegerVector n, weight z.1 := by
          apply Finset.sum_le_sum
          intro z _hz
          have hR_nonneg : 0 ≤ R := by positivity
          have hnorm_sq_lt : ‖integerVector n z.1‖ ^ 2 < R ^ 2 :=
            sq_lt_sq.mpr (by
              rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hR_nonneg]
              exact z.2.2)
          have hsumsq_lt : (∑ i : Fin n, (z.1 i : Real) ^ 2) < (n : Real) / 100 := by
            have hR_sq : R ^ 2 = (n : Real) / 100 := by
              have hnnonneg : 0 ≤ (n : Real) := by positivity
              dsimp [R]
              rw [mul_pow, Real.sq_sqrt hnnonneg]
              ring
            simpa [integerVector_norm_sq_eq_sum n z.1, hR_sq] using hnorm_sq_lt
          have hnonneg :
              0 ≤ 4 * ((n : Real) / 100 - ∑ i : Fin n, (z.1 i : Real) ^ 2) := by
            nlinarith
          calc
            (1 : Real) = Real.exp 0 := by simp
            _ ≤ weight z.1 := by
                exact Real.exp_monotone hnonneg
  have hweight_image_le_box :
      (∑ z : ShortIntegerVector n, weight z.1) ≤ ∑ p ∈ box, weight p := by
    let imageSet : Finset (Fin n -> Int) :=
      Finset.univ.image (fun z : ShortIntegerVector n => z.1)
    have hsum_image :
        (∑ z : ShortIntegerVector n, weight z.1) =
          ∑ p ∈ imageSet, weight p := by
      rw [show (∑ p ∈ imageSet, weight p) =
          ∑ p ∈ Finset.univ.image (fun z : ShortIntegerVector n => z.1), weight p by rfl]
      rw [Finset.sum_image]
      intro a _ha b _hb hab
      exact Subtype.ext hab
    rw [hsum_image]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro p hp
        rcases Finset.mem_image.mp hp with ⟨z, _hz, rfl⟩
        exact hmem_box z)
      (by
        intro p _hpbox _hpnot
        positivity)
  have hbox_sum_le :
      (∑ p ∈ box, weight p) ≤
        Real.exp ((n : Real) / 25) *
          (Real.exp (61 / 1000 : Real)) ^ n := by
    have hfactor :
        (∑ p ∈ box, weight p) =
          Real.exp ((n : Real) / 25) *
            ∑ p ∈ box, ∏ i : Fin n, Real.exp (-4 * (p i : Real) ^ 2) := by
      calc
        (∑ p ∈ box, weight p) =
            ∑ p ∈ box,
              Real.exp ((n : Real) / 25) *
                ∏ i : Fin n, Real.exp (-4 * (p i : Real) ^ 2) := by
              apply Finset.sum_congr rfl
              intro p _hp
              dsimp [weight]
              rw [show 4 * ((n : Real) / 100 - ∑ i : Fin n, (p i : Real) ^ 2) =
                  (n : Real) / 25 + ∑ i : Fin n, (-4 * (p i : Real) ^ 2) by
                    rw [← Finset.mul_sum]
                    ring]
              rw [Real.exp_add, Real.exp_sum]
        _ = Real.exp ((n : Real) / 25) *
              ∑ p ∈ box, ∏ i : Fin n, Real.exp (-4 * (p i : Real) ^ 2) := by
              rw [Finset.mul_sum]
    rw [hfactor]
    have hprod_eq :
        (∑ p ∈ box, ∏ i : Fin n, Real.exp (-4 * (p i : Real) ^ 2)) =
          (∑ m ∈ Finset.Icc (-(M : Int)) (M : Int),
            Real.exp (-4 * (m : Real) ^ 2)) ^ n := by
      dsimp [box]
      calc
        (∑ p ∈ Fintype.piFinset fun _ : Fin n => Finset.Icc (-(M : Int)) (M : Int),
            ∏ i : Fin n, Real.exp (-4 * (p i : Real) ^ 2)) =
            ∏ _i : Fin n,
              ∑ m ∈ Finset.Icc (-(M : Int)) (M : Int),
                Real.exp (-4 * (m : Real) ^ 2) := by
              exact (Finset.prod_univ_sum
                (fun _ : Fin n => Finset.Icc (-(M : Int)) (M : Int))
                (fun _ m => Real.exp (-4 * (m : Real) ^ 2))).symm
        _ = (∑ m ∈ Finset.Icc (-(M : Int)) (M : Int),
              Real.exp (-4 * (m : Real) ^ 2)) ^ n := by
              simp
    rw [hprod_eq]
    have htheta_nonneg :
        0 ≤ ∑ m ∈ Finset.Icc (-(M : Int)) (M : Int),
          Real.exp (-4 * (m : Real) ^ 2) := by
      positivity
    have htheta_le :
        (∑ m ∈ Finset.Icc (-(M : Int)) (M : Int),
          Real.exp (-4 * (m : Real) ^ 2)) ≤ Real.exp (61 / 1000 : Real) :=
      finite_int_gaussian_sum_le_exp M
    have hprod_le :
        (∑ m ∈ Finset.Icc (-(M : Int)) (M : Int),
          Real.exp (-4 * (m : Real) ^ 2)) ^ n ≤
          (Real.exp (61 / 1000 : Real)) ^ n :=
      pow_le_pow_left₀ htheta_nonneg htheta_le n
    exact mul_le_mul_of_nonneg_left hprod_le (Real.exp_pos _).le
  have hexp :
      Real.exp ((n : Real) / 25) * (Real.exp (61 / 1000 : Real)) ^ n =
        Real.exp ((101 / 1000 : Real) * (n : Real)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  calc
    (Nat.card (ShortIntegerVector n) : Real) ≤ ∑ z : ShortIntegerVector n, weight z.1 :=
      hcard_le_weight
    _ ≤ ∑ p ∈ box, weight p := hweight_image_le_box
    _ ≤ Real.exp ((n : Real) / 25) * (Real.exp (61 / 1000 : Real)) ^ n :=
      hbox_sum_le
    _ = Real.exp ((101 / 1000 : Real) * (n : Real)) := hexp

private def ConstructionAShortKernelGood (q s n : Nat)
    (H : Matrix (Fin s) (Fin n) (ZMod q)) : Prop :=
  ∀ z : Fin n -> Int, z ≠ 0 -> InConstructionAKernel q s n H z ->
    ¬ ‖integerVector n z‖ < (1 / 10 : Real) * Real.sqrt (n : Real)

private theorem not_constructionAShortKernelGood_iff
    (q s n : Nat) (H : Matrix (Fin s) (Fin n) (ZMod q)) :
    ¬ ConstructionAShortKernelGood q s n H ↔
      ∃ z : Fin n -> Int,
        z ≠ 0 ∧ InConstructionAKernel q s n H z ∧
          ‖integerVector n z‖ < (1 / 10 : Real) * Real.sqrt (n : Real) := by
  classical
  unfold ConstructionAShortKernelGood
  constructor
  · intro hgood
    by_contra hnone
    apply hgood
    intro z hz0 hzker hzshort
    exact hnone ⟨z, hz0, hzker, hzshort⟩
  · rintro ⟨z, hz0, hzker, hzshort⟩ hgood
    exact hgood z hz0 hzker hzshort

private theorem shortKernelBad_card_le_sum_kernel_fibers (q s n : Nat) [NeZero q]
    [Fintype (ShortIntegerVector n)]
    [Fintype {H : Matrix (Fin s) (Fin n) (ZMod q) //
      ¬ ConstructionAShortKernelGood q s n H}]
    [∀ z : ShortIntegerVector n,
      Fintype {H : Matrix (Fin s) (Fin n) (ZMod q) //
        InConstructionAKernel q s n H z.1}] :
    Fintype.card {H : Matrix (Fin s) (Fin n) (ZMod q) //
        ¬ ConstructionAShortKernelGood q s n H} ≤
      ∑ z : ShortIntegerVector n,
        Fintype.card {H : Matrix (Fin s) (Fin n) (ZMod q) //
          InConstructionAKernel q s n H z.1} := by
  classical
  let Bad :=
    {H : Matrix (Fin s) (Fin n) (ZMod q) //
      ¬ ConstructionAShortKernelGood q s n H}
  let KernelFor :=
    fun z : ShortIntegerVector n =>
      {H : Matrix (Fin s) (Fin n) (ZMod q) // InConstructionAKernel q s n H z.1}
  let Target := (z : ShortIntegerVector n) × KernelFor z
  let f : Bad -> Target := fun H =>
    let hbad := (not_constructionAShortKernelGood_iff q s n H.1).1 H.2
    let z : ShortIntegerVector n :=
      ⟨Classical.choose hbad, by
        rcases Classical.choose_spec hbad with ⟨hz0, _hzker, hzshort⟩
        exact ⟨hz0, hzshort⟩⟩
    ⟨z, ⟨H.1, by
      rcases Classical.choose_spec hbad with ⟨_hz0, hzker, _hzshort⟩
      exact hzker⟩⟩
  have hf : Function.Injective f := by
    intro H K hHK
    apply Subtype.ext
    exact congrArg (fun z : Target => z.2.1) hHK
  have hcard : Fintype.card Bad ≤ Fintype.card Target :=
    Fintype.card_le_of_injective f hf
  simpa [Bad, KernelFor, Target, Fintype.card_sigma] using hcard

private theorem shortKernelBad_card_bound (q s : Nat) [NeZero q] (hq : Nat.Prime q) :
    Nat.card {H : Matrix (Fin s) (Fin (q * q)) (ZMod q) //
        ¬ ConstructionAShortKernelGood q s (q * q) H} * q ^ s ≤
      Nat.card (ShortIntegerVector (q * q)) *
        Nat.card (Matrix (Fin s) (Fin (q * q)) (ZMod q)) := by
  classical
  haveI : Finite (ShortIntegerVector (q * q)) :=
    shortIntegerVector_finite (q * q)
  haveI : Fintype (ShortIntegerVector (q * q)) :=
    Fintype.ofFinite (ShortIntegerVector (q * q))
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have hbad :=
    shortKernelBad_card_le_sum_kernel_fibers q s (q * q)
  calc
    Fintype.card {H : Matrix (Fin s) (Fin (q * q)) (ZMod q) //
        ¬ ConstructionAShortKernelGood q s (q * q) H} * q ^ s
        ≤ (∑ z : ShortIntegerVector (q * q),
            Fintype.card {H : Matrix (Fin s) (Fin (q * q)) (ZMod q) //
              InConstructionAKernel q s (q * q) H z.1}) * q ^ s := by
          exact Nat.mul_le_mul_right (q ^ s) hbad
    _ = ∑ z : ShortIntegerVector (q * q),
            Fintype.card {H : Matrix (Fin s) (Fin (q * q)) (ZMod q) //
              InConstructionAKernel q s (q * q) H z.1} * q ^ s := by
          rw [Finset.sum_mul]
    _ = ∑ _z : ShortIntegerVector (q * q),
            Fintype.card (Matrix (Fin s) (Fin (q * q)) (ZMod q)) := by
          apply Finset.sum_congr rfl
          intro z _hz
          have hfiber :
              Fintype.card {H : Matrix (Fin s) (Fin (q * q)) (ZMod q) //
                  InConstructionAKernel q s (q * q) H z.1} =
                Fintype.card {H : Matrix (Fin s) (Fin (q * q)) (ZMod q) //
                  constructionASyndrome q s (q * q) H z.1 = 0} := by
            exact Fintype.card_congr (Equiv.subtypeEquivRight fun H => by
              rfl)
          rw [hfiber]
          exact kernelSyndromeFiber_card q s (q * q) hq z.1
            (shortIntegerVector_mod_ne_zero q hq z)
    _ = Fintype.card (ShortIntegerVector (q * q)) *
          Fintype.card (Matrix (Fin s) (Fin (q * q)) (ZMod q)) := by
          simp

private theorem shortKernelBad_card_lt_half_total_of_short_card
    (q s : Nat) [NeZero q] (hq : Nat.Prime q)
    (hsmall : 2 * Nat.card (ShortIntegerVector (q * q)) < q ^ s) :
    2 * Nat.card {H : Matrix (Fin s) (Fin (q * q)) (ZMod q) //
        ¬ ConstructionAShortKernelGood q s (q * q) H} <
      Nat.card (Matrix (Fin s) (Fin (q * q)) (ZMod q)) := by
  classical
  let Bad :=
    {H : Matrix (Fin s) (Fin (q * q)) (ZMod q) //
      ¬ ConstructionAShortKernelGood q s (q * q) H}
  let Short := ShortIntegerVector (q * q)
  let Ω := Matrix (Fin s) (Fin (q * q)) (ZMod q)
  have hbound : Nat.card Bad * q ^ s ≤ Nat.card Short * Nat.card Ω := by
    simpa [Bad, Short, Ω] using shortKernelBad_card_bound q s hq
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqpow_pos : 0 < q ^ s := pow_pos hqpos s
  have hΩpos : 0 < Nat.card Ω := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos_iff.mpr ⟨0⟩
  have htwice_bound :
      (2 * Nat.card Bad) * q ^ s ≤ (2 * Nat.card Short) * Nat.card Ω := by
    calc
      (2 * Nat.card Bad) * q ^ s = 2 * (Nat.card Bad * q ^ s) := by ring
      _ ≤ 2 * (Nat.card Short * Nat.card Ω) := Nat.mul_le_mul_left 2 hbound
      _ = (2 * Nat.card Short) * Nat.card Ω := by ring
  have hright_lt : (2 * Nat.card Short) * Nat.card Ω < q ^ s * Nat.card Ω :=
    mul_lt_mul_of_pos_right hsmall hΩpos
  have hmul_lt : (2 * Nat.card Bad) * q ^ s < q ^ s * Nat.card Ω :=
    lt_of_le_of_lt htwice_bound hright_lt
  have hmul_lt' : (2 * Nat.card Bad) * q ^ s < Nat.card Ω * q ^ s := by
    simpa [mul_comm] using hmul_lt
  exact lt_of_mul_lt_mul_right hmul_lt' hqpow_pos.le

private def ConstructionASyndromeCovering (q s n : Nat)
    (H : Matrix (Fin s) (Fin n) (ZMod q)) : Prop :=
  ∀ y : Fin s -> ZMod q,
    ∃ ε : Fin n -> Int,
      (∀ i : Fin n, ε i = 0 ∨ ε i = 1) ∧ constructionASyndrome q s n H ε = y

private def ConstructionAZModSyndromeCovering (q s n : Nat)
    (H : Matrix (Fin s) (Fin n) (ZMod q)) : Prop :=
  ∀ y : Fin s -> ZMod q,
    ∃ ε : Fin n -> ZMod q, IsBooleanVector ε ∧ finiteFieldMatVec q s n H ε = y

private noncomputable instance constructionAZModSyndromeCoverBadFintype
    (q s n : Nat) [NeZero q] :
    Fintype {H : Matrix (Fin s) (Fin n) (ZMod q) //
      ¬ ConstructionAZModSyndromeCovering q s n H} := by
  classical
  refine Fintype.subtype
    (Finset.univ.filter fun H : Matrix (Fin s) (Fin n) (ZMod q) =>
      ¬ ConstructionAZModSyndromeCovering q s n H) ?_
  intro H
  simp

private def MissingSyndrome (q s n : Nat)
    (H : Matrix (Fin s) (Fin n) (ZMod q)) (y : Fin s -> ZMod q) : Prop :=
  ∀ ε : Fin n -> ZMod q, IsBooleanVector ε -> finiteFieldMatVec q s n H ε ≠ y

private lemma zero_isBooleanVector (q n : Nat) :
    IsBooleanVector (0 : Fin n -> ZMod q) := by
  intro i
  left
  rfl

private theorem not_missing_zero (q s n : Nat)
    (H : Matrix (Fin s) (Fin n) (ZMod q)) :
    ¬ MissingSyndrome q s n H 0 := by
  intro hmissing
  exact hmissing 0 (zero_isBooleanVector q n) (by
    ext i
    simp [finiteFieldMatVec])

private theorem missing_syndrome_ne_zero
    (q s n : Nat) {H : Matrix (Fin s) (Fin n) (ZMod q)}
    {y : Fin s -> ZMod q} :
    MissingSyndrome q s n H y -> y ≠ 0 := by
  intro hmissing hy
  subst hy
  exact not_missing_zero q s n H hmissing

private noncomputable def fixedSyndromeNonmissing
    (q s n : Nat) (y : Fin s -> ZMod q) :=
  {H : Matrix (Fin s) (Fin n) (ZMod q) // ¬ MissingSyndrome q s n H y}

private noncomputable instance fixedSyndromeNonmissingFintype
    (q s n : Nat) [NeZero q] (y : Fin s -> ZMod q) :
    Fintype (fixedSyndromeNonmissing q s n y) := by
  classical
  refine Fintype.subtype
    (Finset.univ.filter fun H : Matrix (Fin s) (Fin n) (ZMod q) =>
      ¬ MissingSyndrome q s n H y) ?_
  intro H
  simp

private theorem fixedSyndromePreimage_sum_card
    (q s n : Nat) [NeZero q] (y : Fin s -> ZMod q) :
    (∑ H : fixedSyndromeNonmissing q s n y,
        Fintype.card (fixedSyndromePreimage q s n y H.1)) =
      Fintype.card (fixedSyndromeIncidence q s n y) := by
  classical
  let Nonmissing := fixedSyndromeNonmissing q s n y
  let Pre := fixedSyndromePreimage q s n y
  let Inc := fixedSyndromeIncidence q s n y
  let e : Sigma (fun H : Nonmissing => Pre H.1) ≃ Inc :=
    { toFun := fun p : Sigma (fun H : Nonmissing => Pre H.1) =>
        ⟨(p.1.1, p.2.1), p.2.2⟩
      invFun := fun p : Inc =>
        ⟨⟨p.1.1, by
            intro hmissing
            exact hmissing p.1.2.1 p.1.2.2.1 p.2⟩,
          ⟨p.1.2, p.2⟩⟩
      left_inv := by
        intro p
        rcases p with ⟨H, ε, hε⟩
        rfl
      right_inv := by
        intro p
        rcases p with ⟨⟨H, ε⟩, hHε⟩
        rfl }
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr e

private theorem fixedSyndromePreimage_sum_sq_card
    (q s n : Nat) [NeZero q] (y : Fin s -> ZMod q) :
    (∑ H : fixedSyndromeNonmissing q s n y,
        Fintype.card (fixedSyndromePreimage q s n y H.1) ^ 2) =
      Fintype.card (fixedSyndromeSquareIncidence q s n y) := by
  classical
  let Nonmissing := fixedSyndromeNonmissing q s n y
  let Pre := fixedSyndromePreimage q s n y
  let Square := fixedSyndromeSquareIncidence q s n y
  let e : Sigma (fun H : Nonmissing => Pre H.1 × Pre H.1) ≃ Square :=
    { toFun := fun p : Sigma (fun H : Nonmissing => Pre H.1 × Pre H.1) =>
        ⟨(p.1.1, (p.2.1.1, p.2.2.1)), p.2.1.2, p.2.2.2⟩
      invFun := fun p : Square =>
        ⟨⟨p.1.1, by
            intro hmissing
            exact hmissing p.1.2.1.1 p.1.2.1.2.1 p.2.1⟩,
          ⟨⟨p.1.2.1, p.2.1⟩, ⟨p.1.2.2, p.2.2⟩⟩⟩
      left_inv := by
        intro p
        rcases p with ⟨H, ε, η⟩
        rfl
      right_inv := by
        intro p
        rcases p with ⟨⟨H, ε, η⟩, hε, hη⟩
        rfl }
  calc
    (∑ H : Nonmissing, Fintype.card (Pre H.1) ^ 2) =
        ∑ H : Nonmissing, Fintype.card (Pre H.1 × Pre H.1) := by
          simp [pow_two]
    _ = Fintype.card (Sigma fun H : Nonmissing => Pre H.1 × Pre H.1) := by
          rw [Fintype.card_sigma]
    _ = Fintype.card Square := by
          exact Fintype.card_congr e

private noncomputable instance missingSyndromeFintype
    (q s n : Nat) [NeZero q] (y : Fin s -> ZMod q) :
    Fintype {H : Matrix (Fin s) (Fin n) (ZMod q) // MissingSyndrome q s n H y} := by
  classical
  refine Fintype.subtype
    (Finset.univ.filter fun H : Matrix (Fin s) (Fin n) (ZMod q) =>
      MissingSyndrome q s n H y) ?_
  intro H
  simp

private theorem missing_fixed_syndrome_card_bound
    (q s n : Nat) [NeZero q] (hq : Nat.Prime q) (hqodd : Odd q)
    (hn : 1 ≤ n) {y : Fin s -> ZMod q} (_hy : y ≠ 0) :
    Fintype.card {H : Matrix (Fin s) (Fin n) (ZMod q) //
        MissingSyndrome q s n H y} * (2 ^ n - 1) ≤
      Fintype.card (Matrix (Fin s) (Fin n) (ZMod q)) * q ^ s := by
  classical
  let Ω := Matrix (Fin s) (Fin n) (ZMod q)
  let Missing := {H : Ω // MissingSyndrome q s n H y}
  let Nonmissing := fixedSyndromeNonmissing q s n y
  let Inc := fixedSyndromeIncidence q s n y
  let Square := fixedSyndromeSquareIncidence q s n y
  let B := Fintype.card (NonzeroBooleanVector q n)
  let T := Fintype.card Ω
  let Q := q ^ s
  have hBcard : B = 2 ^ n - 1 := by
    simpa [B] using nonzeroBooleanVector_fintype_card q n hq
  have hBpos : 0 < B := by
    have hpow : 1 < 2 ^ n := by
      cases n with
      | zero => omega
      | succ k =>
          have hpos : 0 < 2 ^ k := pow_pos (by norm_num : 0 < (2 : Nat)) k
          change 1 < 2 ^ k * 2
          calc
            1 < 1 * 2 := by norm_num
            _ ≤ 2 ^ k * 2 := Nat.mul_le_mul_right 2 hpos
    rw [hBcard]
    omega
  have hTpos : 0 < T := by
    rw [Fintype.card_pos_iff]
    exact ⟨0⟩
  have hMleT : Fintype.card Missing ≤ T := by
    simpa [Missing, T, Ω] using
      Fintype.card_subtype_le (fun H : Ω => MissingSyndrome q s n H y)
  have hNcard : Fintype.card Nonmissing = T - Fintype.card Missing := by
    simpa [Nonmissing, Missing, T, Ω, fixedSyndromeNonmissing] using
      Fintype.card_subtype_compl (fun H : Ω => MissingSyndrome q s n H y)
  have hMN : Fintype.card Missing + Fintype.card Nonmissing = T := by
    rw [hNcard, Nat.add_sub_of_le hMleT]
  let f : Nonmissing -> Nat := fun H =>
    Fintype.card (fixedSyndromePreimage q s n y H.1)
  have hcauchy :
      (∑ H : Nonmissing, f H) ^ 2 ≤
        Fintype.card Nonmissing * ∑ H : Nonmissing, f H ^ 2 := by
    simpa [f] using
      (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset Nonmissing)) (f := f))
  change
      (∑ H : Nonmissing, Fintype.card (fixedSyndromePreimage q s n y H.1)) ^ 2 ≤
        Fintype.card Nonmissing *
          ∑ H : Nonmissing, Fintype.card (fixedSyndromePreimage q s n y H.1) ^ 2
    at hcauchy
  rw [fixedSyndromePreimage_sum_card q s n y,
    fixedSyndromePreimage_sum_sq_card q s n y] at hcauchy
  have hQ2 : q ^ (2 * s) = Q * Q := by
    rw [show 2 * s = s + s by omega, pow_add]
  have hInc : Fintype.card Inc * Q = B * T := by
    simpa [Inc, B, T, Ω, Q] using fixedSyndromeIncidence_card_mul q s n hq y
  have hSquare : Fintype.card Square * q ^ (2 * s) = T * B * (B + Q - 1) := by
    simpa [Square, T, B, Ω, Q] using
      fixedSyndromeSquareIncidence_card_mul q s n hq hqodd hn y
  have hCauchyMul :
      Fintype.card Inc ^ 2 * q ^ (2 * s) ≤
        Fintype.card Nonmissing * (Fintype.card Square * q ^ (2 * s)) := by
    have hmul := Nat.mul_le_mul_right (q ^ (2 * s)) hcauchy
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hMain :
      (B * T) ^ 2 ≤ Fintype.card Nonmissing * (T * B * (B + Q - 1)) := by
    calc
      (B * T) ^ 2 = Fintype.card Inc ^ 2 * q ^ (2 * s) := by
        rw [← hInc, hQ2]
        ring
      _ ≤ Fintype.card Nonmissing * (Fintype.card Square * q ^ (2 * s)) :=
        hCauchyMul
      _ = Fintype.card Nonmissing * (T * B * (B + Q - 1)) := by
        rw [hSquare]
  have hCpos : 0 < T * B := Nat.mul_pos hTpos hBpos
  have hCancelInput :
      (T * B) * (T * B) ≤
        (T * B) * (Fintype.card Nonmissing * (B + Q - 1)) := by
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hMain
  have hBTle : T * B ≤ Fintype.card Nonmissing * (B + Q - 1) :=
    Nat.le_of_mul_le_mul_left hCancelInput hCpos
  have hGoalB : Fintype.card Missing * B ≤ T * Q := by
    let M := Fintype.card Missing
    let N := Fintype.card Nonmissing
    have hMN' : M + N = T := by simpa [M, N] using hMN
    have hBTle' : T * B ≤ N * (B + Q - 1) := by simpa [N] using hBTle
    have hQpos : 0 < Q := by
      exact pow_pos (Nat.pos_of_ne_zero (NeZero.ne q)) s
    have hBQ : B + Q - 1 = B + (Q - 1) := by omega
    change M * B ≤ T * Q
    have h1 : (M + N) * B ≤ N * (B + Q - 1) := by
      simpa [hMN'] using hBTle'
    have h2 : M * B + N * B ≤ N * B + N * (Q - 1) := by
      calc
        M * B + N * B = (M + N) * B := by ring
        _ ≤ N * (B + Q - 1) := h1
        _ = N * B + N * (Q - 1) := by
          rw [hBQ]
          ring
    have h3 : M * B ≤ N * (Q - 1) := by
      have h2' : M * B + N * B ≤ N * (Q - 1) + N * B := by
        simpa [add_comm, add_left_comm, add_assoc] using h2
      exact Nat.le_of_add_le_add_right h2'
    have hNleT : N ≤ T := by omega
    exact h3.trans (Nat.mul_le_mul hNleT (Nat.sub_le Q 1))
  simpa [Missing, B, hBcard, T, Ω, Q] using hGoalB

private theorem not_missingSyndrome_iff
    (q s n : Nat) (H : Matrix (Fin s) (Fin n) (ZMod q)) (y : Fin s -> ZMod q) :
    ¬ MissingSyndrome q s n H y ↔
      ∃ ε : Fin n -> ZMod q, IsBooleanVector ε ∧ finiteFieldMatVec q s n H ε = y := by
  classical
  unfold MissingSyndrome
  constructor
  · intro hmissing
    by_contra hnone
    apply hmissing
    intro ε hε hεy
    exact hnone ⟨ε, hε, hεy⟩
  · rintro ⟨ε, hε, hεy⟩ hmissing
    exact hmissing ε hε hεy

private theorem not_constructionAZModSyndromeCovering_iff
    (q s n : Nat) (H : Matrix (Fin s) (Fin n) (ZMod q)) :
    ¬ ConstructionAZModSyndromeCovering q s n H ↔
      ∃ y : Fin s -> ZMod q, MissingSyndrome q s n H y := by
  classical
  unfold ConstructionAZModSyndromeCovering MissingSyndrome
  constructor
  · intro hcover
    by_contra hnone
    apply hcover
    intro y
    by_contra hy
    apply hnone
    refine ⟨y, ?_⟩
    intro ε hε hεy
    exact hy ⟨ε, hε, hεy⟩
  · rintro ⟨y, hmissing⟩ hcover
    rcases hcover y with ⟨ε, hε, hεy⟩
    exact hmissing ε hε hεy

private theorem constructionAZModSyndromeCovering_iff_no_missing
    (q s n : Nat) (H : Matrix (Fin s) (Fin n) (ZMod q)) :
    ConstructionAZModSyndromeCovering q s n H ↔
      ∀ y : Fin s -> ZMod q, ¬ MissingSyndrome q s n H y := by
  classical
  constructor
  · intro hcover y hmissing
    rcases hcover y with ⟨ε, hε, hεy⟩
    exact hmissing ε hε hεy
  · intro hmissing y
    exact (not_missingSyndrome_iff q s n H y).1 (hmissing y)

private theorem not_constructionAZModSyndromeCovering_iff_exists_nonzero_missing
    (q s n : Nat) (H : Matrix (Fin s) (Fin n) (ZMod q)) :
    ¬ ConstructionAZModSyndromeCovering q s n H ↔
      ∃ y : Fin s -> ZMod q, y ≠ 0 ∧ MissingSyndrome q s n H y := by
  classical
  rw [not_constructionAZModSyndromeCovering_iff]
  constructor
  · rintro ⟨y, hmissing⟩
    exact ⟨y, missing_syndrome_ne_zero q s n hmissing, hmissing⟩
  · rintro ⟨y, _hy, hmissing⟩
    exact ⟨y, hmissing⟩

private theorem syndromeCoverBad_card_le_sum_missing (q s n : Nat) [NeZero q]
    [Fintype {H : Matrix (Fin s) (Fin n) (ZMod q) //
      ¬ ConstructionAZModSyndromeCovering q s n H}]
    [∀ y : Fin s -> ZMod q,
      Fintype {H : Matrix (Fin s) (Fin n) (ZMod q) // MissingSyndrome q s n H y}] :
    Fintype.card {H : Matrix (Fin s) (Fin n) (ZMod q) //
        ¬ ConstructionAZModSyndromeCovering q s n H} ≤
      ∑ y : Fin s -> ZMod q,
        Fintype.card {H : Matrix (Fin s) (Fin n) (ZMod q) //
          MissingSyndrome q s n H y} := by
  classical
  let Bad :=
    {H : Matrix (Fin s) (Fin n) (ZMod q) //
      ¬ ConstructionAZModSyndromeCovering q s n H}
  let MissingFor :=
    fun y : Fin s -> ZMod q =>
      {H : Matrix (Fin s) (Fin n) (ZMod q) // MissingSyndrome q s n H y}
  let Target := (y : Fin s -> ZMod q) × MissingFor y
  let f : Bad -> Target := fun H =>
    let hmissing := (not_constructionAZModSyndromeCovering_iff q s n H.1).1 H.2
    let y := Classical.choose hmissing
    ⟨y, ⟨H.1, Classical.choose_spec hmissing⟩⟩
  have hf : Function.Injective f := by
    intro H K hHK
    apply Subtype.ext
    exact congrArg (fun z : Target => z.2.1) hHK
  have hcard : Fintype.card Bad ≤ Fintype.card Target :=
    Fintype.card_le_of_injective f hf
  simpa [Bad, MissingFor, Target, Fintype.card_sigma] using hcard

private theorem missing_zero_card (q s n : Nat)
    [Fintype {H : Matrix (Fin s) (Fin n) (ZMod q) //
      MissingSyndrome q s n H 0}] :
    Fintype.card {H : Matrix (Fin s) (Fin n) (ZMod q) //
      MissingSyndrome q s n H 0} = 0 := by
  rw [Fintype.card_eq_zero_iff]
  exact ⟨fun H => not_missing_zero q s n H.1 H.2⟩

private theorem syndromeCoverBad_card_bound_of_fixed_missing
    (q s n : Nat) [NeZero q] (hn : 1 ≤ n)
    [Fintype {H : Matrix (Fin s) (Fin n) (ZMod q) //
      ¬ ConstructionAZModSyndromeCovering q s n H}]
    [∀ y : Fin s -> ZMod q,
      Fintype {H : Matrix (Fin s) (Fin n) (ZMod q) // MissingSyndrome q s n H y}]
    (hfixed : ∀ y : Fin s -> ZMod q, y ≠ 0 ->
      Fintype.card {H : Matrix (Fin s) (Fin n) (ZMod q) //
          MissingSyndrome q s n H y} * (2 ^ n - 1) ≤
        Fintype.card (Matrix (Fin s) (Fin n) (ZMod q)) * q ^ s) :
    Fintype.card {H : Matrix (Fin s) (Fin n) (ZMod q) //
        ¬ ConstructionAZModSyndromeCovering q s n H} * 2 ^ n ≤
      2 * Fintype.card (Matrix (Fin s) (Fin n) (ZMod q)) * q ^ (2 * s) := by
  classical
  let Ω := Matrix (Fin s) (Fin n) (ZMod q)
  let Y := Fin s -> ZMod q
  let Bad :=
    {H : Matrix (Fin s) (Fin n) (ZMod q) //
      ¬ ConstructionAZModSyndromeCovering q s n H}
  let MissingFor :=
    fun y : Y => {H : Matrix (Fin s) (Fin n) (ZMod q) // MissingSyndrome q s n H y}
  have hbad :=
    syndromeCoverBad_card_le_sum_missing q s n
  have hbad_mul :
      Fintype.card Bad * (2 ^ n - 1) ≤
        (∑ y : Y, Fintype.card (MissingFor y)) * (2 ^ n - 1) := by
    exact Nat.mul_le_mul_right (2 ^ n - 1) (by simpa [Bad, MissingFor, Y] using hbad)
  rw [Finset.sum_mul] at hbad_mul
  have hsum :
      (∑ y : Y, Fintype.card (MissingFor y) * (2 ^ n - 1)) ≤
        ∑ _y : Y, Fintype.card Ω * q ^ s := by
    apply Finset.sum_le_sum
    intro y _hy
    by_cases hy0 : y = 0
    · subst y
      have hzero : Fintype.card (MissingFor 0) = 0 := by
        simpa [MissingFor] using missing_zero_card q s n
      rw [hzero]
      simp [Ω]
    · simpa [MissingFor, Ω] using hfixed y hy0
  have hYcard : Fintype.card Y = q ^ s := by
    simp [Y]
  have hbad_pred :
      Fintype.card Bad * (2 ^ n - 1) ≤ Fintype.card Ω * q ^ (2 * s) := by
    calc
      Fintype.card Bad * (2 ^ n - 1) ≤
          ∑ y : Y, Fintype.card (MissingFor y) * (2 ^ n - 1) := hbad_mul
      _ ≤ ∑ _y : Y, Fintype.card Ω * q ^ s := hsum
      _ = Fintype.card Ω * q ^ (2 * s) := by
          rw [Finset.sum_const, Finset.card_univ, hYcard]
          calc
            q ^ s * (Fintype.card Ω * q ^ s) =
                Fintype.card Ω * (q ^ s * q ^ s) := by ring
            _ = Fintype.card Ω * q ^ (s + s) := by rw [pow_add]
            _ = Fintype.card Ω * q ^ (2 * s) := by
                rw [show s + s = 2 * s by omega]
  have htwo_le_pow : 2 ≤ 2 ^ n := by
    cases n with
    | zero => omega
    | succ k =>
        have hpos : 0 < 2 ^ k := pow_pos (by norm_num : 0 < (2 : Nat)) k
        have hone : 1 ≤ 2 ^ k := hpos
        change 2 ≤ 2 ^ k * 2
        calc
          2 = 1 * 2 := by norm_num
          _ ≤ 2 ^ k * 2 := Nat.mul_le_mul_right 2 hone
  have hpow_le_twice_pred : 2 ^ n ≤ 2 * (2 ^ n - 1) := by
    omega
  calc
    Fintype.card Bad * 2 ^ n ≤ Fintype.card Bad * (2 * (2 ^ n - 1)) := by
      exact Nat.mul_le_mul_left (Fintype.card Bad) hpow_le_twice_pred
    _ = 2 * (Fintype.card Bad * (2 ^ n - 1)) := by ring
    _ ≤ 2 * (Fintype.card Ω * q ^ (2 * s)) := by
      exact Nat.mul_le_mul_left 2 hbad_pred
    _ = 2 * Fintype.card Ω * q ^ (2 * s) := by ring

private theorem syndromeCoverBad_card_bound
    (q s n : Nat) [NeZero q] (hq : Nat.Prime q) (hqodd : Odd q)
    (hn : 1 ≤ n) :
    Fintype.card {H : Matrix (Fin s) (Fin n) (ZMod q) //
        ¬ ConstructionAZModSyndromeCovering q s n H} * 2 ^ n ≤
      2 * Fintype.card (Matrix (Fin s) (Fin n) (ZMod q)) * q ^ (2 * s) := by
  exact syndromeCoverBad_card_bound_of_fixed_missing q s n hn
    (fun y hy => missing_fixed_syndrome_card_bound q s n hq hqodd hn hy)

private theorem syndromeCoverBad_card_lt_half_total_of_card_bound
    (q s n : Nat) [NeZero q]
    [Fintype {H : Matrix (Fin s) (Fin n) (ZMod q) //
      ¬ ConstructionAZModSyndromeCovering q s n H}]
    (hbound :
      Fintype.card {H : Matrix (Fin s) (Fin n) (ZMod q) //
          ¬ ConstructionAZModSyndromeCovering q s n H} * 2 ^ n ≤
        2 * Fintype.card (Matrix (Fin s) (Fin n) (ZMod q)) * q ^ (2 * s))
    (hsmall : 4 * q ^ (2 * s) < 2 ^ n) :
    2 * Fintype.card {H : Matrix (Fin s) (Fin n) (ZMod q) //
        ¬ ConstructionAZModSyndromeCovering q s n H} <
      Fintype.card (Matrix (Fin s) (Fin n) (ZMod q)) := by
  classical
  let Bad :=
    {H : Matrix (Fin s) (Fin n) (ZMod q) //
      ¬ ConstructionAZModSyndromeCovering q s n H}
  let Ω := Matrix (Fin s) (Fin n) (ZMod q)
  have hΩpos : 0 < Fintype.card Ω := Fintype.card_pos_iff.mpr ⟨0⟩
  have htwopow_pos : 0 < 2 ^ n := pow_pos (by norm_num : 0 < (2 : Nat)) n
  have hleft :
      (2 * Fintype.card Bad) * 2 ^ n ≤ Fintype.card Ω * (4 * q ^ (2 * s)) := by
    calc
      (2 * Fintype.card Bad) * 2 ^ n = 2 * (Fintype.card Bad * 2 ^ n) := by
        ring
      _ ≤ 2 * (2 * Fintype.card Ω * q ^ (2 * s)) := by
        exact Nat.mul_le_mul_left 2 (by simpa [Bad, Ω] using hbound)
      _ = Fintype.card Ω * (4 * q ^ (2 * s)) := by ring
  have hright : Fintype.card Ω * (4 * q ^ (2 * s)) < Fintype.card Ω * 2 ^ n :=
    mul_lt_mul_of_pos_left hsmall hΩpos
  have hmul :
      (2 * Fintype.card Bad) * 2 ^ n < Fintype.card Ω * 2 ^ n :=
    lt_of_le_of_lt hleft hright
  exact lt_of_mul_lt_mul_right hmul htwopow_pos.le

private theorem syndromeCoverBad_card_lt_half_total_of_fixed_missing
    (q s n : Nat) [NeZero q] (hn : 1 ≤ n)
    [Fintype {H : Matrix (Fin s) (Fin n) (ZMod q) //
      ¬ ConstructionAZModSyndromeCovering q s n H}]
    [∀ y : Fin s -> ZMod q,
      Fintype {H : Matrix (Fin s) (Fin n) (ZMod q) // MissingSyndrome q s n H y}]
    (hfixed : ∀ y : Fin s -> ZMod q, y ≠ 0 ->
      Fintype.card {H : Matrix (Fin s) (Fin n) (ZMod q) //
          MissingSyndrome q s n H y} * (2 ^ n - 1) ≤
        Fintype.card (Matrix (Fin s) (Fin n) (ZMod q)) * q ^ s)
    (hsmall : 4 * q ^ (2 * s) < 2 ^ n) :
    2 * Fintype.card {H : Matrix (Fin s) (Fin n) (ZMod q) //
        ¬ ConstructionAZModSyndromeCovering q s n H} <
      Fintype.card (Matrix (Fin s) (Fin n) (ZMod q)) := by
  exact syndromeCoverBad_card_lt_half_total_of_card_bound q s n
    (syndromeCoverBad_card_bound_of_fixed_missing q s n hn hfixed) hsmall

private noncomputable def constructionASyndromeRows (q : Nat) : Nat :=
  Nat.ceil (((q * q : Nat) : Real) / (5 * Real.log q))

private theorem constructionASyndromeRows_lower {q : Nat} (_hq : 2 ≤ q) :
    ((q * q : Nat) : Real) / (5 * Real.log q) ≤ constructionASyndromeRows q := by
  simpa [constructionASyndromeRows] using
    Nat.le_ceil (((q * q : Nat) : Real) / (5 * Real.log q))

private theorem constructionASyndromeRows_upper {q : Nat} (hq : 3 ≤ q) :
    (constructionASyndromeRows q : Real) ≤
      ((q * q : Nat) : Real) / (5 * Real.log q) + 1 := by
  have hxnonneg :
      0 ≤ ((q * q : Nat) : Real) / (5 * Real.log q) := by
    have hlog : 0 < Real.log (q : Real) :=
      Real.log_pos (by exact_mod_cast (show 1 < q from by omega))
    positivity
  exact (Nat.ceil_lt_add_one hxnonneg).le

private theorem eventually_log_le_const_sq {ε : Real} (hε : 0 < ε) :
    ∀ᶠ q : Nat in Filter.atTop,
      Real.log (q : Real) ≤ ε * (q : Real) ^ 2 := by
  have hsmall : Real.log =o[Filter.atTop] (fun x : Real => x ^ (2 : Real)) :=
    isLittleO_log_rpow_atTop (by norm_num : (0 : Real) < 2)
  have htend : Filter.Tendsto
      (fun x : Real => Real.log x / x ^ (2 : Real)) Filter.atTop (𝓝 0) := by
    exact hsmall.tendsto_div_nhds_zero
  have htendNat : Filter.Tendsto
      (fun q : Nat => Real.log (q : Real) / (q : Real) ^ (2 : Real))
        Filter.atTop (𝓝 0) := by
    exact htend.comp tendsto_natCast_atTop_atTop
  have hevAbs : ∀ᶠ q : Nat in Filter.atTop,
      |Real.log (q : Real) / (q : Real) ^ (2 : Real) - 0| < ε := by
    exact (Metric.tendsto_nhds.mp htendNat) ε hε
  filter_upwards [hevAbs, Filter.eventually_ge_atTop (1 : Nat)] with q hq hqge
  have hqpos : 0 < (q : Real) := by
    exact_mod_cast (Nat.succ_le_iff.mp hqge)
  have hpowpos : 0 < (q : Real) ^ (2 : Real) := Real.rpow_pos_of_pos hqpos 2
  have hdiv_le :
      Real.log (q : Real) / (q : Real) ^ (2 : Real) ≤ ε := by
    have hlt : |Real.log (q : Real) / (q : Real) ^ (2 : Real)| < ε := by
      simpa using hq
    exact (abs_lt.mp hlt).2.le
  have := (div_le_iff₀ hpowpos).mp hdiv_le
  simpa [mul_comm, mul_left_comm, mul_assoc, Real.rpow_natCast] using this

private theorem syndromeCover_power_small_aux {q : Nat} (hq3 : 3 ≤ q)
    (hlogq : Real.log (q : Real) ≤ (1 / 40 : Real) * (q : Real) ^ 2)
    (hlog4 : Real.log 4 ≤ (1 / 20 : Real) * (q : Real) ^ 2) :
    let s := constructionASyndromeRows q
    4 * q ^ (2 * s) < 2 ^ (q * q) := by
  dsimp
  let s := constructionASyndromeRows q
  have hqpos_nat : 0 < q := by omega
  have hqpos : 0 < (q : Real) := by exact_mod_cast hqpos_nat
  have hqne : (q : Real) ≠ 0 := hqpos.ne'
  have hlogpos : 0 < Real.log (q : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < q from by omega))
  have hlogne : Real.log (q : Real) ≠ 0 := hlogpos.ne'
  have hs_upper : (s : Real) ≤ ((q * q : Nat) : Real) / (5 * Real.log q) + 1 := by
    simpa [s] using constructionASyndromeRows_upper (q := q) hq3
  have hterm_le : ((2 * s : Nat) : Real) * Real.log (q : Real) ≤
      (2 / 5 : Real) * (q : Real) ^ 2 + 2 * Real.log (q : Real) := by
    have hmul := mul_le_mul_of_nonneg_right hs_upper
      (by positivity : 0 ≤ (2 : Real) * Real.log (q : Real))
    have heval : (((q * q : Nat) : Real) / (5 * Real.log q) + 1) *
        ((2 : Real) * Real.log (q : Real)) =
        (2 / 5 : Real) * (q : Real) ^ 2 + 2 * Real.log (q : Real) := by
      field_simp [hlogne]
      norm_num [Nat.cast_mul, pow_two]
    calc
      ((2 * s : Nat) : Real) * Real.log (q : Real) =
          (s : Real) * ((2 : Real) * Real.log (q : Real)) := by
            norm_num [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc]
      _ ≤ (((q * q : Nat) : Real) / (5 * Real.log q) + 1) *
          ((2 : Real) * Real.log (q : Real)) := hmul
      _ = (2 / 5 : Real) * (q : Real) ^ 2 + 2 * Real.log (q : Real) := heval
  have hleftlog :
      Real.log (((4 * q ^ (2 * s) : Nat) : Real)) =
        Real.log 4 + ((2 * s : Nat) : Real) * Real.log (q : Real) := by
    have hpowne : ((q : Real) ^ (2 * s)) ≠ 0 := pow_ne_zero _ hqne
    rw [Nat.cast_mul, Nat.cast_pow]
    rw [Real.log_mul (show ((4 : Nat) : Real) ≠ 0 by norm_num) hpowne,
      Real.log_pow]
    norm_num
  have hrightlog :
      Real.log (((2 ^ (q * q) : Nat) : Real)) = (q : Real) ^ 2 * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num [Nat.cast_mul, pow_two, mul_comm, mul_left_comm, mul_assoc]
  have hlog2half : (1 / 2 : Real) < Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hqSqpos : 0 < (q : Real) ^ 2 := sq_pos_of_ne_zero hqne
  have hleft_le_half :
      Real.log (((4 * q ^ (2 * s) : Nat) : Real)) ≤
        (1 / 2 : Real) * (q : Real) ^ 2 := by
    calc
      Real.log (((4 * q ^ (2 * s) : Nat) : Real)) =
          Real.log 4 + ((2 * s : Nat) : Real) * Real.log (q : Real) := hleftlog
      _ ≤ Real.log 4 +
          ((2 / 5 : Real) * (q : Real) ^ 2 + 2 * Real.log (q : Real)) := by
        nlinarith [hterm_le]
      _ ≤ (1 / 20 : Real) * (q : Real) ^ 2 +
            ((2 / 5 : Real) * (q : Real) ^ 2 +
              2 * ((1 / 40 : Real) * (q : Real) ^ 2)) := by
        nlinarith [hlog4, hlogq]
      _ = (1 / 2 : Real) * (q : Real) ^ 2 := by ring
  have hlog_lt :
      Real.log (((4 * q ^ (2 * s) : Nat) : Real)) <
        Real.log (((2 ^ (q * q) : Nat) : Real)) := by
    rw [hrightlog]
    nlinarith [hleft_le_half, mul_lt_mul_of_pos_right hlog2half hqSqpos]
  have hleftpos_nat : 0 < 4 * q ^ (2 * s) :=
    Nat.mul_pos (by norm_num) (pow_pos hqpos_nat _)
  have hrightpos_nat : 0 < 2 ^ (q * q) := pow_pos (by norm_num : 0 < (2 : Nat)) _
  have hleftpos : 0 < (((4 * q ^ (2 * s) : Nat) : Real)) := by
    exact_mod_cast hleftpos_nat
  have hrightpos : 0 < (((2 ^ (q * q) : Nat) : Real)) := by
    exact_mod_cast hrightpos_nat
  have hlt_real :
      (((4 * q ^ (2 * s) : Nat) : Real)) < (((2 ^ (q * q) : Nat) : Real)) :=
    (Real.log_lt_log_iff hleftpos hrightpos).mp hlog_lt
  exact_mod_cast hlt_real

private theorem eventually_log_four_le_twentieth_sq :
    ∀ᶠ q : Nat in Filter.atTop,
      Real.log 4 ≤ (1 / 20 : Real) * (q : Real) ^ 2 := by
  filter_upwards [Filter.eventually_ge_atTop (9 : Nat)] with q hq
  have hlog4le : Real.log 4 ≤ (4 : Real) :=
    Real.log_le_self (by norm_num : (0 : Real) ≤ 4)
  have hq2nat : 80 ≤ q ^ 2 := by
    nlinarith [sq_nonneg (q : Int)]
  have hq2 : (80 : Real) ≤ (q : Real) ^ 2 := by
    exact_mod_cast hq2nat
  nlinarith

private theorem eventually_syndromeCover_power_small :
    ∃ q0 : Nat, ∀ q : Nat, q0 ≤ q ->
      let s := constructionASyndromeRows q
      4 * q ^ (2 * s) < 2 ^ (q * q) := by
  have hlogq := eventually_log_le_const_sq (by norm_num : (0 : Real) < 1 / 40)
  have hlog4 := eventually_log_four_le_twentieth_sq
  have hlarge := Filter.eventually_ge_atTop (3 : Nat)
  have hev : ∀ᶠ q : Nat in Filter.atTop,
      let s := constructionASyndromeRows q
      4 * q ^ (2 * s) < 2 ^ (q * q) := by
    filter_upwards [hlogq, hlog4, hlarge] with q hqlog h4 hq3
    exact syndromeCover_power_small_aux hq3 hqlog h4
  rcases Filter.eventually_atTop.mp hev with ⟨q0, hq0⟩
  exact ⟨q0, fun q hq => hq0 q hq⟩

private theorem syndromeCoverBad_card_lt_half_total_for_large_prime_squares :
    ∃ q0 : Nat, ∀ q : Nat, q0 ≤ q -> Nat.Prime q -> Odd q ->
      let s := constructionASyndromeRows q
      2 * Nat.card {H : Matrix (Fin s) (Fin (q * q)) (ZMod q) //
          ¬ ConstructionAZModSyndromeCovering q s (q * q) H} <
        Nat.card (Matrix (Fin s) (Fin (q * q)) (ZMod q)) := by
  classical
  rcases eventually_syndromeCover_power_small with ⟨qCover, hcoverSmall⟩
  refine ⟨qCover, ?_⟩
  intro q hqCover hqprime hqodd
  dsimp
  let s := constructionASyndromeRows q
  haveI : NeZero q := ⟨hqprime.ne_zero⟩
  have hn : 1 ≤ q * q := by
    exact Nat.succ_le_of_lt (Nat.mul_pos hqprime.pos hqprime.pos)
  have hsmall : 4 * q ^ (2 * s) < 2 ^ (q * q) := by
    simpa [s] using hcoverSmall q hqCover
  have hhalf :
      2 * Fintype.card {H : Matrix (Fin s) (Fin (q * q)) (ZMod q) //
          ¬ ConstructionAZModSyndromeCovering q s (q * q) H} <
        Fintype.card (Matrix (Fin s) (Fin (q * q)) (ZMod q)) := by
    exact syndromeCoverBad_card_lt_half_total_of_card_bound q s (q * q)
      (syndromeCoverBad_card_bound q s (q * q) hqprime hqodd hn) hsmall
  simpa [s, Nat.card_eq_fintype_card] using hhalf

private theorem eventually_log_two_le_cent_sq :
    ∃ q0 : Nat, ∀ q : Nat, q0 ≤ q ->
      Real.log 2 ≤ (1 / 100 : Real) * (q : Real) ^ 2 := by
  refine ⟨15, ?_⟩
  intro q hq
  have hlog2le : Real.log 2 ≤ (2 : Real) :=
    Real.log_le_self (by norm_num : (0 : Real) ≤ 2)
  have hq2nat : 200 ≤ q ^ 2 := by
    nlinarith [sq_nonneg (q : Int)]
  have hq2 : (200 : Real) ≤ (q : Real) ^ 2 := by
    exact_mod_cast hq2nat
  nlinarith

private theorem shortKernel_power_small_aux {q : Nat} (hq2 : 2 ≤ q)
    (hlog2 : Real.log 2 ≤ (1 / 100 : Real) * (q : Real) ^ 2) :
    let s := constructionASyndromeRows q
    2 * Nat.card (ShortIntegerVector (q * q)) < q ^ s := by
  dsimp
  let s := constructionASyndromeRows q
  haveI : Finite (ShortIntegerVector (q * q)) := shortIntegerVector_finite (q * q)
  haveI : Fintype (ShortIntegerVector (q * q)) :=
    Fintype.ofFinite (ShortIntegerVector (q * q))
  have hn : 1 ≤ q * q := by
    exact Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
  have hcard :
      (Nat.card (ShortIntegerVector (q * q)) : Real) ≤
        Real.exp ((101 / 1000 : Real) * ((q * q : Nat) : Real)) :=
    shortIntegerVector_card_exp_bound (q * q) hn
  have hlogpos : 0 < Real.log (q : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < q from by omega))
  have hs_lower :
      ((q * q : Nat) : Real) / (5 * Real.log q) ≤ (s : Real) := by
    simpa [s] using constructionASyndromeRows_lower (q := q) hq2
  have hslog_ge : (1 / 5 : Real) * (q : Real) ^ 2 ≤ (s : Real) * Real.log q := by
    have hmul := mul_le_mul_of_nonneg_right hs_lower hlogpos.le
    have hlogne : Real.log (q : Real) ≠ 0 := hlogpos.ne'
    field_simp [hlogne] at hmul
    have hqcast : ((q * q : Nat) : Real) = (q : Real) ^ 2 := by
      norm_num [Nat.cast_mul, pow_two]
    rw [hqcast] at hmul
    nlinarith
  have hleft_le :
      ((2 * Nat.card (ShortIntegerVector (q * q)) : Nat) : Real) ≤
        2 * Real.exp ((101 / 1000 : Real) * ((q * q : Nat) : Real)) := by
    simpa [Nat.cast_mul] using
      mul_le_mul_of_nonneg_left hcard (by norm_num : (0 : Real) ≤ 2)
  have hqpos_nat : 0 < q := by omega
  have hqpos : 0 < (q : Real) := by exact_mod_cast hqpos_nat
  have hrightpos_nat : 0 < q ^ s := pow_pos hqpos_nat s
  have hrightpos : 0 < ((q ^ s : Nat) : Real) := by exact_mod_cast hrightpos_nat
  have hleftpos :
      0 < 2 * Real.exp ((101 / 1000 : Real) * ((q * q : Nat) : Real)) := by
    positivity
  have hlog_left :
      Real.log (2 * Real.exp ((101 / 1000 : Real) * ((q * q : Nat) : Real))) =
        Real.log 2 + (101 / 1000 : Real) * ((q * q : Nat) : Real) := by
    rw [Real.log_mul (by norm_num : (2 : Real) ≠ 0) (Real.exp_ne_zero _), Real.log_exp]
  have hlog_right :
      Real.log (((q ^ s : Nat) : Real)) = (s : Real) * Real.log q := by
    rw [Nat.cast_pow, Real.log_pow]
  have hlog_lt :
      Real.log (2 * Real.exp ((101 / 1000 : Real) * ((q * q : Nat) : Real))) <
        Real.log (((q ^ s : Nat) : Real)) := by
    rw [hlog_left, hlog_right]
    have hqcast : ((q * q : Nat) : Real) = (q : Real) ^ 2 := by
      norm_num [Nat.cast_mul, pow_two]
    nlinarith
  have hreal_lt :
      2 * Real.exp ((101 / 1000 : Real) * ((q * q : Nat) : Real)) <
        ((q ^ s : Nat) : Real) :=
    (Real.log_lt_log_iff hleftpos hrightpos).mp hlog_lt
  have hnat_real_lt :
      ((2 * Nat.card (ShortIntegerVector (q * q)) : Nat) : Real) <
        ((q ^ s : Nat) : Real) :=
    lt_of_le_of_lt hleft_le hreal_lt
  exact_mod_cast hnat_real_lt

private theorem eventually_shortKernel_power_small :
    ∃ q0 : Nat, ∀ q : Nat, q0 ≤ q ->
      let s := constructionASyndromeRows q
      2 * Nat.card (ShortIntegerVector (q * q)) < q ^ s := by
  rcases eventually_log_two_le_cent_sq with ⟨qLog, hqLog⟩
  refine ⟨max 2 qLog, ?_⟩
  intro q hq
  have hq2 : 2 ≤ q := le_trans (Nat.le_max_left 2 qLog) hq
  have hqLog' : qLog ≤ q := le_trans (Nat.le_max_right 2 qLog) hq
  exact shortKernel_power_small_aux hq2 (hqLog q hqLog')

private theorem shortKernelBad_card_lt_half_total_for_large_prime_squares :
    ∃ q0 : Nat, ∀ q : Nat, q0 ≤ q -> Nat.Prime q -> Odd q ->
      let s := constructionASyndromeRows q
      2 * Nat.card {H : Matrix (Fin s) (Fin (q * q)) (ZMod q) //
          ¬ ConstructionAShortKernelGood q s (q * q) H} <
        Nat.card (Matrix (Fin s) (Fin (q * q)) (ZMod q)) := by
  classical
  rcases eventually_shortKernel_power_small with ⟨qShort, hshortSmall⟩
  refine ⟨qShort, ?_⟩
  intro q hqShort hqprime _hqodd
  dsimp
  let s := constructionASyndromeRows q
  haveI : NeZero q := ⟨hqprime.ne_zero⟩
  have hsmall : 2 * Nat.card (ShortIntegerVector (q * q)) < q ^ s := by
    simpa [s] using hshortSmall q hqShort
  have hhalf :
      2 * Nat.card {H : Matrix (Fin s) (Fin (q * q)) (ZMod q) //
          ¬ ConstructionAShortKernelGood q s (q * q) H} <
        Nat.card (Matrix (Fin s) (Fin (q * q)) (ZMod q)) :=
    shortKernelBad_card_lt_half_total_of_short_card q s hqprime hsmall
  simpa [s] using hhalf

private def intBooleanLift {q n : Nat} (ε : Fin n -> ZMod q) : Fin n -> Int :=
  fun i => if ε i = 0 then 0 else 1

private lemma intBooleanLift_isBoolean {q n : Nat} (ε : Fin n -> ZMod q) :
    ∀ i : Fin n, intBooleanLift ε i = 0 ∨ intBooleanLift ε i = 1 := by
  intro i
  by_cases hεi : ε i = 0
  · left
    simp [intBooleanLift, hεi]
  · right
    simp [intBooleanLift, hεi]

private lemma intVectorMod_intBooleanLift_eq {q n : Nat}
    (ε : Fin n -> ZMod q) (hε : IsBooleanVector ε) :
    intVectorMod q n (intBooleanLift ε) = ε := by
  funext i
  by_cases hεi : ε i = 0
  · simp [intVectorMod, intBooleanLift, hεi]
  · rcases hε i with hzero | hone
    · exact False.elim (hεi hzero)
    · change ((if ε i = 0 then (0 : Int) else 1 : Int) : ZMod q) = ε i
      rw [if_neg hεi]
      simpa using hone.symm

private lemma constructionASyndromeCovering_of_zmod_boolean_covering
    {q s n : Nat} {H : Matrix (Fin s) (Fin n) (ZMod q)}
    (hcover : ConstructionAZModSyndromeCovering q s n H) :
    ConstructionASyndromeCovering q s n H := by
  intro y
  obtain ⟨ε, hεbool, hεsyn⟩ := hcover y
  refine ⟨intBooleanLift ε, intBooleanLift_isBoolean ε, ?_⟩
  unfold constructionASyndrome
  rw [intVectorMod_intBooleanLift_eq ε hεbool]
  exact hεsyn

private lemma exists_constructionAKernel_lattice_bounds_of_zmod_good_matrix
    {q s n : Nat} [NeZero q] (H : Matrix (Fin s) (Fin n) (ZMod q)) (hn : 1 ≤ n)
    (hshort : ConstructionAShortKernelGood q s n H)
    (hcover : ConstructionAZModSyndromeCovering q s n H) :
    ∃ Γ : KNFullRankLattice n,
      (1 / 10 : Real) * Real.sqrt (n : Real) ≤ shortestVectorLength Γ ∧
        coveringRadius Γ ≤ (3 / 2 : Real) * Real.sqrt (n : Real) :=
  exists_constructionAKernel_lattice_bounds_of_good_matrix H hn hshort
    (constructionASyndromeCovering_of_zmod_boolean_covering hcover)

private lemma exists_of_card_bad_add_lt_total {α : Type*} [Fintype α]
    (P Q : α -> Prop) [Fintype {x : α // ¬ P x}] [Fintype {x : α // ¬ Q x}]
    [Fintype {x : α // ¬ P x ∨ ¬ Q x}]
    (hcard : Fintype.card {x : α // ¬ P x} + Fintype.card {x : α // ¬ Q x} <
      Fintype.card α) :
    ∃ x : α, P x ∧ Q x := by
  by_contra hnone
  have hcover : ∀ x : α, ¬ P x ∨ ¬ Q x := by
    intro x
    by_cases hP : P x
    · right
      intro hQ
      exact hnone ⟨x, hP, hQ⟩
    · exact Or.inl hP
  let f : α -> {x : α // ¬ P x ∨ ¬ Q x} := fun x => ⟨x, hcover x⟩
  have hf : Function.Injective f := by
    intro x y hxy
    exact congrArg Subtype.val hxy
  have htotal_le_union : Fintype.card α ≤ Fintype.card {x : α // ¬ P x ∨ ¬ Q x} :=
    Fintype.card_le_of_injective f hf
  have hunion_le : Fintype.card {x : α // ¬ P x ∨ ¬ Q x} ≤
      Fintype.card {x : α // ¬ P x} + Fintype.card {x : α // ¬ Q x} :=
    Fintype.card_subtype_or (fun x : α => ¬ P x) (fun x : α => ¬ Q x)
  exact not_lt_of_ge (le_trans htotal_le_union hunion_le) hcard

private lemma exists_constructionAGoodMatrix_of_bad_card_lt
    (q s n : Nat) [NeZero q]
    [Fintype {H : Matrix (Fin s) (Fin n) (ZMod q) //
      ¬ ConstructionAShortKernelGood q s n H}]
    [Fintype {H : Matrix (Fin s) (Fin n) (ZMod q) //
      ¬ ConstructionASyndromeCovering q s n H}]
    [Fintype {H : Matrix (Fin s) (Fin n) (ZMod q) //
      ¬ ConstructionAShortKernelGood q s n H ∨ ¬ ConstructionASyndromeCovering q s n H}]
    (hcard :
      Fintype.card {H : Matrix (Fin s) (Fin n) (ZMod q) //
          ¬ ConstructionAShortKernelGood q s n H} +
        Fintype.card {H : Matrix (Fin s) (Fin n) (ZMod q) //
          ¬ ConstructionASyndromeCovering q s n H} <
          Fintype.card (Matrix (Fin s) (Fin n) (ZMod q))) :
    ∃ H : Matrix (Fin s) (Fin n) (ZMod q),
      ConstructionAShortKernelGood q s n H ∧ ConstructionASyndromeCovering q s n H := by
  classical
  exact exists_of_card_bad_add_lt_total
    (ConstructionAShortKernelGood q s n)
    (ConstructionASyndromeCovering q s n) hcard

private lemma exists_primeSquare_lattice_bounds_of_bad_card_lt
    (q s : Nat) [NeZero q] (hq : Nat.Prime q)
    [Fintype {H : Matrix (Fin s) (Fin (q * q)) (ZMod q) //
      ¬ ConstructionAShortKernelGood q s (q * q) H}]
    [Fintype {H : Matrix (Fin s) (Fin (q * q)) (ZMod q) //
      ¬ ConstructionASyndromeCovering q s (q * q) H}]
    [Fintype {H : Matrix (Fin s) (Fin (q * q)) (ZMod q) //
      ¬ ConstructionAShortKernelGood q s (q * q) H ∨
        ¬ ConstructionASyndromeCovering q s (q * q) H}]
    (hcard :
      Fintype.card {H : Matrix (Fin s) (Fin (q * q)) (ZMod q) //
          ¬ ConstructionAShortKernelGood q s (q * q) H} +
        Fintype.card {H : Matrix (Fin s) (Fin (q * q)) (ZMod q) //
          ¬ ConstructionASyndromeCovering q s (q * q) H} <
          Fintype.card (Matrix (Fin s) (Fin (q * q)) (ZMod q))) :
    ∃ Γ : KNFullRankLattice (q * q),
      (1 / 10 : Real) * Real.sqrt ((q * q : Nat) : Real) ≤ shortestVectorLength Γ ∧
        coveringRadius Γ ≤ (3 / 2 : Real) * Real.sqrt ((q * q : Nat) : Real) := by
  obtain ⟨H, hshort, hcover⟩ :=
    exists_constructionAGoodMatrix_of_bad_card_lt q s (q * q) hcard
  exact exists_primeSquare_constructionAKernel_lattice_bounds_of_good_matrix hq H hshort hcover

private lemma exists_constructionAZModGoodMatrix_of_bad_card_lt
    (q s n : Nat) [NeZero q]
    [Fintype {H : Matrix (Fin s) (Fin n) (ZMod q) //
      ¬ ConstructionAShortKernelGood q s n H}]
    [Fintype {H : Matrix (Fin s) (Fin n) (ZMod q) //
      ¬ ConstructionAZModSyndromeCovering q s n H}]
    [Fintype {H : Matrix (Fin s) (Fin n) (ZMod q) //
      ¬ ConstructionAShortKernelGood q s n H ∨
        ¬ ConstructionAZModSyndromeCovering q s n H}]
    (hcard :
      Fintype.card {H : Matrix (Fin s) (Fin n) (ZMod q) //
          ¬ ConstructionAShortKernelGood q s n H} +
        Fintype.card {H : Matrix (Fin s) (Fin n) (ZMod q) //
          ¬ ConstructionAZModSyndromeCovering q s n H} <
          Fintype.card (Matrix (Fin s) (Fin n) (ZMod q))) :
    ∃ H : Matrix (Fin s) (Fin n) (ZMod q),
      ConstructionAShortKernelGood q s n H ∧
        ConstructionAZModSyndromeCovering q s n H := by
  classical
  exact exists_of_card_bad_add_lt_total
    (ConstructionAShortKernelGood q s n)
    (ConstructionAZModSyndromeCovering q s n) hcard

private lemma exists_primeSquare_lattice_bounds_of_zmod_bad_card_lt
    (q s : Nat) [NeZero q] (hq : Nat.Prime q)
    [Fintype {H : Matrix (Fin s) (Fin (q * q)) (ZMod q) //
      ¬ ConstructionAShortKernelGood q s (q * q) H}]
    [Fintype {H : Matrix (Fin s) (Fin (q * q)) (ZMod q) //
      ¬ ConstructionAZModSyndromeCovering q s (q * q) H}]
    [Fintype {H : Matrix (Fin s) (Fin (q * q)) (ZMod q) //
      ¬ ConstructionAShortKernelGood q s (q * q) H ∨
        ¬ ConstructionAZModSyndromeCovering q s (q * q) H}]
    (hcard :
      Fintype.card {H : Matrix (Fin s) (Fin (q * q)) (ZMod q) //
          ¬ ConstructionAShortKernelGood q s (q * q) H} +
        Fintype.card {H : Matrix (Fin s) (Fin (q * q)) (ZMod q) //
          ¬ ConstructionAZModSyndromeCovering q s (q * q) H} <
          Fintype.card (Matrix (Fin s) (Fin (q * q)) (ZMod q))) :
    ∃ Γ : KNFullRankLattice (q * q),
      (1 / 10 : Real) * Real.sqrt ((q * q : Nat) : Real) ≤ shortestVectorLength Γ ∧
        coveringRadius Γ ≤ (3 / 2 : Real) * Real.sqrt ((q * q : Nat) : Real) := by
  obtain ⟨H, hshort, hcover⟩ :=
    exists_constructionAZModGoodMatrix_of_bad_card_lt q s (q * q) hcard
  have hn : 1 ≤ q * q := by
    have hqpos : 0 < q := hq.pos
    exact Nat.succ_le_of_lt (Nat.mul_pos hqpos hqpos)
  exact exists_constructionAKernel_lattice_bounds_of_zmod_good_matrix H hn hshort hcover

private lemma exists_primeSquare_lattice_bounds_of_zmod_nat_bad_card_lt
    (q s : Nat) [NeZero q] (hq : Nat.Prime q)
    (hcard :
      Nat.card {H : Matrix (Fin s) (Fin (q * q)) (ZMod q) //
          ¬ ConstructionAShortKernelGood q s (q * q) H} +
        Nat.card {H : Matrix (Fin s) (Fin (q * q)) (ZMod q) //
          ¬ ConstructionAZModSyndromeCovering q s (q * q) H} <
          Nat.card (Matrix (Fin s) (Fin (q * q)) (ZMod q))) :
    ∃ Γ : KNFullRankLattice (q * q),
      (1 / 10 : Real) * Real.sqrt ((q * q : Nat) : Real) ≤ shortestVectorLength Γ ∧
        coveringRadius Γ ≤ (3 / 2 : Real) * Real.sqrt ((q * q : Nat) : Real) := by
  classical
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hcard
  exact exists_primeSquare_lattice_bounds_of_zmod_bad_card_lt q s hq hcard

private theorem goodConstructionALattice_primeSquare_of_bad_card_lt
    (hbad :
      ∃ q0 : Nat, ∀ q : Nat, q0 ≤ q -> Nat.Prime q -> Odd q ->
        let s := constructionASyndromeRows q
        Nat.card {H : Matrix (Fin s) (Fin (q * q)) (ZMod q) //
            ¬ ConstructionAShortKernelGood q s (q * q) H} +
          Nat.card {H : Matrix (Fin s) (Fin (q * q)) (ZMod q) //
            ¬ ConstructionAZModSyndromeCovering q s (q * q) H} <
            Nat.card (Matrix (Fin s) (Fin (q * q)) (ZMod q))) :
    ∃ q0 : Nat, ∀ q : Nat, q0 ≤ q -> Nat.Prime q -> Odd q ->
      ∃ Γ : KNFullRankLattice (q * q),
        (1 / 10 : Real) * Real.sqrt ((q * q : Nat) : Real) ≤ shortestVectorLength Γ ∧
          coveringRadius Γ ≤ (3 / 2 : Real) * Real.sqrt ((q * q : Nat) : Real) := by
  classical
  rcases hbad with ⟨q0, hbad⟩
  refine ⟨q0, ?_⟩
  intro q hq0 hqprime hqodd
  haveI : NeZero q := ⟨hqprime.ne_zero⟩
  exact exists_primeSquare_lattice_bounds_of_zmod_nat_bad_card_lt q
    (constructionASyndromeRows q) hqprime (hbad q hq0 hqprime hqodd)

private theorem constructionA_bad_card_lt_for_large_prime_squares_of_halves
    (hshort :
      ∃ q0 : Nat, ∀ q : Nat, q0 ≤ q -> Nat.Prime q -> Odd q ->
        let s := constructionASyndromeRows q
        2 * Nat.card {H : Matrix (Fin s) (Fin (q * q)) (ZMod q) //
            ¬ ConstructionAShortKernelGood q s (q * q) H} <
          Nat.card (Matrix (Fin s) (Fin (q * q)) (ZMod q)))
    (hcover :
      ∃ q0 : Nat, ∀ q : Nat, q0 ≤ q -> Nat.Prime q -> Odd q ->
        let s := constructionASyndromeRows q
        2 * Nat.card {H : Matrix (Fin s) (Fin (q * q)) (ZMod q) //
            ¬ ConstructionAZModSyndromeCovering q s (q * q) H} <
          Nat.card (Matrix (Fin s) (Fin (q * q)) (ZMod q))) :
    ∃ q0 : Nat, ∀ q : Nat, q0 ≤ q -> Nat.Prime q -> Odd q ->
      let s := constructionASyndromeRows q
      Nat.card {H : Matrix (Fin s) (Fin (q * q)) (ZMod q) //
          ¬ ConstructionAShortKernelGood q s (q * q) H} +
        Nat.card {H : Matrix (Fin s) (Fin (q * q)) (ZMod q) //
          ¬ ConstructionAZModSyndromeCovering q s (q * q) H} <
          Nat.card (Matrix (Fin s) (Fin (q * q)) (ZMod q)) := by
  rcases hshort with ⟨qShort, hshort⟩
  rcases hcover with ⟨qCover, hcover⟩
  refine ⟨max qShort qCover, ?_⟩
  intro q hq0 hqprime hqodd
  have hqShort : qShort ≤ q := le_trans (Nat.le_max_left qShort qCover) hq0
  have hqCover : qCover ≤ q := le_trans (Nat.le_max_right qShort qCover) hq0
  specialize hshort q hqShort hqprime hqodd
  specialize hcover q hqCover hqprime hqodd
  omega

private theorem goodConstructionALattice_primeSquare_of_half_bad_card_lt
    (hshort :
      ∃ q0 : Nat, ∀ q : Nat, q0 ≤ q -> Nat.Prime q -> Odd q ->
        let s := constructionASyndromeRows q
        2 * Nat.card {H : Matrix (Fin s) (Fin (q * q)) (ZMod q) //
            ¬ ConstructionAShortKernelGood q s (q * q) H} <
          Nat.card (Matrix (Fin s) (Fin (q * q)) (ZMod q)))
    (hcover :
      ∃ q0 : Nat, ∀ q : Nat, q0 ≤ q -> Nat.Prime q -> Odd q ->
        let s := constructionASyndromeRows q
        2 * Nat.card {H : Matrix (Fin s) (Fin (q * q)) (ZMod q) //
            ¬ ConstructionAZModSyndromeCovering q s (q * q) H} <
          Nat.card (Matrix (Fin s) (Fin (q * q)) (ZMod q))) :
    ∃ q0 : Nat, ∀ q : Nat, q0 ≤ q -> Nat.Prime q -> Odd q ->
      ∃ Γ : KNFullRankLattice (q * q),
        (1 / 10 : Real) * Real.sqrt ((q * q : Nat) : Real) ≤ shortestVectorLength Γ ∧
          coveringRadius Γ ≤ (3 / 2 : Real) * Real.sqrt ((q * q : Nat) : Real) :=
  goodConstructionALattice_primeSquare_of_bad_card_lt
    (constructionA_bad_card_lt_for_large_prime_squares_of_halves hshort hcover)

/-- Good Construction-A lattices exist in large odd-prime-square dimensions. -/
theorem goodConstructionALattice_primeSquare :
    ∃ q0 : Nat, ∀ q : Nat, q0 ≤ q -> Nat.Prime q -> Odd q ->
      ∃ Γ : KNFullRankLattice (q * q),
        (1 / 10 : Real) * Real.sqrt ((q * q : Nat) : Real) ≤ shortestVectorLength Γ ∧
          coveringRadius Γ ≤ (3 / 2 : Real) * Real.sqrt ((q * q : Nat) : Real) := by
  exact goodConstructionALattice_primeSquare_of_half_bad_card_lt
    shortKernelBad_card_lt_half_total_for_large_prime_squares
    syndromeCoverBad_card_lt_half_total_for_large_prime_squares

/-- Rescaled good lattices with `N(Γ)=1` and bounded covering radius. -/
theorem rescaledGoodConstructionALattice :
    ∃ q0 : Nat, ∀ q : Nat, q0 ≤ q -> Nat.Prime q -> Odd q ->
      ∃ Γ : KNFullRankLattice (q * q),
        shortestVectorLength Γ = 1 ∧ coveringRadius Γ ≤ 15 := by
  obtain ⟨q0, hgood⟩ := goodConstructionALattice_primeSquare
  refine ⟨q0, ?_⟩
  intro q hq0 hprime hodd
  rcases hgood q hq0 hprime hodd with ⟨Γ, hN, hR⟩
  let S : Real := Real.sqrt ((q * q : Nat) : Real)
  have hSpos : 0 < S := by
    have hqpos : 0 < q := hprime.pos
    have hnpos : 0 < q * q := Nat.mul_pos hqpos hqpos
    exact Real.sqrt_pos.mpr (by exact_mod_cast hnpos)
  have hNpos : 0 < shortestVectorLength Γ := by
    have hlower_pos : 0 < (1 / 10 : Real) * S := by positivity
    exact lt_of_lt_of_le hlower_pos (by simpa [S] using hN)
  let t : Real := (shortestVectorLength Γ)⁻¹
  have ht : 0 < t := inv_pos.mpr hNpos
  let Γ' : KNFullRankLattice (q * q) := ⟨scaledLatticeBasis Γ.basis t ht.ne'⟩
  refine ⟨Γ', ?_, ?_⟩
  · change shortestVectorLength
        (⟨scaledLatticeBasis Γ.basis t ht.ne'⟩ : KNFullRankLattice (q * q)) = 1
    rw [shortestVectorLength_scaled Γ ht]
    simpa [t] using inv_mul_cancel₀ hNpos.ne'
  · change coveringRadius
        (⟨scaledLatticeBasis Γ.basis t ht.ne'⟩ : KNFullRankLattice (q * q)) ≤ 15
    rw [coveringRadius_scaled Γ ht]
    have hmul : (3 / 2 : Real) * S ≤ 15 * shortestVectorLength Γ := by
      nlinarith [hN]
    have hnonneg : 0 ≤ (shortestVectorLength Γ)⁻¹ := inv_nonneg.mpr hNpos.le
    have hscaled_upper :
        (shortestVectorLength Γ)⁻¹ * ((3 / 2 : Real) * S) ≤ 15 := by
      have htmp := mul_le_mul_of_nonneg_left hmul hnonneg
      field_simp [hNpos.ne'] at htmp ⊢
      nlinarith
    calc
      t * coveringRadius Γ ≤ t * ((3 / 2 : Real) * S) := by
        exact mul_le_mul_of_nonneg_left (by simpa [S] using hR) ht.le
      _ ≤ 15 := by
        simpa [t] using hscaled_upper

/-- Odd prime squares are unbounded. -/
theorem arbitrarilyLargeOddPrimeSquares :
    ∀ N : Nat, ∃ q : Nat, Nat.Prime q ∧ Odd q ∧ N ≤ q * q := by
  intro N
  obtain ⟨q, hqge, hprime⟩ := Nat.exists_infinite_primes (max N 3)
  refine ⟨q, hprime, hprime.odd_of_ne_two ?_, ?_⟩
  · omega
  · have hNq : N ≤ q := le_trans (Nat.le_max_left N 3) hqge
    exact le_trans hNq (Nat.le_mul_self q)

/-- The final dual lattice used in the Khot--Naor construction. -/
noncomputable def finalKhotNaorLattice {n : Nat} (Γ : KNFullRankLattice n) :
    KNFullRankLattice n :=
  knDualLattice Γ

/-- The dual of the final lattice is the original Construction-A lattice. -/
theorem finalKhotNaorLattice_dual {n : Nat} (Γ : KNFullRankLattice n) :
    IsDualLattice (finalKhotNaorLattice Γ) Γ := by
  simpa [finalKhotNaorLattice] using knDoubleDual Γ

private lemma coveringRadius_pos_of_shortest_eq_one {n : Nat}
    (hn : 1 ≤ n) (Λ : KNFullRankLattice n)
    (hshort : shortestVectorLength Λ = 1) :
    0 < coveringRadius Λ := by
  have hhalf := half_shortestVectorLength_le_coveringRadius hn Λ
  have hhalf_pos : 0 < (1 / 2 : Real) * shortestVectorLength Λ := by
    rw [hshort]
    norm_num
  exact lt_of_lt_of_le hhalf_pos hhalf

private lemma isDualLattice_carrier_eq {n : Nat}
    {Λ Γ Δ : KNFullRankLattice n}
    (hΓ : IsDualLattice Λ Γ) (hΔ : IsDualLattice Λ Δ) :
    Γ.carrier = Δ.carrier := by
  ext u
  rw [hΓ u, hΔ u]

private lemma shortestVectorLength_eq_of_carrier_eq {n : Nat}
    {Λ Γ : KNFullRankLattice n} (h : Λ.carrier = Γ.carrier) :
    shortestVectorLength Λ = shortestVectorLength Γ := by
  unfold shortestVectorLength
  rw [h]

private lemma distanceToLattice_eq_of_carrier_eq {n : Nat}
    {Λ Γ : KNFullRankLattice n} (h : Λ.carrier = Γ.carrier)
    (x : RealEuclideanSpace n) :
    distanceToLattice Λ x = distanceToLattice Γ x := by
  unfold distanceToLattice
  rw [h]

private lemma coveringRadius_eq_of_carrier_eq {n : Nat}
    {Λ Γ : KNFullRankLattice n} (h : Λ.carrier = Γ.carrier) :
    coveringRadius Λ = coveringRadius Γ := by
  have hfun : distanceToLattice Λ = distanceToLattice Γ := by
    funext x
    exact distanceToLattice_eq_of_carrier_eq h x
  simp [coveringRadius, hfun]

private lemma knDual_finalKhotNaorLattice_carrier_eq {n : Nat}
    (Γ : KNFullRankLattice n) :
    (knDualLattice (finalKhotNaorLattice Γ)).carrier = Γ.carrier :=
  isDualLattice_carrier_eq (knDualLattice_spec (finalKhotNaorLattice Γ))
    (finalKhotNaorLattice_dual Γ)

private lemma shortestVectorLength_knDual_finalKhotNaorLattice {n : Nat}
    (Γ : KNFullRankLattice n) :
    shortestVectorLength (knDualLattice (finalKhotNaorLattice Γ)) =
      shortestVectorLength Γ :=
  shortestVectorLength_eq_of_carrier_eq (knDual_finalKhotNaorLattice_carrier_eq Γ)

private lemma coveringRadius_knDual_finalKhotNaorLattice {n : Nat}
    (Γ : KNFullRankLattice n) :
    coveringRadius (knDualLattice (finalKhotNaorLattice Γ)) =
      coveringRadius Γ :=
  coveringRadius_eq_of_carrier_eq (knDual_finalKhotNaorLattice_carrier_eq Γ)

/-- The final Khot--Naor constant `sqrt 7 / (480e)`. -/
noncomputable def khotNaorFinalConstant : Real :=
  Real.sqrt 7 / (480 * Real.exp 1)

/-- Positivity of the final Khot--Naor constant. -/
theorem khotNaorFinalConstant_pos :
    0 < khotNaorFinalConstant := by
  unfold khotNaorFinalConstant
  positivity

/-- Real-valued flat-torus lower bound transferred to represented project lattices. -/
theorem khotNaorProjectForm :
    exists c : Real, 0 < c /\
      forall N : Nat, exists n : Nat, N <= n /\
        exists A : LatticeBasis n,
          ENNReal.ofReal (c * Real.sqrt (n : Real)) <=
            (letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A;
              hilbertDistortion (flatTorus n A)) := by
  classical
  refine ⟨khotNaorFinalConstant, khotNaorFinalConstant_pos, ?_⟩
  intro N
  obtain ⟨q0, hgood⟩ := rescaledGoodConstructionALattice
  obtain ⟨q, hqge, hprime⟩ := Nat.exists_infinite_primes (max (max N q0) 3)
  have hodd : Odd q := hprime.odd_of_ne_two (by omega)
  have hq0 : q0 ≤ q := by
    exact le_trans (by omega : q0 ≤ max (max N q0) 3) hqge
  have hNq : N ≤ q := by
    exact le_trans (by omega : N ≤ max (max N q0) 3) hqge
  have hqpos : 0 < q := hprime.pos
  have hnpos : 0 < q * q := Nat.mul_pos hqpos hqpos
  have hn : 1 ≤ q * q := by omega
  have hNn : N ≤ q * q := le_trans hNq (Nat.le_mul_self q)
  rcases hgood q hq0 hprime hodd with ⟨Γ, hshort, hcover⟩
  let Λ : KNFullRankLattice (q * q) := finalKhotNaorLattice Γ
  refine ⟨q * q, hNn, Λ.basis, ?_⟩
  have hdual := dualLatticeHilbertLowerBound (n := q * q) hn Λ
  have hRpos : 0 < coveringRadius Γ :=
    coveringRadius_pos_of_shortest_eq_one hn Γ hshort
  have hshort_dual :
      shortestVectorLength (knDualLattice Λ) = 1 := by
    change shortestVectorLength (knDualLattice (finalKhotNaorLattice Γ)) = 1
    rw [shortestVectorLength_knDual_finalKhotNaorLattice Γ, hshort]
  have hcover_dual :
      coveringRadius (knDualLattice Λ) ≤ 15 := by
    change coveringRadius (knDualLattice (finalKhotNaorLattice Γ)) ≤ 15
    rw [coveringRadius_knDual_finalKhotNaorLattice Γ]
    exact hcover
  have hRdual_pos :
      0 < coveringRadius (knDualLattice Λ) := by
    change 0 < coveringRadius (knDualLattice (finalKhotNaorLattice Γ))
    rw [coveringRadius_knDual_finalKhotNaorLattice Γ]
    exact hRpos
  have hratio :
      (1 / 15 : Real) ≤
        shortestVectorLength (knDualLattice Λ) / coveringRadius (knDualLattice Λ) := by
    rw [hshort_dual]
    field_simp [hRdual_pos.ne']
    exact hcover_dual
  have hconstant :
      khotNaorFinalConstant ≤
        khotNaorAnalyticConstant *
          (shortestVectorLength (knDualLattice Λ) / coveringRadius (knDualLattice Λ)) := by
    calc
      khotNaorFinalConstant = khotNaorAnalyticConstant * (1 / 15 : Real) := by
        unfold khotNaorFinalConstant khotNaorAnalyticConstant
        field_simp [Real.exp_ne_zero]
        ring
      _ ≤ khotNaorAnalyticConstant *
            (shortestVectorLength (knDualLattice Λ) / coveringRadius (knDualLattice Λ)) :=
          mul_le_mul_of_nonneg_left hratio khotNaorAnalyticConstant_pos.le
  have hreal :
      khotNaorFinalConstant * Real.sqrt ((q * q : Nat) : Real) ≤
        khotNaorAnalyticConstant *
          (shortestVectorLength (knDualLattice Λ) / coveringRadius (knDualLattice Λ)) *
            Real.sqrt ((q * q : Nat) : Real) :=
    mul_le_mul_of_nonneg_right hconstant (Real.sqrt_nonneg _)
  exact le_trans (ENNReal.ofReal_le_ofReal hreal) (by
    simpa [Λ, KNFullRankLattice.torus, KNFullRankLattice.torusMetric] using hdual)

/-- The Khot--Naor lower bound for Hilbert distortion of flat tori. -/
theorem khotNaorFlatTorusLowerBound :
    exists c : Real, 0 < c /\
      forall N : Nat, exists n : Nat, N <= n /\
        exists A : LatticeBasis n,
          ENNReal.ofReal (c * Real.sqrt (n : Real)) <=
            (letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A;
              hilbertDistortion (flatTorus n A)) := by
  exact khotNaorProjectForm

/-- The unit-lattice torus model is isometric to the corresponding lattice quotient. -/
theorem flatTorusUnitLatticeIsometry (n : Nat) (A : LatticeBasis n) :
    (letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A;
      letI : PseudoMetricSpace (flatTorusEuclideanLatticeQuotient n A) :=
        flatTorusEuclideanLatticeMetric n A;
      exists e : Equiv (flatTorus n A) (flatTorusEuclideanLatticeQuotient n A),
        Isometry e) := by
  exact flatTorusUnitLatticeIsometry_aux n A

end

end SphereObstructionHilbertShiftQuotient
