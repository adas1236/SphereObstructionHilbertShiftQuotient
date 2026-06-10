import SphereObstructionHilbertShiftQuotient.Distortion

set_option linter.style.header false

/-!
Flat torus inputs.

This file names the flat tori with unit lattice, their metric, and the
Khot--Naor lower-bound input used in the main obstruction.
-/

namespace SphereObstructionHilbertShiftQuotient

noncomputable section

/-- An invertible real matrix used as a lattice basis for the flat torus metric. -/
structure LatticeBasis (n : Nat) where
  /-- The matrix whose columns encode the lattice basis. -/
  matrix : Matrix (Fin n) (Fin n) Real
  /-- The lattice basis matrix has invertible determinant. -/
  invertible : IsUnit matrix.det

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

/-- The flat quotient metric on `R^n / Z^n` with matrix `A`. -/
@[reducible]
noncomputable def flatTorusMetric
    (n : Nat) (A : LatticeBasis n) : PseudoMetricSpace (flatTorus n A) := by
  letI : SeminormedAddCommGroup (RealEuclideanSpace n) :=
    SeminormedAddCommGroup.induced (RealEuclideanSpace n) (RealEuclideanSpace n)
      (Matrix.toEuclideanLin A.matrix)
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

/-- The Khot--Naor lower bound for Hilbert distortion of flat tori. -/
theorem khotNaorFlatTorusLowerBound :
    exists c : Real, 0 < c /\
      forall N : Nat, exists n : Nat, N <= n /\
        exists A : LatticeBasis n,
          ENNReal.ofReal (c * Real.sqrt (n : Real)) <=
            (letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A;
              hilbertDistortion (flatTorus n A)) := by
  sorry

/-- The unit-lattice torus model is isometric to the corresponding lattice quotient. -/
theorem flatTorusUnitLatticeIsometry (n : Nat) (A : LatticeBasis n) :
    (letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A;
      letI : PseudoMetricSpace (flatTorusEuclideanLatticeQuotient n A) :=
        flatTorusEuclideanLatticeMetric n A;
      exists e : Equiv (flatTorus n A) (flatTorusEuclideanLatticeQuotient n A),
        Isometry e) := by
  sorry

end

end SphereObstructionHilbertShiftQuotient
