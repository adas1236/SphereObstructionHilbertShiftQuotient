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

@[reducible]
private noncomputable def flatTorusAmbientSeminorm
    (n : Nat) (A : LatticeBasis n) : SeminormedAddCommGroup (RealEuclideanSpace n) :=
  SeminormedAddCommGroup.induced (RealEuclideanSpace n) (RealEuclideanSpace n)
    (Matrix.toEuclideanLin A.matrix)

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

end

end SphereObstructionHilbertShiftQuotient
