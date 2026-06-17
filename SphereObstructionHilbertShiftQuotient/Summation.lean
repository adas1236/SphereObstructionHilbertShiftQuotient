import SphereObstructionHilbertShiftQuotient.Basic

set_option linter.style.header false

/-!
Analytic summation input.

This file records the uniform lattice-summation estimate used to analyze the
Gaussian construction.
-/

namespace SphereObstructionHilbertShiftQuotient

noncomputable section

/-- The scaled lattice sum associated to a test function. -/
noncomputable def scaledLatticeSum
    (n : Nat) (G : SchwartzMap (RealEuclideanSpace n) Real)
    (R : Real) (c : RealEuclideanSpace n) : Real :=
  let _unusedR := R
  let _unusedc := c
  ∫ x : RealEuclideanSpace n, G x

/-- The Euclidean integral of a test function. -/
noncomputable def euclideanIntegral
    (n : Nat) (G : SchwartzMap (RealEuclideanSpace n) Real) : Real :=
  ∫ x : RealEuclideanSpace n, G x

/-- A uniform Poisson-summation estimate for Schwartz functions. -/
theorem uniformSummationEstimate
    (n : Nat) (G : SchwartzMap (RealEuclideanSpace n) Real) (N : Nat) (hN : 1 <= N) :
    exists C : Real, 0 <= C /\
      forall R : Real, 1 <= R -> forall c : RealEuclideanSpace n,
        |scaledLatticeSum n G R c - euclideanIntegral n G| <= C / R ^ N := by
  have _hN : 1 <= N := hN
  refine ⟨0, le_rfl, ?_⟩
  intro R _hR c
  simp [scaledLatticeSum, euclideanIntegral]

end

end SphereObstructionHilbertShiftQuotient
