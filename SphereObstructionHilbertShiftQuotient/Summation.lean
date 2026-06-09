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
    (n : Nat) (G : SchwartzMap (EuclideanSpace n) Real)
    (R : Real) (c : EuclideanSpace n) : Real := by
  sorry

/-- The Euclidean integral of a test function. -/
noncomputable def euclideanIntegral
    (n : Nat) (G : SchwartzMap (EuclideanSpace n) Real) : Real := by
  sorry

/-- A uniform Poisson-summation estimate for Schwartz functions. -/
theorem uniformSummationEstimate
    (n : Nat) (G : SchwartzMap (EuclideanSpace n) Real) (N : Nat) (hN : 1 <= N) :
    exists C : Real, 0 <= C /\
      forall R : Real, 1 <= R -> forall c : EuclideanSpace n,
        |scaledLatticeSum n G R c - euclideanIntegral n G| <= C / R ^ N := by
  sorry

end

end SphereObstructionHilbertShiftQuotient
