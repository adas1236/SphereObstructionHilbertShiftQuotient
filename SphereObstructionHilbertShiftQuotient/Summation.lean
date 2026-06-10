import SphereObstructionHilbertShiftQuotient.Basic

set_option linter.style.header false

/-!
Analytic summation input.

This file records the uniform lattice-summation estimate used to analyze the
Gaussian construction.
-/

namespace SphereObstructionHilbertShiftQuotient

noncomputable section

private noncomputable def summationIntegerPoint
    (n : Nat) (k : Fin n -> Int) : RealEuclideanSpace n :=
  WithLp.toLp 2 (fun i : Fin n => (k i : Real))

/-- The scaled lattice sum associated to a test function. -/
noncomputable def scaledLatticeSum
    (n : Nat) (G : SchwartzMap (RealEuclideanSpace n) Real)
    (R : Real) (c : RealEuclideanSpace n) : Real :=
  (R ^ n)⁻¹ * ∑' k : Fin n -> Int,
    G ((R⁻¹ : Real) • (summationIntegerPoint n k - c))

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
  sorry

end

end SphereObstructionHilbertShiftQuotient
