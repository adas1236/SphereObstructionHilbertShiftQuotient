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

private noncomputable def gaussianSample
    (n : Nat) (A : LatticeBasis n) (R : Real) (u : RealEuclideanSpace n)
    (k : Fin n -> Int) : Real :=
  Real.exp (-(matrixNormSq n A ((R⁻¹ : Real) • (gaussianIntegerPoint n k - u)) / 2))

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

/-- The normalized Gaussian lattice vector, viewed as a point of the quotient. -/
noncomputable def gaussianLatticeVector
    (n : Nat) (A : LatticeBasis n) (R : Real) (u : RealEuclideanSpace n) :
    higherRankHilbertSphere n := by
  classical
  let raw : (Fin n -> Int) -> Real := gaussianSample n A R u
  exact
    if h : ∃ hmem : Memℓp raw (2 : ℝ≥0∞), (⟨raw, hmem⟩ : gaussianL2Space n) ≠ 0 then
      normalizedGaussianL2Vector n ⟨raw, Classical.choose h⟩ (Classical.choose_spec h)
    else
      defaultGaussianSphereVector n

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
  sorry

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
  sorry

end

end SphereObstructionHilbertShiftQuotient
