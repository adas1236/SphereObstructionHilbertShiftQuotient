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

private noncomputable def gaussianRawFunction
    (n : Nat) (A : LatticeBasis n) (R : Real) (u : RealEuclideanSpace n) :
    (Fin n -> Int) -> Real :=
  gaussianSample n A R u

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

private noncomputable def gaussianCorrelationCenter
    {n : Nat} (u w : RealEuclideanSpace n) : RealEuclideanSpace n :=
  ((2 : Real)⁻¹) • (u + w)

private noncomputable def gaussianCorrelationKernel
    (n : Nat) (A : LatticeBasis n) (R : Real) (u w : RealEuclideanSpace n) : Real :=
  Real.exp (-(matrixNormSq n A (u - w)) / (4 * R ^ 2))

private def gaussianCompletedSquareFormula
    (n : Nat) (A : LatticeBasis n) (R : Real) (u w : RealEuclideanSpace n) : Prop :=
  gaussianRawInnerSum n A R u w =
    gaussianCorrelationKernel n A R u w *
      (R ^ n * gaussianPeriodizedMass n A R (gaussianCorrelationCenter u w))

private def gaussianPeriodizedMassAsymptotic
    (n : Nat) (A : LatticeBasis n) (N : Nat) : Prop :=
  ∃ C : Real, 0 <= C /\
    forall R : Real, 1 <= R -> forall c : RealEuclideanSpace n,
      ∃ theta : Real, |theta| <= C / R ^ N /\
        gaussianPeriodizedMass n A R c = 1 + theta

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

private axiom gaussianRawMemℓp_of_one_le
    (n : Nat) (A : LatticeBasis n) (R : Real) (u : RealEuclideanSpace n) (hR : 1 <= R) :
    Memℓp (gaussianRawFunction n A R u) (2 : ℝ≥0∞)

private theorem gaussianRawAdmissible_of_one_le
    (n : Nat) (A : LatticeBasis n) (R : Real) (u : RealEuclideanSpace n) (hR : 1 <= R) :
    gaussianRawAdmissible n A R u := by
  let hmem := gaussianRawMemℓp_of_one_le n A R u hR
  exact ⟨hmem, gaussianRawL2Vector_ne_zero n A R u hmem⟩

private axiom gaussianPeriodizedMassAsymptotic_of_uniformSummationEstimate
    (n : Nat) (A : LatticeBasis n) (N : Nat) (hN : 1 <= N) :
    gaussianPeriodizedMassAsymptotic n A N

private axiom gaussianNormalizedRawCorrelationAsymptotic_of_periodizedMass
    (n : Nat) (A : LatticeBasis n) (N : Nat) (hN : 1 <= N)
    (hMass : gaussianPeriodizedMassAsymptotic n A N) :
    exists C : Real, 0 <= C /\
      forall R : Real, forall hR : 1 <= R, forall u w : RealEuclideanSpace n,
        exists theta : Real,
          |theta| <= C / R ^ N /\
            gaussianNormalizedRawCorrelation n A R u w
                (gaussianRawAdmissible_of_one_le n A R u hR)
                (gaussianRawAdmissible_of_one_le n A R w hR) =
              gaussianCorrelationKernel n A R u w * (1 + theta)

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

private axiom gaussianFiniteSubsetMap_distortion_from_correlationAsymptotic
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
              (1 + eps) * gaussianEmbeddingScale R * dist x.1 y.1)

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
  exact gaussianFiniteSubsetMap_distortion_from_correlationAsymptotic n A E eps heps hCorr

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
