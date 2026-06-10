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

private noncomputable def encodedShiftFunction
    (n M : Nat) (x : finitelySupportedHigherRankPoint n) : Int -> Real := by
  classical
  exact fun r =>
    if h : ∃ k : Fin n -> Int, k ∈ x.2.1 ∧ mixedRadixMap n M k = r then
      ((x.1 : codingHigherRankL2Space n) (Classical.choose h))
    else
      0

/-- One-dimensional shift representative obtained by mixed-radix coding. -/
noncomputable def encodedShiftRepresentative
    (n M : Nat) : finitelySupportedHigherRankPoint n -> shiftHilbertSphere := by
  classical
  exact fun x =>
    let raw : Int -> Real := encodedShiftFunction n M x
    if h : ∃ hmem : Memℓp raw (2 : ℝ≥0∞), (⟨raw, hmem⟩ : codingShiftL2Space) ≠ 0 then
      normalizedShiftL2Vector ⟨raw, Classical.choose h⟩ (Classical.choose_spec h)
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
  sorry

/-- Exact coding preserves the finite set of correlations for finitely supported data. -/
theorem codingPreservesCorrelations
    (n M L : Nat) (F : Finset (finitelySupportedHigherRankPoint n))
    (hM : 2 * L + 1 < M)
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
  sorry

/-- Quotient distance is Lipschitz under changing Hilbert-sphere representatives. -/
theorem quotientDistanceLipschitzRepresentatives
    (n : Nat) (x y x' y' : higherRankHilbertSphere n) :
    (letI : PseudoMetricSpace (higherRankSphereQuotient n) := higherRankChordalMetric n;
      |dist (higherRankQuotientMk n x) (higherRankQuotientMk n y) -
          dist (higherRankQuotientMk n x') (higherRankQuotientMk n y')| <=
        higherRankRepresentativeNorm n x x' + higherRankRepresentativeNorm n y y') := by
  sorry

/-- Finite subsets of a higher-rank quotient may be approximated by finitely supported data. -/
theorem finiteSupportApproximationInQuotient
    (n : Nat) (F : Finset (higherRankSphereQuotient n)) (eps : Real) (heps : 0 < eps) :
    (letI : PseudoMetricSpace (higherRankSphereQuotient n) := higherRankChordalMetric n;
      exists G : Finset (higherRankSphereQuotient n),
        (forall y, y ∈ G ->
          exists z : finitelySupportedHigherRankPoint n,
            higherRankQuotientMk n (finitelySupportedHigherRankRepresentative n z) = y) /\
          FiniteMetricApproximation F G (1 + eps)) := by
  sorry

/-- Every finite subset of a higher-rank quotient embeds into the shift quotient. -/
theorem higherRankFiniteSubsetEmbedsInShiftQuotient
    (n : Nat) (F : Finset (higherRankSphereQuotient n)) (eps : Real) (heps : 0 < eps) :
    (letI : PseudoMetricSpace (higherRankSphereQuotient n) := higherRankChordalMetric n;
      letI : PseudoMetricSpace shiftSphereQuotient := shiftChordalMetric;
      FiniteMetricEmbedsWithDistortion shiftSphereQuotient F (1 + eps)) := by
  sorry

end

end SphereObstructionHilbertShiftQuotient
