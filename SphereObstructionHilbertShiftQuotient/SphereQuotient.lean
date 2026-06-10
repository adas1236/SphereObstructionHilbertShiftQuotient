import SphereObstructionHilbertShiftQuotient.Basic

set_option linter.style.header false
open scoped lp ENNReal

/-!
Sphere quotient models and their quotient metrics.

The declarations here name the one-dimensional shift quotient, the higher-rank
translation quotients, and the metric facts used by downstream files.
-/

namespace SphereObstructionHilbertShiftQuotient

noncomputable section

private abbrev l2Space (ι : Type*) : Type _ :=
  ↥(lp (fun (_ : ι) => Real) 2)

private noncomputable def reindexL2 {ι : Type*} (e : ι ≃ ι) (f : l2Space ι) :
    l2Space ι :=
  ⟨fun i => f (e i), by
    change Memℓp (fun i : ι => f (e i)) (2 : ℝ≥0∞)
    have hpos : 0 < (2 : ℝ≥0∞).toReal := by norm_num
    rw [memℓp_gen_iff hpos]
    have hf : Summable fun i : ι => ‖f i‖ ^ (2 : ℝ≥0∞).toReal :=
      (lp.memℓp f).summable hpos
    simpa [Function.comp_def] using
      (e.summable_iff (f := fun i : ι => ‖f i‖ ^ (2 : ℝ≥0∞).toReal)).mpr hf⟩

private lemma norm_reindexL2 {ι : Type*} (e : ι ≃ ι) (f : l2Space ι) :
    ‖reindexL2 e f‖ = ‖f‖ := by
  have hpos : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  apply Real.rpow_left_injOn hpos.ne' (lp.norm_nonneg' _) (lp.norm_nonneg' _)
  change ‖reindexL2 e f‖ ^ (2 : ℝ≥0∞).toReal = ‖f‖ ^ (2 : ℝ≥0∞).toReal
  rw [lp.norm_rpow_eq_tsum hpos, lp.norm_rpow_eq_tsum hpos]
  change (∑' i : ι, ‖f (e i)‖ ^ (2 : ℝ≥0∞).toReal) =
    ∑' i : ι, ‖f i‖ ^ (2 : ℝ≥0∞).toReal
  exact e.tsum_eq (fun i : ι => ‖f i‖ ^ (2 : ℝ≥0∞).toReal)

private lemma dist_reindexL2 {ι : Type*} (e : ι ≃ ι) (f g : l2Space ι) :
    dist (reindexL2 e f) (reindexL2 e g) = dist f g := by
  rw [dist_eq_norm, dist_eq_norm]
  have h : reindexL2 e f - reindexL2 e g = reindexL2 e (f - g) := by
    ext i
    rfl
  rw [h, norm_reindexL2]

private lemma angle_reindexL2 {ι : Type*} (e : ι ≃ ι) (f g : l2Space ι) :
    InnerProductGeometry.angle (reindexL2 e f) (reindexL2 e g) =
      InnerProductGeometry.angle f g := by
  rw [InnerProductGeometry.angle, InnerProductGeometry.angle]
  rw [norm_reindexL2, norm_reindexL2]
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  congr 2
  change (∑' i : ι, inner Real (f (e i)) (g (e i))) =
    ∑' i : ι, inner Real (f i) (g i)
  exact e.tsum_eq (fun i : ι => inner Real (f i) (g i))

private noncomputable def translationOnL2 {G : Type*} [AddCommGroup G] (a : G)
    (f : l2Space G) : l2Space G :=
  reindexL2 (Equiv.subRight a) f

private noncomputable def translationOnSphere {G : Type*} [AddCommGroup G] (a : G) :
    Metric.sphere (0 : l2Space G) 1 -> Metric.sphere (0 : l2Space G) 1 :=
  fun x => ⟨translationOnL2 a x, by
    rw [Metric.mem_sphere, dist_zero_right]
    rw [translationOnL2, norm_reindexL2]
    rw [← dist_zero_right (x : l2Space G)]
    exact x.2⟩

private lemma translationOnSphere_zero {G : Type*} [AddCommGroup G]
    (x : Metric.sphere (0 : l2Space G) 1) :
    translationOnSphere (0 : G) x = x := by
  ext i
  simp [translationOnSphere, translationOnL2, reindexL2]

private lemma translationOnSphere_add {G : Type*} [AddCommGroup G] (a b : G)
    (x : Metric.sphere (0 : l2Space G) 1) :
    translationOnSphere a (translationOnSphere b x) = translationOnSphere (a + b) x := by
  ext i
  simp [translationOnSphere, translationOnL2, reindexL2, sub_eq_add_neg, add_assoc, add_comm]

private lemma translationOnSphere_chordal_isometry {G : Type*} [AddCommGroup G] (a : G) :
    Isometry (translationOnSphere a :
      Metric.sphere (0 : l2Space G) 1 -> Metric.sphere (0 : l2Space G) 1) := by
  intro x y
  rw [edist_dist, edist_dist]
  change ENNReal.ofReal (dist (translationOnL2 a (x : l2Space G))
    (translationOnL2 a (y : l2Space G))) = ENNReal.ofReal (dist (x : l2Space G) y)
  rw [translationOnL2, translationOnL2, dist_reindexL2]

@[reducible]
private noncomputable def sphereAngularPseudoEMetricSpace {G : Type*} [AddCommGroup G] :
    PseudoEMetricSpace (Metric.sphere (0 : l2Space G) 1) :=
  PseudoEMetricSpace.ofEDist
    (fun x y => ENNReal.ofReal <| InnerProductGeometry.angle (x : l2Space G) y)
    (fun x => by
      have hxnorm : ‖(x : l2Space G)‖ = 1 := by
        rw [← dist_zero_right (x : l2Space G)]
        exact x.2
      have hxne : (x : l2Space G) ≠ 0 := by
        intro h
        rw [h, norm_zero] at hxnorm
        norm_num at hxnorm
      simp [InnerProductGeometry.angle_self hxne])
    (fun x y => by
      simp [InnerProductGeometry.angle_comm])
    (fun x y z => by
      rw [← ENNReal.ofReal_add
        (InnerProductGeometry.angle_nonneg (x : l2Space G) y)
        (InnerProductGeometry.angle_nonneg (y : l2Space G) z)]
      exact ENNReal.ofReal_le_ofReal <|
        InnerProductGeometry.angle_le_angle_add_angle (x : l2Space G) y z)

private lemma translationOnSphere_angular_isometry {G : Type*} [AddCommGroup G] (a : G) :
    (letI : PseudoEMetricSpace (Metric.sphere (0 : l2Space G) 1) :=
      sphereAngularPseudoEMetricSpace;
      Isometry (translationOnSphere a :
        Metric.sphere (0 : l2Space G) 1 -> Metric.sphere (0 : l2Space G) 1)) := by
  intro x y
  change ENNReal.ofReal
      (InnerProductGeometry.angle (translationOnL2 a (x : l2Space G))
        (translationOnL2 a (y : l2Space G))) =
    ENNReal.ofReal (InnerProductGeometry.angle (x : l2Space G) y)
  rw [translationOnL2, translationOnL2, angle_reindexL2]

@[reducible]
private def translationOrbitSetoid {G : Type*} [AddCommGroup G] :
    Setoid (Metric.sphere (0 : l2Space G) 1) where
  r x y := exists a : G, y = translationOnSphere a x
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact ⟨0, (translationOnSphere_zero x).symm⟩
    · intro x y hxy
      rcases hxy with ⟨a, rfl⟩
      refine ⟨-a, ?_⟩
      rw [translationOnSphere_add, neg_add_cancel, translationOnSphere_zero]
    · intro x y z hxy hyz
      rcases hxy with ⟨a, rfl⟩
      rcases hyz with ⟨b, rfl⟩
      exact ⟨b + a, translationOnSphere_add b a x⟩

@[reducible]
private noncomputable def orbitQuotientPseudoEMetricSpace
    {G X : Type*} [AddCommGroup G] [PseudoEMetricSpace X]
    (T : G -> X -> X) (rel : Setoid X)
    (hzero : forall x : X, T 0 x = x)
    (hadd : forall a b : G, forall x : X, T a (T b x) = T (a + b) x)
    (hiso : forall a : G, Isometry (T a)) : PseudoEMetricSpace (Quotient rel) :=
  PseudoEMetricSpace.ofEDist
    (fun x y => ⨅ a : G, edist (Quotient.out x) (T a (Quotient.out y)))
    (fun x => by
      refine le_antisymm ?_ bot_le
      simpa [hzero] using
        (iInf_le (fun a : G => edist (Quotient.out x) (T a (Quotient.out x))) 0))
    (fun x y => by
      calc
        (⨅ a : G, edist (Quotient.out x) (T a (Quotient.out y))) =
            ⨅ a : G, edist (Quotient.out y) (T (-a) (Quotient.out x)) := by
          congr with a
          rw [← (hiso (-a)).edist_eq (Quotient.out x) (T a (Quotient.out y))]
          rw [hadd, neg_add_cancel, hzero, edist_comm]
        _ = ⨅ a : G, edist (Quotient.out y) (T a (Quotient.out x)) := by
          simpa using
            (Equiv.neg G).iInf_comp
              (g := fun a : G => edist (Quotient.out y) (T a (Quotient.out x))))
    (fun x y z => by
      let ox := Quotient.out x
      let oy := Quotient.out y
      let oz := Quotient.out z
      let f : G × G -> ENNReal := fun p => edist ox (T p.1 oy)
      let g : G × G -> ENNReal := fun p => edist oy (T p.2 oz)
      have hfst : Function.Surjective (fun p : G × G => p.1) := fun a => ⟨(a, 0), rfl⟩
      have hsnd : Function.Surjective (fun p : G × G => p.2) := fun a => ⟨(0, a), rfl⟩
      calc
        (⨅ a : G, edist ox (T a oz)) <= ⨅ p : G × G, f p + g p := by
          refine le_iInf fun p => ?_
          refine le_trans (iInf_le (fun a : G => edist ox (T a oz)) (p.1 + p.2)) ?_
          have hdist : edist (T p.1 oy) (T (p.1 + p.2) oz) = edist oy (T p.2 oz) := by
            rw [← (hiso (-p.1)).edist_eq (T p.1 oy) (T (p.1 + p.2) oz)]
            rw [hadd, neg_add_cancel, hzero, hadd]
            congr 1
            abel_nf
          simpa [f, g, hdist] using edist_triangle ox (T p.1 oy) (T (p.1 + p.2) oz)
        _ = (⨅ p : G × G, f p) + (⨅ p : G × G, g p) := by
          refine (ENNReal.iInf_add_iInf ?_).symm
          intro p q
          exact ⟨(p.1, q.2), le_rfl⟩
        _ = (⨅ a : G, edist ox (T a oy)) + (⨅ a : G, edist oy (T a oz)) := by
          rw [hfst.iInf_comp (fun a : G => edist ox (T a oy)),
            hsnd.iInf_comp (fun a : G => edist oy (T a oz))])

@[reducible]
private noncomputable def orbitQuotientPseudoMetricSpace
    {G X : Type*} [AddCommGroup G] [PseudoEMetricSpace X]
    (T : G -> X -> X) (rel : Setoid X)
    (hzero : forall x : X, T 0 x = x)
    (hadd : forall a b : G, forall x : X, T a (T b x) = T (a + b) x)
    (hiso : forall a : G, Isometry (T a))
    (hfinite : forall x y : X, edist x y ≠ ⊤) : PseudoMetricSpace (Quotient rel) := by
  letI : PseudoEMetricSpace (Quotient rel) :=
    orbitQuotientPseudoEMetricSpace T rel hzero hadd hiso
  exact PseudoEMetricSpace.toPseudoMetricSpace fun x y => by
    refine ne_top_of_le_ne_top (hfinite (Quotient.out x) (T 0 (Quotient.out y))) ?_
    exact iInf_le (fun a : G => edist (Quotient.out x) (T a (Quotient.out y))) 0

/-- The unit sphere in the real Hilbert space `l2 Int`, before quotienting by shifts. -/
@[reducible]
noncomputable def shiftHilbertSphere : Type :=
  Metric.sphere (0 : l2Space Int) 1

/-- The metric topology on the shift Hilbert sphere. -/
@[reducible]
noncomputable def shiftHilbertSphereMetric : PseudoMetricSpace shiftHilbertSphere :=
  inferInstance

/-- The bilateral shift action on the Hilbert sphere. -/
noncomputable def shiftAction (k : Int) : shiftHilbertSphere -> shiftHilbertSphere :=
  translationOnSphere k

/-- The orbit of a unit vector under all integer shifts. -/
noncomputable def shiftOrbit (x : shiftHilbertSphere) : Set shiftHilbertSphere :=
  Set.range fun k : Int => shiftAction k x

/-- Hilbert-space distance between shift-sphere representatives. -/
noncomputable def shiftRepresentativeNorm
    (x y : shiftHilbertSphere) : Real :=
  ‖(x : l2Space Int) - (y : l2Space Int)‖

/-- Hilbert-space inner product between shift-sphere representatives. -/
noncomputable def shiftRepresentativeInner
    (x y : shiftHilbertSphere) : Real :=
  inner Real (x : l2Space Int) (y : l2Space Int)

private lemma shiftAction_zero (x : shiftHilbertSphere) : shiftAction 0 x = x :=
  translationOnSphere_zero x

private lemma shiftAction_add (a b : Int) (x : shiftHilbertSphere) :
    shiftAction a (shiftAction b x) = shiftAction (a + b) x :=
  translationOnSphere_add a b x

private lemma shiftAction_chordal_isometry (a : Int) :
    Isometry (shiftAction a) :=
  translationOnSphere_chordal_isometry a

private lemma shiftAction_angular_isometry (a : Int) :
    (letI : PseudoEMetricSpace shiftHilbertSphere := sphereAngularPseudoEMetricSpace;
      Isometry (shiftAction a)) :=
  translationOnSphere_angular_isometry a

/-- The quotient of the unit sphere of `l2 Int` by the bilateral shift. -/
noncomputable def shiftSphereQuotient : Type :=
  Quotient (translationOrbitSetoid (G := Int))

/-- The quotient map from the shift Hilbert sphere to the shift quotient. -/
noncomputable def shiftQuotientMk : shiftHilbertSphere -> shiftSphereQuotient :=
  Quotient.mk (translationOrbitSetoid (G := Int))

/-- The chordal quotient metric on the shift sphere quotient. -/
@[reducible]
noncomputable def shiftChordalMetric : PseudoMetricSpace shiftSphereQuotient :=
  orbitQuotientPseudoMetricSpace shiftAction (translationOrbitSetoid (G := Int))
    shiftAction_zero shiftAction_add shiftAction_chordal_isometry
    (fun x y => (edist_lt_top x y).ne)

/-- The angular quotient metric on the shift sphere quotient. -/
@[reducible]
noncomputable def shiftAngularMetric : PseudoMetricSpace shiftSphereQuotient := by
  letI : PseudoEMetricSpace shiftHilbertSphere := sphereAngularPseudoEMetricSpace
  exact orbitQuotientPseudoMetricSpace shiftAction (translationOrbitSetoid (G := Int))
    shiftAction_zero shiftAction_add shiftAction_angular_isometry
    (fun x y => by
      change ENNReal.ofReal (InnerProductGeometry.angle (x : l2Space Int) y) ≠ ⊤
      exact ENNReal.ofReal_ne_top)

/-- Shift orbits on the Hilbert sphere are closed. -/
theorem shiftOrbitsClosed (x : shiftHilbertSphere) :
    (letI : PseudoMetricSpace shiftHilbertSphere := shiftHilbertSphereMetric;
      IsClosed (shiftOrbit x)) := by
  sorry

/-- The chordal and angular quotient metrics are bilipschitz equivalent. -/
theorem chordalAngularMetricEquivalence :
    forall x y : shiftSphereQuotient,
      shiftChordalMetric.dist x y = 2 * Real.sin (shiftAngularMetric.dist x y / 2) /\
        (2 / Real.pi) * shiftAngularMetric.dist x y <= shiftChordalMetric.dist x y /\
          shiftChordalMetric.dist x y <= shiftAngularMetric.dist x y := by
  sorry

/-- The unit sphere in `l2 (Fin n -> Int)`, before quotienting by translations. -/
@[reducible]
noncomputable def higherRankHilbertSphere (n : Nat) : Type :=
  Metric.sphere (0 : l2Space (Fin n -> Int)) 1

/-- The metric topology on the higher-rank Hilbert sphere. -/
@[reducible]
noncomputable def higherRankHilbertSphereMetric
    (n : Nat) : PseudoMetricSpace (higherRankHilbertSphere n) :=
  inferInstance

/-- Translation by an element of `Z^n` on the higher-rank Hilbert sphere. -/
noncomputable def higherRankTranslation
    (n : Nat) (a : Fin n -> Int) : higherRankHilbertSphere n -> higherRankHilbertSphere n :=
  translationOnSphere a

/-- The translation orbit of a higher-rank unit vector. -/
noncomputable def higherRankOrbit
    (n : Nat) (x : higherRankHilbertSphere n) : Set (higherRankHilbertSphere n) :=
  Set.range fun a : Fin n -> Int => higherRankTranslation n a x

/-- Hilbert-space distance between higher-rank representatives. -/
noncomputable def higherRankRepresentativeNorm
    (n : Nat) (x y : higherRankHilbertSphere n) : Real :=
  ‖(x : l2Space (Fin n -> Int)) - (y : l2Space (Fin n -> Int))‖

/-- Hilbert-space inner product between higher-rank representatives. -/
noncomputable def higherRankRepresentativeInner
    (n : Nat) (x y : higherRankHilbertSphere n) : Real :=
  inner Real (x : l2Space (Fin n -> Int)) (y : l2Space (Fin n -> Int))

private lemma higherRankTranslation_zero (n : Nat) (x : higherRankHilbertSphere n) :
    higherRankTranslation n 0 x = x :=
  translationOnSphere_zero x

private lemma higherRankTranslation_add (n : Nat) (a b : Fin n -> Int)
    (x : higherRankHilbertSphere n) :
    higherRankTranslation n a (higherRankTranslation n b x) =
      higherRankTranslation n (a + b) x :=
  translationOnSphere_add a b x

private lemma higherRankTranslation_chordal_isometry (n : Nat) (a : Fin n -> Int) :
    Isometry (higherRankTranslation n a) :=
  translationOnSphere_chordal_isometry a

/-- The quotient of the unit sphere of `l2 (Fin n -> Int)` by translations. -/
noncomputable def higherRankSphereQuotient (n : Nat) : Type :=
  Quotient (translationOrbitSetoid (G := Fin n -> Int))

/-- The quotient map from representatives to the higher-rank sphere quotient. -/
noncomputable def higherRankQuotientMk
    (n : Nat) : higherRankHilbertSphere n -> higherRankSphereQuotient n :=
  Quotient.mk (translationOrbitSetoid (G := Fin n -> Int))

/-- The chordal quotient metric on the higher-rank sphere quotient. -/
@[reducible]
noncomputable def higherRankChordalMetric
    (n : Nat) : PseudoMetricSpace (higherRankSphereQuotient n) :=
  orbitQuotientPseudoMetricSpace (higherRankTranslation n)
    (translationOrbitSetoid (G := Fin n -> Int))
    (higherRankTranslation_zero n) (higherRankTranslation_add n)
    (higherRankTranslation_chordal_isometry n) (fun x y => (edist_lt_top x y).ne)

/-- The set of translated representative correlations. -/
noncomputable def higherRankCorrelationSet
    (n : Nat) (f g : higherRankHilbertSphere n) : Set Real :=
  Set.range fun a : Fin n -> Int =>
    higherRankRepresentativeInner n f (higherRankTranslation n a g)

/-- The supremum of translated representative correlations. -/
noncomputable def higherRankCorrelationSupFromRepresentatives
    (n : Nat) (f g : higherRankHilbertSphere n) : Real :=
  sSup (higherRankCorrelationSet n f g)

/-- The supremal translation correlation appearing in the quotient distance formula. -/
noncomputable def higherRankCorrelationSup
    (n : Nat) (x y : higherRankSphereQuotient n) : Real :=
  higherRankCorrelationSupFromRepresentatives n (Quotient.out x) (Quotient.out y)

/-- Translation orbits on the higher-rank Hilbert sphere are closed. -/
theorem higherRankTranslationOrbitsClosed (n : Nat) (x : higherRankHilbertSphere n) :
    (letI : PseudoMetricSpace (higherRankHilbertSphere n) := higherRankHilbertSphereMetric n;
      IsClosed (higherRankOrbit n x)) := by
  sorry

/-- The quotient distance is determined by translated representative correlations. -/
theorem higherRankCorrelationFormula (n : Nat) (f g : higherRankHilbertSphere n) :
    (letI : PseudoMetricSpace (higherRankSphereQuotient n) := higherRankChordalMetric n;
      dist (higherRankQuotientMk n f) (higherRankQuotientMk n g) ^ 2 =
        2 - 2 * higherRankCorrelationSupFromRepresentatives n f g) := by
  sorry

end

end SphereObstructionHilbertShiftQuotient
