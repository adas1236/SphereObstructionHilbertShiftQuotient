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

private lemma l2_large_coordinates_finite {ι : Type*} (f : l2Space ι) {ε : Real}
    (hε : 0 < ε) :
    {i : ι | ε <= ‖f i‖}.Finite := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  have hsumm : Summable fun i : ι => ‖f i‖ ^ (2 : ℝ≥0∞).toReal :=
    (lp.memℓp f).summable hp
  have hεpow : 0 < ε ^ (2 : ℝ≥0∞).toReal :=
    Real.rpow_pos_of_pos hε _
  have hfinite :
      {i : ι | ε ^ (2 : ℝ≥0∞).toReal <= ‖f i‖ ^ (2 : ℝ≥0∞).toReal}.Finite := by
    simpa [not_lt] using hsumm.tendsto_cofinite_zero.eventually_lt_const hεpow
  exact hfinite.subset fun i hi =>
    Real.rpow_le_rpow (le_of_lt hε) hi hp.le

private lemma exists_nonzero_coordinate {ι : Type*} (f : l2Space ι) (hf : f ≠ 0) :
    ∃ i : ι, f i ≠ 0 := by
  by_contra h
  apply hf
  ext i
  by_contra hi
  exact h ⟨i, hi⟩

private theorem translationOrbitClosed {G : Type*} [AddCommGroup G]
    (x : Metric.sphere (0 : l2Space G) 1) :
    IsClosed (Set.range fun a : G => translationOnSphere a x) := by
  classical
  refine isClosed_of_closure_subset ?_
  intro y hy
  have hynorm : ‖(y : l2Space G)‖ = 1 := by
    rw [← dist_zero_right (y : l2Space G)]
    exact y.2
  have hyne : (y : l2Space G) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hynorm
    norm_num at hynorm
  obtain ⟨i₀, hi₀⟩ := exists_nonzero_coordinate (y : l2Space G) hyne
  let δ : Real := ‖(y : l2Space G) i₀‖ / 2
  have hδ : 0 < δ := half_pos (norm_pos_iff.mpr hi₀)
  let large : Set G := {j : G | δ <= ‖(x : l2Space G) j‖}
  let nearTranslations : Set G := (fun j : G => i₀ - j) '' large
  let nearOrbit : Set (Metric.sphere (0 : l2Space G) 1) :=
    (fun a : G => translationOnSphere a x) '' nearTranslations
  have hnear_closed : IsClosed nearOrbit := by
    exact ((l2_large_coordinates_finite (x : l2Space G) hδ).image _).image
      (fun a : G => translationOnSphere a x) |>.isClosed
  have hy_near_closure : y ∈ closure nearOrbit := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hmin : 0 < min ε δ := lt_min hε hδ
    rcases (Metric.mem_closure_iff.mp hy (min ε δ) hmin) with
      ⟨z, hz, hzy⟩
    rcases hz with ⟨a, rfl⟩
    have hdistδ : dist y (translationOnSphere a x) < δ :=
      lt_of_lt_of_le hzy (min_le_right ε δ)
    have hnormδ :
        ‖(y : l2Space G) - translationOnL2 a (x : l2Space G)‖ < δ := by
      change dist (y : l2Space G) (translationOnL2 a (x : l2Space G)) < δ at hdistδ
      simpa [dist_eq_norm] using hdistδ
    have hcoord :
        ‖(y : l2Space G) i₀ - (x : l2Space G) (i₀ - a)‖ < δ := by
      calc
        ‖(y : l2Space G) i₀ - (x : l2Space G) (i₀ - a)‖ =
            ‖((y : l2Space G) - translationOnL2 a (x : l2Space G)) i₀‖ := by
          rfl
        _ <= ‖(y : l2Space G) - translationOnL2 a (x : l2Space G)‖ := by
          exact lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
            ((y : l2Space G) - translationOnL2 a (x : l2Space G)) i₀
        _ < δ := hnormδ
    have htri :
        ‖(y : l2Space G) i₀‖ <=
          ‖(y : l2Space G) i₀ - (x : l2Space G) (i₀ - a)‖ +
            ‖(x : l2Space G) (i₀ - a)‖ := by
      simpa [sub_eq_add_neg, add_assoc] using
        norm_add_le ((y : l2Space G) i₀ - (x : l2Space G) (i₀ - a))
          ((x : l2Space G) (i₀ - a))
    have hlarge : δ <= ‖(x : l2Space G) (i₀ - a)‖ := by
      have hδeq : ‖(y : l2Space G) i₀‖ = 2 * δ := by
        dsimp [δ]
        ring
      linarith
    have ha_near : a ∈ nearTranslations := by
      refine ⟨i₀ - a, hlarge, ?_⟩
      abel_nf
    refine ⟨translationOnSphere a x, ?_, lt_of_lt_of_le hzy (min_le_left ε δ)⟩
    exact ⟨a, ha_near, rfl⟩
  have hy_near : y ∈ nearOrbit := by
    simpa [hnear_closed.closure_eq] using hy_near_closure
  rcases hy_near with ⟨a, _ha, rfl⟩
  exact ⟨a, rfl⟩

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
  exact translationOrbitClosed x

private lemma unit_norm_sub_eq_two_sin_half_angle
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]
    (x y : V) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖x - y‖ = 2 * Real.sin (InnerProductGeometry.angle x y / 2) := by
  have hcos : inner Real x y = Real.cos (InnerProductGeometry.angle x y) := by
    rw [← InnerProductGeometry.cos_angle_mul_norm_mul_norm x y]
    rw [hx, hy]
    ring
  have hsq : ‖x - y‖ ^ 2 = (2 * Real.sin (InnerProductGeometry.angle x y / 2)) ^ 2 := by
    rw [norm_sub_sq_real, hcos, hx, hy]
    ring_nf
    rw [Real.sin_sq_eq_half_sub]
    ring_nf
  have hsin_nonneg : 0 ≤ Real.sin (InnerProductGeometry.angle x y / 2) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith [InnerProductGeometry.angle_nonneg x y]
    · linarith [InnerProductGeometry.angle_le_pi x y, Real.pi_pos]
  have hrhs_nonneg : 0 ≤ 2 * Real.sin (InnerProductGeometry.angle x y / 2) := by
    positivity
  have habs :=
    (sq_eq_sq_iff_abs_eq_abs (‖x - y‖)
      (2 * Real.sin (InnerProductGeometry.angle x y / 2))).mp hsq
  simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hrhs_nonneg] using habs

private lemma two_sin_half_monotoneOn :
    MonotoneOn (fun t : Real => 2 * Real.sin (t / 2)) (Set.Icc 0 Real.pi) := by
  intro u hu v hv huv
  have hu' : u / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [hu.1, hu.2, Real.pi_pos]
  have hv' : v / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [hv.1, hv.2, Real.pi_pos]
  have hsin := Real.strictMonoOn_sin.monotoneOn hu' hv' (by linarith)
  nlinarith

private lemma iInf_two_sin_half_eq {ι : Type*} [Nonempty ι] (θ : ι -> Real)
    (hθ0 : forall i, 0 <= θ i) (hθπ : forall i, θ i <= Real.pi) :
    (⨅ i, 2 * Real.sin (θ i / 2)) = 2 * Real.sin ((⨅ i, θ i) / 2) := by
  let φ : Real -> Real := fun t => 2 * Real.sin (t / 2)
  let A : Set Real := Set.range θ
  have hA_nonempty : A.Nonempty := Set.range_nonempty θ
  have hA_bdd : BddBelow A := by
    refine ⟨0, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact hθ0 i
  have hA_subset : A ⊆ Set.Icc 0 Real.pi := by
    rintro _ ⟨i, rfl⟩
    exact ⟨hθ0 i, hθπ i⟩
  have hmonoA : MonotoneOn φ A := two_sin_half_monotoneOn.mono hA_subset
  have hcont : ContinuousAt φ (sInf A) := by
    exact (continuous_const.mul
      (Real.continuous_sin.comp (continuous_id.div_const 2))).continuousAt
  have hmap := MonotoneOn.map_csInf_of_continuousWithinAt hcont.continuousWithinAt hmonoA
    hA_nonempty hA_bdd
  have hrange : Set.range (fun i => φ (θ i)) = φ '' A := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨θ i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨t, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  change sInf (Set.range (fun i => φ (θ i))) = φ (sInf (Set.range θ))
  rw [hrange]
  exact hmap.symm

private lemma two_div_pi_mul_le_two_sin_half {t : Real} (h0 : 0 <= t) (hπ : t <= Real.pi) :
    (2 / Real.pi) * t <= 2 * Real.sin (t / 2) := by
  have hsin := Real.mul_le_sin (x := t / 2) (by linarith) (by linarith)
  nlinarith [Real.pi_pos]

private lemma two_sin_half_le_self {t : Real} (h0 : 0 <= t) :
    2 * Real.sin (t / 2) <= t := by
  have hsin := Real.sin_le (x := t / 2) (by linarith)
  nlinarith

/-- The chordal and angular quotient metrics are bilipschitz equivalent. -/
theorem chordalAngularMetricEquivalence :
    forall x y : shiftSphereQuotient,
      shiftChordalMetric.dist x y = 2 * Real.sin (shiftAngularMetric.dist x y / 2) /\
        (2 / Real.pi) * shiftAngularMetric.dist x y <= shiftChordalMetric.dist x y /\
          shiftChordalMetric.dist x y <= shiftAngularMetric.dist x y := by
  intro x y
  let θ : Int -> Real := fun a =>
    InnerProductGeometry.angle ((Quotient.out x : shiftHilbertSphere) : l2Space Int)
      ((shiftAction a (Quotient.out y) : shiftHilbertSphere) : l2Space Int)
  have hθ0 : forall a, 0 <= θ a := by
    intro a
    exact InnerProductGeometry.angle_nonneg _ _
  have hθπ : forall a, θ a <= Real.pi := by
    intro a
    exact InnerProductGeometry.angle_le_pi _ _
  have hangular :
      shiftAngularMetric.dist x y = ⨅ a : Int, θ a := by
    dsimp [shiftAngularMetric, orbitQuotientPseudoMetricSpace,
      orbitQuotientPseudoEMetricSpace, PseudoEMetricSpace.toPseudoMetricSpace,
      PseudoEMetricSpace.toPseudoMetricSpaceOfDist, θ]
    change (⨅ a : Int, ENNReal.ofReal (InnerProductGeometry.angle
      ((Quotient.out x : shiftHilbertSphere) : l2Space Int)
      ((shiftAction a (Quotient.out y) : shiftHilbertSphere) : l2Space Int))).toReal =
        ⨅ a : Int, InnerProductGeometry.angle
          ((Quotient.out x : shiftHilbertSphere) : l2Space Int)
          ((shiftAction a (Quotient.out y) : shiftHilbertSphere) : l2Space Int)
    rw [ENNReal.toReal_iInf]
    · simp [ENNReal.toReal_ofReal, InnerProductGeometry.angle_nonneg]
    · intro a
      exact ENNReal.ofReal_ne_top
  have hchordal :
      shiftChordalMetric.dist x y = ⨅ a : Int, 2 * Real.sin (θ a / 2) := by
    dsimp [shiftChordalMetric, orbitQuotientPseudoMetricSpace,
      orbitQuotientPseudoEMetricSpace, PseudoEMetricSpace.toPseudoMetricSpace,
      PseudoEMetricSpace.toPseudoMetricSpaceOfDist, θ]
    change (⨅ a : Int, edist (Quotient.out x) (shiftAction a (Quotient.out y))).toReal =
      ⨅ a : Int, 2 * Real.sin (InnerProductGeometry.angle
        ((Quotient.out x : shiftHilbertSphere) : l2Space Int)
        ((shiftAction a (Quotient.out y) : shiftHilbertSphere) : l2Space Int) / 2)
    rw [ENNReal.toReal_iInf]
    · congr with a
      rw [edist_dist]
      have hxnorm : ‖((Quotient.out x : shiftHilbertSphere) : l2Space Int)‖ = 1 := by
        rw [← dist_zero_right (((Quotient.out x : shiftHilbertSphere) : l2Space Int))]
        exact (Quotient.out x : shiftHilbertSphere).2
      have hynorm :
          ‖((shiftAction a (Quotient.out y) : shiftHilbertSphere) : l2Space Int)‖ = 1 := by
        rw [← dist_zero_right
          (((shiftAction a (Quotient.out y) : shiftHilbertSphere) : l2Space Int))]
        exact (shiftAction a (Quotient.out y) : shiftHilbertSphere).2
      rw [ENNReal.toReal_ofReal]
      · rw [Subtype.dist_eq, dist_eq_norm]
        exact unit_norm_sub_eq_two_sin_half_angle _ _ hxnorm hynorm
      · positivity
    · intro a
      exact edist_ne_top _ _
  have heq :
      shiftChordalMetric.dist x y = 2 * Real.sin (shiftAngularMetric.dist x y / 2) := by
    rw [hchordal, hangular]
    exact iInf_two_sin_half_eq θ hθ0 hθπ
  have hang_nonneg : 0 <= shiftAngularMetric.dist x y := by
    exact @dist_nonneg _ shiftAngularMetric x y
  have hang_le_pi : shiftAngularMetric.dist x y <= Real.pi := by
    rw [hangular]
    have hθ_bdd : BddBelow (Set.range θ) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨a, rfl⟩
      exact hθ0 a
    exact le_trans (ciInf_le hθ_bdd (0 : Int)) (hθπ 0)
  refine ⟨heq, ?_, ?_⟩
  · rw [heq]
    exact two_div_pi_mul_le_two_sin_half hang_nonneg hang_le_pi
  · rw [heq]
    exact two_sin_half_le_self hang_nonneg

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
  exact translationOrbitClosed x

private lemma iInf_sq_eq {ι : Type*} [Nonempty ι] (r : ι -> Real)
    (hr : forall i, 0 <= r i) :
    (⨅ i, r i) ^ 2 = ⨅ i, (r i) ^ 2 := by
  let φ : Real -> Real := fun t => t ^ 2
  let A : Set Real := Set.range r
  have hA_nonempty : A.Nonempty := Set.range_nonempty r
  have hA_bdd : BddBelow A := by
    refine ⟨0, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact hr i
  have hA_nonneg : ∀ x ∈ A, 0 <= x := by
    rintro _ ⟨i, rfl⟩
    exact hr i
  have hmonoA : MonotoneOn φ A := by
    intro x hx y hy hxy
    have hx0 := hA_nonneg x hx
    have hy0 := hA_nonneg y hy
    dsimp [φ]
    nlinarith
  have hcont : ContinuousAt φ (sInf A) := by
    exact (continuous_id.pow 2).continuousAt
  have hmap := MonotoneOn.map_csInf_of_continuousWithinAt hcont.continuousWithinAt hmonoA
    hA_nonempty hA_bdd
  have hrange : Set.range (fun i => φ (r i)) = φ '' A := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨r i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨t, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  change φ (sInf (Set.range r)) = sInf (Set.range fun i => φ (r i))
  rw [hrange]
  exact hmap

private lemma iInf_two_sub_two_mul_eq {ι : Type*} [Nonempty ι] (c : ι -> Real)
    (hc : forall i, c i <= 1) :
    (⨅ i, 2 - 2 * c i) = 2 - 2 * sSup (Set.range c) := by
  let φ : Real -> Real := fun t => 2 - 2 * t
  let A : Set Real := Set.range c
  have hA_nonempty : A.Nonempty := Set.range_nonempty c
  have hA_bdd : BddAbove A := by
    refine ⟨1, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact hc i
  have hantiA : AntitoneOn φ A := by
    intro x _ y _ hxy
    dsimp [φ]
    linarith
  have hcont : ContinuousAt φ (sSup A) := by
    exact (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt
  have hmap := AntitoneOn.map_csSup_of_continuousWithinAt hcont.continuousWithinAt hantiA
    hA_nonempty hA_bdd
  have hrange : Set.range (fun i => φ (c i)) = φ '' A := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨c i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨t, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  change sInf (Set.range fun i => φ (c i)) = φ (sSup (Set.range c))
  rw [hrange]
  exact hmap.symm

private lemma translationOnL2_add {G : Type*} [AddCommGroup G] (a b : G)
    (f : l2Space G) :
    translationOnL2 a (translationOnL2 b f) = translationOnL2 (a + b) f := by
  ext i
  simp [translationOnL2, reindexL2, sub_eq_add_neg, add_assoc, add_comm]

private lemma inner_reindexL2 {ι : Type*} (e : ι ≃ ι) (f g : l2Space ι) :
    inner Real (reindexL2 e f) (reindexL2 e g) = inner Real f g := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  change (∑' i : ι, inner Real (f (e i)) (g (e i))) =
    ∑' i : ι, inner Real (f i) (g i)
  exact e.tsum_eq (fun i : ι => inner Real (f i) (g i))

private lemma translationOnL2_inner {G : Type*} [AddCommGroup G] (a b : G)
    (f g : l2Space G) :
    inner Real (translationOnL2 a f) (translationOnL2 b g) =
      inner Real f (translationOnL2 (b - a) g) := by
  have hb : a + (b - a) = b := by abel
  rw [← hb, ← translationOnL2_add]
  have harg : a + (b - a) - a = b - a := by abel
  rw [harg]
  change inner Real (reindexL2 (Equiv.subRight a) f)
      (reindexL2 (Equiv.subRight a) (translationOnL2 (b - a) g)) =
    inner Real f (translationOnL2 (b - a) g)
  exact inner_reindexL2 (Equiv.subRight a) f (translationOnL2 (b - a) g)

private lemma shiftCorrelationRange_translation_eq
    (p q : Int) (f g : shiftHilbertSphere) :
    Set.range (fun a : Int =>
      shiftRepresentativeInner (shiftAction p f) (shiftAction a (shiftAction q g))) =
      Set.range (fun a : Int => shiftRepresentativeInner f (shiftAction a g)) := by
  change Set.range (fun a : Int =>
      inner Real (translationOnL2 p (f : l2Space Int))
        (translationOnL2 a (translationOnL2 q (g : l2Space Int)))) =
    Set.range (fun a : Int => inner Real (f : l2Space Int) (translationOnL2 a g))
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨a + q - p, ?_⟩
    change inner Real (f : l2Space Int) (translationOnL2 (a + q - p) g) =
      inner Real (translationOnL2 p (f : l2Space Int))
        (translationOnL2 a (translationOnL2 q g))
    rw [translationOnL2_add, translationOnL2_inner]
  · rintro ⟨a, rfl⟩
    refine ⟨a + p - q, ?_⟩
    change inner Real (translationOnL2 p (f : l2Space Int))
        (translationOnL2 (a + p - q) (translationOnL2 q g)) =
      inner Real (f : l2Space Int) (translationOnL2 a g)
    rw [translationOnL2_add, translationOnL2_inner]
    congr 2
    abel

private lemma shiftRepresentativeInner_le_one (f g : shiftHilbertSphere) :
    shiftRepresentativeInner f g <= 1 := by
  have hf : ‖(f : l2Space Int)‖ = 1 := by
    rw [← dist_zero_right (f : l2Space Int)]
    exact f.2
  have hg : ‖(g : l2Space Int)‖ = 1 := by
    rw [← dist_zero_right (g : l2Space Int)]
    exact g.2
  simpa [shiftRepresentativeInner, hf, hg] using
    real_inner_le_norm (x := (f : l2Space Int)) (y := (g : l2Space Int))

private lemma shiftAction_dist_sq (a : Int) (f g : shiftHilbertSphere) :
    dist f (shiftAction a g) ^ 2 =
      2 - 2 * shiftRepresentativeInner f (shiftAction a g) := by
  have hf : ‖(f : l2Space Int)‖ = 1 := by
    rw [← dist_zero_right (f : l2Space Int)]
    exact f.2
  have hg : ‖(shiftAction a g : l2Space Int)‖ = 1 := by
    rw [← dist_zero_right (shiftAction a g : l2Space Int)]
    exact (shiftAction a g).2
  rw [Subtype.dist_eq, dist_eq_norm, norm_sub_sq_real, hf, hg]
  simp [shiftRepresentativeInner]
  ring

private lemma shiftCorrelationFormula_for_out (x y : shiftSphereQuotient) :
    (letI : PseudoMetricSpace shiftSphereQuotient := shiftChordalMetric;
      dist x y ^ 2 =
        2 - 2 * sSup (Set.range fun a : Int =>
          shiftRepresentativeInner (Quotient.out x) (shiftAction a (Quotient.out y)))) := by
  letI : PseudoMetricSpace shiftSphereQuotient := shiftChordalMetric
  let r : Int -> Real := fun a => dist (Quotient.out x) (shiftAction a (Quotient.out y))
  let c : Int -> Real := fun a =>
    shiftRepresentativeInner (Quotient.out x) (shiftAction a (Quotient.out y))
  have hdist : dist x y = ⨅ a : Int, r a := by
    dsimp [shiftChordalMetric, orbitQuotientPseudoMetricSpace,
      orbitQuotientPseudoEMetricSpace, PseudoEMetricSpace.toPseudoMetricSpace,
      PseudoEMetricSpace.toPseudoMetricSpaceOfDist, r]
    change (⨅ a : Int, edist (Quotient.out x) (shiftAction a (Quotient.out y))).toReal =
      ⨅ a : Int, dist (Quotient.out x) (shiftAction a (Quotient.out y))
    rw [ENNReal.toReal_iInf]
    · congr with a
    · intro a
      exact edist_ne_top _ _
  have hr_nonneg : forall a, 0 <= r a := fun a => dist_nonneg
  have hc_le_one : forall a, c a <= 1 := by
    intro a
    exact shiftRepresentativeInner_le_one (Quotient.out x) (shiftAction a (Quotient.out y))
  calc
    dist x y ^ 2 = (⨅ a : Int, r a) ^ 2 := by rw [hdist]
    _ = ⨅ a : Int, (r a) ^ 2 := iInf_sq_eq r hr_nonneg
    _ = ⨅ a : Int, 2 - 2 * c a := by
      congr with a
      exact shiftAction_dist_sq a (Quotient.out x) (Quotient.out y)
    _ = 2 - 2 * sSup (Set.range c) := iInf_two_sub_two_mul_eq c hc_le_one
    _ = 2 - 2 * sSup (Set.range fun a : Int =>
        shiftRepresentativeInner (Quotient.out x) (shiftAction a (Quotient.out y))) := rfl

/-- The shift-quotient distance is determined by translated representative correlations. -/
theorem shiftCorrelationFormula (f g : shiftHilbertSphere) :
    (letI : PseudoMetricSpace shiftSphereQuotient := shiftChordalMetric;
      dist (shiftQuotientMk f) (shiftQuotientMk g) ^ 2 =
        2 - 2 * sSup (Set.range fun a : Int =>
          shiftRepresentativeInner f (shiftAction a g))) := by
  letI : PseudoMetricSpace shiftSphereQuotient := shiftChordalMetric
  let x : shiftSphereQuotient := shiftQuotientMk f
  let y : shiftSphereQuotient := shiftQuotientMk g
  have hxrel : (translationOrbitSetoid (G := Int)).r (Quotient.out x) f := by
    simpa [x, shiftQuotientMk] using
      (Quotient.mk_out (s := translationOrbitSetoid (G := Int)) f)
  have hyrel : (translationOrbitSetoid (G := Int)).r (Quotient.out y) g := by
    simpa [y, shiftQuotientMk] using
      (Quotient.mk_out (s := translationOrbitSetoid (G := Int)) g)
  rcases hxrel with ⟨p, hfp⟩
  rcases hyrel with ⟨q, hgq⟩
  change f = shiftAction p (Quotient.out x) at hfp
  change g = shiftAction q (Quotient.out y) at hgq
  have hsup :
      sSup (Set.range fun a : Int =>
        shiftRepresentativeInner (Quotient.out x) (shiftAction a (Quotient.out y))) =
        sSup (Set.range fun a : Int => shiftRepresentativeInner f (shiftAction a g)) := by
    rw [hfp, hgq]
    rw [shiftCorrelationRange_translation_eq p q (Quotient.out x) (Quotient.out y)]
  change dist x y ^ 2 =
    2 - 2 * sSup (Set.range fun a : Int => shiftRepresentativeInner f (shiftAction a g))
  rw [shiftCorrelationFormula_for_out x y, hsup]

private lemma higherRankCorrelationRange_translation_eq
    (n : Nat) (p q : Fin n -> Int) (f g : higherRankHilbertSphere n) :
    Set.range (fun a : Fin n -> Int =>
      higherRankRepresentativeInner n (higherRankTranslation n p f)
        (higherRankTranslation n a (higherRankTranslation n q g))) =
      Set.range (fun a : Fin n -> Int =>
        higherRankRepresentativeInner n f (higherRankTranslation n a g)) := by
  change Set.range (fun a : Fin n -> Int =>
      inner Real (translationOnL2 p (f : l2Space (Fin n -> Int)))
        (translationOnL2 a (translationOnL2 q (g : l2Space (Fin n -> Int))))) =
    Set.range (fun a : Fin n -> Int =>
      inner Real (f : l2Space (Fin n -> Int)) (translationOnL2 a g))
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨a + q - p, ?_⟩
    change inner Real (f : l2Space (Fin n -> Int)) (translationOnL2 (a + q - p) g) =
      inner Real (translationOnL2 p (f : l2Space (Fin n -> Int)))
        (translationOnL2 a (translationOnL2 q g))
    rw [translationOnL2_add, translationOnL2_inner]
  · rintro ⟨a, rfl⟩
    refine ⟨a + p - q, ?_⟩
    change inner Real (translationOnL2 p (f : l2Space (Fin n -> Int)))
        (translationOnL2 (a + p - q) (translationOnL2 q g)) =
      inner Real (f : l2Space (Fin n -> Int)) (translationOnL2 a g)
    rw [translationOnL2_add, translationOnL2_inner]
    congr 2
    abel

private lemma higherRankRepresentativeInner_le_one
    (n : Nat) (f g : higherRankHilbertSphere n) :
    higherRankRepresentativeInner n f g <= 1 := by
  have hf : ‖(f : l2Space (Fin n -> Int))‖ = 1 := by
    rw [← dist_zero_right (f : l2Space (Fin n -> Int))]
    exact f.2
  have hg : ‖(g : l2Space (Fin n -> Int))‖ = 1 := by
    rw [← dist_zero_right (g : l2Space (Fin n -> Int))]
    exact g.2
  simpa [higherRankRepresentativeInner, hf, hg] using
    real_inner_le_norm (x := (f : l2Space (Fin n -> Int))) (y := (g : l2Space (Fin n -> Int)))

private lemma higherRankTranslation_dist_sq
    (n : Nat) (a : Fin n -> Int) (f g : higherRankHilbertSphere n) :
    dist f (higherRankTranslation n a g) ^ 2 =
      2 - 2 * higherRankRepresentativeInner n f (higherRankTranslation n a g) := by
  have hf : ‖(f : l2Space (Fin n -> Int))‖ = 1 := by
    rw [← dist_zero_right (f : l2Space (Fin n -> Int))]
    exact f.2
  have hg : ‖(higherRankTranslation n a g : l2Space (Fin n -> Int))‖ = 1 := by
    rw [← dist_zero_right (higherRankTranslation n a g : l2Space (Fin n -> Int))]
    exact (higherRankTranslation n a g).2
  rw [Subtype.dist_eq, dist_eq_norm, norm_sub_sq_real, hf, hg]
  simp [higherRankRepresentativeInner]
  ring

private lemma higherRankCorrelationFormula_for_out
    (n : Nat) (x y : higherRankSphereQuotient n) :
    (letI : PseudoMetricSpace (higherRankSphereQuotient n) := higherRankChordalMetric n;
      dist x y ^ 2 =
        2 - 2 * sSup (Set.range fun a : Fin n -> Int =>
          higherRankRepresentativeInner n (Quotient.out x) (higherRankTranslation n a
            (Quotient.out y)))) := by
  letI : PseudoMetricSpace (higherRankSphereQuotient n) := higherRankChordalMetric n
  let r : (Fin n -> Int) -> Real := fun a =>
    dist (Quotient.out x) (higherRankTranslation n a (Quotient.out y))
  let c : (Fin n -> Int) -> Real := fun a =>
    higherRankRepresentativeInner n (Quotient.out x) (higherRankTranslation n a
      (Quotient.out y))
  have hdist : dist x y = ⨅ a : Fin n -> Int, r a := by
    dsimp [higherRankChordalMetric, orbitQuotientPseudoMetricSpace,
      orbitQuotientPseudoEMetricSpace, PseudoEMetricSpace.toPseudoMetricSpace,
      PseudoEMetricSpace.toPseudoMetricSpaceOfDist, r]
    change (⨅ a : Fin n -> Int, edist (Quotient.out x)
        (higherRankTranslation n a (Quotient.out y))).toReal =
      ⨅ a : Fin n -> Int,
        dist (Quotient.out x) (higherRankTranslation n a (Quotient.out y))
    rw [ENNReal.toReal_iInf]
    · congr with a
    · intro a
      exact edist_ne_top _ _
  have hr_nonneg : forall a, 0 <= r a := fun a => dist_nonneg
  have hc_le_one : forall a, c a <= 1 := by
    intro a
    exact higherRankRepresentativeInner_le_one n (Quotient.out x)
      (higherRankTranslation n a (Quotient.out y))
  calc
    dist x y ^ 2 = (⨅ a : Fin n -> Int, r a) ^ 2 := by rw [hdist]
    _ = ⨅ a : Fin n -> Int, (r a) ^ 2 := iInf_sq_eq r hr_nonneg
    _ = ⨅ a : Fin n -> Int, 2 - 2 * c a := by
      congr with a
      exact higherRankTranslation_dist_sq n a (Quotient.out x) (Quotient.out y)
    _ = 2 - 2 * sSup (Set.range c) := iInf_two_sub_two_mul_eq c hc_le_one
    _ = 2 - 2 * sSup (Set.range fun a : Fin n -> Int =>
        higherRankRepresentativeInner n (Quotient.out x) (higherRankTranslation n a
          (Quotient.out y))) := rfl

/-- The quotient distance is determined by translated representative correlations. -/
theorem higherRankCorrelationFormula (n : Nat) (f g : higherRankHilbertSphere n) :
    (letI : PseudoMetricSpace (higherRankSphereQuotient n) := higherRankChordalMetric n;
      dist (higherRankQuotientMk n f) (higherRankQuotientMk n g) ^ 2 =
        2 - 2 * higherRankCorrelationSupFromRepresentatives n f g) := by
  letI : PseudoMetricSpace (higherRankSphereQuotient n) := higherRankChordalMetric n
  let x : higherRankSphereQuotient n := higherRankQuotientMk n f
  let y : higherRankSphereQuotient n := higherRankQuotientMk n g
  have hxrel : (translationOrbitSetoid (G := Fin n -> Int)).r (Quotient.out x) f := by
    simpa [x, higherRankQuotientMk] using
      (Quotient.mk_out (s := translationOrbitSetoid (G := Fin n -> Int)) f)
  have hyrel : (translationOrbitSetoid (G := Fin n -> Int)).r (Quotient.out y) g := by
    simpa [y, higherRankQuotientMk] using
      (Quotient.mk_out (s := translationOrbitSetoid (G := Fin n -> Int)) g)
  rcases hxrel with ⟨p, hfp⟩
  rcases hyrel with ⟨q, hgq⟩
  change f = higherRankTranslation n p (Quotient.out x) at hfp
  change g = higherRankTranslation n q (Quotient.out y) at hgq
  have hsup :
      sSup (Set.range fun a : Fin n -> Int =>
        higherRankRepresentativeInner n (Quotient.out x) (higherRankTranslation n a
          (Quotient.out y))) =
        higherRankCorrelationSupFromRepresentatives n f g := by
    rw [higherRankCorrelationSupFromRepresentatives, higherRankCorrelationSet, hfp, hgq]
    rw [higherRankCorrelationRange_translation_eq n p q (Quotient.out x) (Quotient.out y)]
  change dist x y ^ 2 = 2 - 2 * higherRankCorrelationSupFromRepresentatives n f g
  rw [higherRankCorrelationFormula_for_out n x y, hsup]

end

end SphereObstructionHilbertShiftQuotient
