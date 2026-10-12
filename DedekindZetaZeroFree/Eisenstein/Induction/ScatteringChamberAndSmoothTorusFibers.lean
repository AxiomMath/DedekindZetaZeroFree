module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.BigCellSectionSmoothness
public import DedekindZetaZeroFree.Eisenstein.Induction.IwasawaCompactOverlap
public import DedekindZetaZeroFree.Eisenstein.Induction.CompactAndFlatSections
public import DedekindZetaZeroFree.Metaplectic.Intertwining.SpatialSmoothingAndCovariantClosure
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.BruhatTwoCellIntegral

@[expose] public section

section

noncomputable section
open scoped NumberField Classical
set_option maxHeartbeats 1200000
set_option maxRecDepth 2500
namespace DedekindZetaZeroFree.KPLiteralChamber
open KPLiteralRaw
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem literal_raw_group_chart_contDiffOn (h : Functions F ζ hζ) (hh : Smooth F ζ hζ h)
    (g : G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => h (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g))
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) := by
  exact literal_raw_group_chart_contDiffOn_source F ζ hζ h hh g

end DedekindZetaZeroFree.KPLiteralChamber

end

end

section

noncomputable section
open scoped NumberField Classical BigOperators
namespace DedekindZetaZeroFree.KPLiteralChamber
open KPLiteralRaw
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private def diagonalCoordinates (z : KPGlobalTorusFunctionData.TorusArch F) :
    KPGlobalTorusBorelTwistCompatibility.GroupArch F :=
  fun w i => if i = 1 then z w else 0

private theorem diagonalCoordinates_smooth :
    ContDiff ℝ (⊤ : ℕ∞) (diagonalCoordinates F) := by
  apply contDiff_pi.mpr
  intro w
  apply contDiff_pi.mpr
  intro i
  by_cases hi : i = 1
  · simp only [diagonalCoordinates, hi, ↓reduceIte]
    fun_prop
  · simp only [diagonalCoordinates, hi, ↓reduceIte]
    exact contDiff_const

private theorem diagonal_chart (z : KPGlobalTorusFunctionData.TorusArch F) :
    KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ (diagonalCoordinates F z) =
      (KPGlobalTorusFunctionData.torusArchChart F ζ hζ z).val := by
  unfold KPGlobalTorusBorelTwistCompatibility.groupArchChart
    KPGlobalTorusFunctionData.torusArchChart KPGlobalTorusFunctionData.archDiagonalLift
  congr 2
  apply RestrictedProduct.ext
  intro v
  cases v with
  | inr q => rfl
  | inl w =>
    simp [KPGlobalTorusBorelTwistCompatibility.groupArchTuple,
      KPGlobalTorusFunctionData.archDiagonalTuple, diagonalCoordinates]

private theorem half_smooth : ContDiffOn ℝ (⊤ : ℕ∞)
    (fun z => KPGlobalTorusFunctionData.deltaHalf F ζ hζ
      (KPGlobalTorusFunctionData.torusArchChart F ζ hζ z))
    (KPGlobalTorusFunctionData.torusArchDomain F) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : KPGlobalTorusFunctionData.TorusArch F => ∏ w, ‖z w‖ ^ 2) := by
    apply contDiff_prod
    intro w _
    have he : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : KPGlobalTorusFunctionData.TorusArch F => z w) := by fun_prop
    exact he.norm_sq ℝ
  have hn (z : KPGlobalTorusFunctionData.TorusArch F)
      (hz : z ∈ KPGlobalTorusFunctionData.torusArchDomain F) :
      (∏ w, ‖z w‖ ^ 2) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr
      (fun w _ => pow_ne_zero _ (norm_ne_zero_iff.mpr (hz w)))
  have hc := Complex.ofRealCLM.contDiff.comp_contDiffOn (hd.contDiffOn.sqrt hn)
  apply hc.congr
  intro z hz
  simp only [KPGlobalTorusFunctionData.deltaHalf,
    KPGlobalTorusBorelNormTwistTransport.AnalyticInputs.delta_chart_formula F ζ hζ z hz]
  rfl

theorem literal_raw_torus_fiber_contDiffOn_source (h : Functions F ζ hζ) (hh : Smooth F ζ hζ h)
    (g : G F ζ hζ) (t : KPGlobalTorusFunctionData.E F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => (KPGlobalTorusFunctionData.deltaHalf F ζ hζ
          (KPGlobalTorusFunctionData.torusArchChart F ζ hζ z * t))⁻¹ *
        h ((KPGlobalTorusFunctionData.torusArchChart F ζ hζ z * t).val * g))
      (KPGlobalTorusFunctionData.torusArchDomain F) := by
  have hmap : Set.MapsTo (diagonalCoordinates F) (KPGlobalTorusFunctionData.torusArchDomain F)
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) := by
    intro z hz w
    exact hz w
  have hv := (literal_raw_group_chart_contDiffOn_source F ζ hζ h hh (t.val * g)).comp
    (diagonalCoordinates_smooth F).contDiffOn hmap
  have hv' : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => h ((KPGlobalTorusFunctionData.torusArchChart F ζ hζ z).val * (t.val * g)))
      (KPGlobalTorusFunctionData.torusArchDomain F) := by
    simpa only [Function.comp_def, diagonal_chart] using hv
  have hm := ((half_smooth F ζ hζ).mul contDiffOn_const).inv (by
    intro z hz
    have hp (a : KPGlobalTorusFunctionData.E F ζ hζ) :
        KPGlobalTorusFunctionData.deltaHalf F ζ hζ a ≠ 0 := by
      have hn : 0 < (((KPGlobalTorusFunctionData.delta F ζ hζ a : NNReal) : ℝ)) := by
        exact_mod_cast (pos_iff_ne_zero.mpr (Units.ne_zero _))
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hn))
    exact mul_ne_zero (hp _) (hp t))
  convert hm.mul hv' using 1
  funext z
  simp [KPGlobalTorusFunctionData.deltaHalf, map_mul, Real.sqrt_mul, mul_assoc]

end DedekindZetaZeroFree.KPLiteralChamber

end
end

section

noncomputable section
open scoped NumberField Classical
set_option maxHeartbeats 1200000
set_option maxRecDepth 2500
namespace DedekindZetaZeroFree.KPLiteralChamber
open KPLiteralRaw
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private theorem half_mul (a b : KPGlobalTorusFunctionData.E F ζ hζ) :
    KPGlobalTorusFunctionData.deltaHalf F ζ hζ (a*b) =
    KPGlobalTorusFunctionData.deltaHalf F ζ hζ a * KPGlobalTorusFunctionData.deltaHalf F ζ hζ b := by
  simp [KPGlobalTorusFunctionData.deltaHalf, map_mul, Real.sqrt_mul]
private theorem half_ne (a : KPGlobalTorusFunctionData.E F ζ hζ) : KPGlobalTorusFunctionData.deltaHalf F ζ hζ a ≠ 0 := by
  have hp : 0 < (((KPGlobalTorusFunctionData.delta F ζ hζ a : NNReal) : ℝ)) := by
    exact_mod_cast (pos_iff_ne_zero.mpr (Units.ne_zero _))
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hp))
private def fiber (K : Subgroup (G F ζ hζ)) (f : Flat F ζ hζ K) (g : G F ζ hζ) :
    KPGlobalTorusFunctionData.TorusFunctions F ζ hζ (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) := by
  refine ⟨fun t => (KPGlobalTorusFunctionData.deltaHalf F ζ hζ t)⁻¹ * f.val 0 (t.val * g), ?_⟩
  intro r t
  have h := (literalSource F ζ hζ K f 0).property r 0 (t.val * g)
  have hn : KPGlobalTorusFunctionData.N F ζ hζ 0 = 1 := by
    unfold KPGlobalTorusFunctionData.N
    have ht : KPGlobalTorusFunctionData.rootTuple F ζ hζ 0 = 1 := by
      apply Subtype.ext
      funext v
      change KPStandardLocalRootLifts.N F ζ hζ v (KPAdelicCoverRestrictedProduct.adeleEval F v 0) = 1
      simp [KPAdelicCoverRestrictedProduct.adeleEval]
    rw [ht, map_one, map_one]
  simp only [hn, mul_one] at h
  change f.val 0 (r.val.val * (t.val * g)) = _ at h
  change (KPGlobalTorusFunctionData.deltaHalf F ζ hζ (r.val * t))⁻¹ * f.val 0 ((r.val.val * t.val) * g) = _
  rw [half_mul, mul_assoc, h]
  field_simp [half_ne F ζ hζ r.val, half_ne F ζ hζ t]
  <;> rfl

private theorem fiber_borel_cov (K : Subgroup (G F ζ hζ)) (f : Flat F ζ hζ K)
    (a t : KPGlobalTorusFunctionData.E F ζ hζ) (x : KPAdeles F) (g : G F ζ hζ) :
    (fiber F ζ hζ K f ((a.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g)).val t =
      KPGlobalTorusFunctionData.deltaHalf F ζ hζ a * (fiber F ζ hζ K f g).val (t * a) := by
  change (KPGlobalTorusFunctionData.deltaHalf F ζ hζ t)⁻¹ *
    f.val 0 (t.val * ((a.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g)) = _
  have he : t.val * ((a.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g) =
      KPGlobalTorusFunctionData.N F ζ hζ ((KPGlobalTorusFunctionData.p F ζ hζ (t*a) : KPAdeles F) * x) * ((t*a).val * g) := by
    rw [← mul_assoc, ← mul_assoc]
    change (t*a).val * KPGlobalTorusFunctionData.N F ζ hζ x * g = _
    rw [coveredTorus_normalizes_upperRoot]
    simp [mul_assoc]
  rw [he, literal_unipotent_invariance]
  change _ = KPGlobalTorusFunctionData.deltaHalf F ζ hζ a *
    ((KPGlobalTorusFunctionData.deltaHalf F ζ hζ (t*a))⁻¹ * f.val 0 ((t*a).val*g))
  rw [half_mul]
  field_simp [half_ne F ζ hζ t, half_ne F ζ hζ a]

private theorem fiber_level (K : Subgroup (G F ζ hζ)) (f : Flat F ζ hζ K) (g : G F ζ hζ) :
    ∃ U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      fiber F ζ hζ K f g ∈ KPGlobalTorusFunctionData.RightLevel
        (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0).H
        (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0).character.toMonoidHom
        ((KPGlobalTorusFunctionData.globalLevel F ζ hζ U).comap (KPGlobalTorusFunctionData.torus F ζ hζ).subtype) := by
  obtain ⟨J, hJ⟩ := (f.property.1 0).1.2.2
  obtain ⟨U, hc, hU⟩ := KPGlobalTorusBorelTwistCompatibilityBorelInduction.UniformFiberLevel.exists_compact_conjugate_torus_level F ζ hζ J g
  refine ⟨U, ?_⟩
  intro u
  apply Subtype.ext
  funext t
  change (KPGlobalTorusFunctionData.deltaHalf F ζ hζ (t*u.val))⁻¹ * f.val 0 ((t*u.val).val*g) =
    (KPGlobalTorusFunctionData.deltaHalf F ζ hζ t)⁻¹ * f.val 0 (t.val*g)
  have hd := KPGlobalTorusBorelNormTwistTransport.delta_compact_subgroup F ζ hζ
    ((KPGlobalTorusFunctionData.globalLevel F ζ hζ U).comap (KPGlobalTorusFunctionData.torus F ζ hζ).subtype) hc u
  have hh : KPGlobalTorusFunctionData.deltaHalf F ζ hζ u.val = 1 := by
    simp [KPGlobalTorusFunctionData.deltaHalf, hd]
  rw [half_mul, hh, mul_one]
  congr 1
  have he : (t*u.val).val*g = (t.val*g)*(g⁻¹*u.val.val*g) := by simp; group
  rw [he]
  exact hJ _ _ (hU u)

theorem literal_raw_torus_fiber_contDiffOn (h : Functions F ζ hζ) (hh : Smooth F ζ hζ h)
    (g : G F ζ hζ) (t : KPGlobalTorusFunctionData.E F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => (KPGlobalTorusFunctionData.deltaHalf F ζ hζ
          (KPGlobalTorusFunctionData.torusArchChart F ζ hζ z * t))⁻¹ *
        h ((KPGlobalTorusFunctionData.torusArchChart F ζ hζ z * t).val * g))
      (KPGlobalTorusFunctionData.torusArchDomain F) := by
  exact literal_raw_torus_fiber_contDiffOn_source F ζ hζ h hh g t

theorem literal_zero_induced_lift (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) :
    ∃ p : KPGlobalTorusBorelTwistCompatibility.Induced F ζ hζ
        (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0),
      ∀ (g : G F ζ hζ) (t : KPGlobalTorusFunctionData.E F ζ hζ),
        (p.val.val g).val.val t =
          (KPGlobalTorusFunctionData.deltaHalf F ζ hζ t)⁻¹ * f.val 0 (t.val * g) := by
  have hs (g : G F ζ hζ) : fiber F ζ hζ K f g ∈
      KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ
        (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) := by
    obtain ⟨U, hU⟩ := fiber_level F ζ hζ K f g
    apply Submodule.mem_iSup_of_mem U
    refine ⟨?_, hU⟩
    intro t
    exact literal_raw_torus_fiber_contDiffOn F ζ hζ (f.val 0) (f.property.1 0).1 g t
  let p : KPGlobalTorusBorelTwistCompatibility.InducedFunctions F ζ hζ
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) :=
    ⟨fun g => ⟨fiber F ζ hζ K f g, hs g⟩, by
      intro a x g
      apply Subtype.ext
      apply Subtype.ext
      funext t
      exact fiber_borel_cov F ζ hζ K f a t x g⟩
  obtain ⟨J, hJ⟩ := (f.property.1 0).1.2.2
  have hp : p ∈ KPGlobalTorusBorelTwistCompatibility.Induced F ζ hζ
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) := by
    apply Submodule.mem_iSup_of_mem J
    constructor
    · intro g
      simpa [p, fiber, KPGlobalTorusFunctionData.deltaHalf] using
        literal_raw_group_chart_contDiffOn F ζ hζ (f.val 0) (f.property.1 0).1 g
    · intro g j
      apply Subtype.ext
      apply Subtype.ext
      funext t
      change (KPGlobalTorusFunctionData.deltaHalf F ζ hζ t)⁻¹ * f.val 0 (t.val*(g*j.val)) =
        (KPGlobalTorusFunctionData.deltaHalf F ζ hζ t)⁻¹ * f.val 0 (t.val*g)
      rw [← mul_assoc, hJ _ _ j.property]
  exact ⟨⟨p, hp⟩, fun _ _ => rfl⟩

end DedekindZetaZeroFree.KPLiteralChamber

end
end

section

noncomputable section
open scoped NumberField Classical
namespace DedekindZetaZeroFree.KPLiteralChamber
open KPLiteralRaw
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem literal_zero_finite_stage (K : Subgroup (G F ζ hζ))
    (f : Flat F ζ hζ K) :
    ∃ (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
      (T : KPGlobalEisensteinData.CompactTypeStage
        ((KPGlobalTorusFunctionData.borelRightTranslation F ζ hζ
          (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0)).comp K.subtype)),
      literalSource F ζ hζ K f 0 ∈
        fixedSubmodule
          ((KPGlobalTorusFunctionData.borelRightTranslation F ζ hζ
            (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0)).comp
              (KPGlobalTorusFunctionData.finitePart F ζ hζ).subtype)
          U.toOpenSubgroup.toSubgroup ∧
      literalSource F ζ hζ K f 0 ∈ T.space := by
  let e : KPMsRationalCompactCrossPairing.Source F ζ hζ 0 →ₗ[ℂ]
      Functions F ζ hζ :=
    { toFun := fun v => v.val
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have he : Function.Injective e := by
    intro v w h
    exact Subtype.ext h
  obtain ⟨S, hS, hfS, hstable⟩ := f.property.2.2
  letI : Module.Finite ℂ S := hS
  let T : KPGlobalEisensteinData.CompactTypeStage
      ((KPGlobalTorusFunctionData.borelRightTranslation F ζ hζ
        (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0)).comp K.subtype) :=
    { space := S.comap e
      finiteDimensional := by
        exact FiniteDimensional.of_injective
          (e.restrict (fun _ hv => hv : ∀ v ∈ S.comap e, e v ∈ S))
          (by
            intro v w h
            apply Subtype.ext
            apply he
            exact congrArg (fun x : S => (x : Functions F ζ hζ)) h)
      invariant := by
        intro k v hv
        exact hstable k (e v) hv }
  obtain ⟨U, hU⟩ := (f.property.1 0).1.2.2
  refine ⟨U, T, ?_, hfS⟩
  intro u
  apply Subtype.ext
  funext g
  exact hU g u.val.val (Subgroup.mem_map.mpr ⟨u.val, u.property, rfl⟩)

theorem literal_zero_mem_sourceCore (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) :
    literalSource F ζ hζ K f 0 ∈
      KPMsRationalCompactCrossPairing.sourceCore F ζ hζ
        (literalIwasawa F ζ hζ K hK) := by
  obtain ⟨p, hp⟩ := literal_zero_induced_lift F ζ hζ K hK f
  have hs : literalSource F ζ hζ K f 0 ∈
      KPMsRationalCompactCrossPairing.scalarSmooth F ζ hζ
        (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) := by
    refine ⟨p, ?_⟩
    apply Subtype.ext
    funext g
    rw [KPGlobalTorusBorelTwistCompatibility.scalarSection_formula, hp]
    simp [KPGlobalTorusFunctionData.deltaHalf, literalSource]
  obtain ⟨U, T, hU, hT⟩ := literal_zero_finite_stage F ζ hζ K f
  exact Submodule.mem_iSup_of_mem U
    (Submodule.mem_iSup_of_mem T ⟨⟨hs, hU⟩, hT⟩)

def literalCore (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) :
    KPMsRationalCompactCrossPairing.Vplus F ζ hζ (literalIwasawa F ζ hζ K hK) :=
  ⟨literalSource F ζ hζ K f 0, literal_zero_mem_sourceCore F ζ hζ K hK f⟩
end DedekindZetaZeroFree.KPLiteralChamber

end
end
