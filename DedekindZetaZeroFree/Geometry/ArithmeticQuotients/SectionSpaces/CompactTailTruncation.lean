module

public import DedekindZetaZeroFree.Metaplectic.Cubic.Cotangent.IntrinsicL2Space

@[expose] public section

section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.RepresentationTheory.ActualSectorTestDensity.CompactTailSources

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContSectorLineL2Isometry KPContSectorSmoothFramesSupport
open KPContActualCotangentMeasurableFamilies
open KPContCotangentActualOverlap KPContCotangentOverlapRationalBranches
open KPContCotangentActualGenuineTwistIsotropy

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

private theorem continuous_labeledA_placeEquiv :
    Continuous (labeledA (placeEquiv F ζ hζ)) := by
  apply continuous_pi
  intro k
  exact (continuous_apply _).comp (CotangentLogCoframe.A (d F)).continuous

private theorem measurable_q (a : Chart (U := U) (H := H)) :
    Measurable (KPContCotangentOverlapRationalBranches.q a) := by
  have hcm : Continuous (KPFiniteCuspAtlas.componentMap F ζ hζ U
      ((H.atlas U).representative a.component)) := by
    have he : KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative a.component) =
        (H.atlas U).components ∘ Sigma.mk a.component := by
      funext x; exact ((H.atlas U).components_formula a.component x).symm
    rw [he]
    exact ((H.atlas U).components.isOpenEmbedding.comp IsOpenEmbedding.sigmaMk).continuous
  have hproj : Measurable (KPCuspSiegel.projection F
      (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H a.component)) :=
    measurable_quotient_mk''
  have hcomp : KPContCotangentOverlapRationalBranches.q a =
      KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative a.component)
      ∘ KPCuspSiegel.projection F
          (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H a.component)
      ∘ labeledA (placeEquiv F ζ hζ) := rfl
  rw [hcomp]
  exact hcm.measurable.comp (hproj.comp continuous_labeledA_placeEquiv.measurable)

private theorem q_isotropyArrow (a : Chart (U := U) (H := H)) (γ : Gamma a) (x : M F)
    (hx : x ∈ omega a) :
    KPContCotangentOverlapRationalBranches.q a ((isotropyArrow a γ).psi x) =
      KPContCotangentOverlapRationalBranches.q a x := by
  simp only [KPContCotangentOverlapRationalBranches.q]
  apply congrArg (KPFiniteCuspAtlas.componentMap F ζ hζ U
    ((H.atlas U).representative a.component))
  simp only [Arrow.psi, coordinateMap, isotropyArrow, isotropyChart,
    ChartKind.representative, inv_one, one_mul, mul_one]
  have hh (z : KPCuspGenuineMonodromy.SymmetricSpace F) :
      labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) z) = z := by
    funext k; simp [labeledA, labeledAInv]
  rw [hh]
  apply Quotient.sound
  apply MulAction.orbitRel_apply.mpr
  exact MulAction.mem_orbit_iff.mpr ⟨γ.val.1.val, rfl⟩

private theorem q_actualBranch {a b : Chart (U := U) (H := H)} (e : ActualBranch a b)
    (x : M F) :
    KPContCotangentOverlapRationalBranches.q b (e.arrow.psi x) =
      KPContCotangentOverlapRationalBranches.q a x := by
  rcases a with ⟨i, ca, oa, da, dao, dac, das, dai⟩
  rcases b with ⟨j, cb, ob, db, dbo, dbc, dbs, dbi⟩
  rcases e with ⟨h, e, hs, ht, hl⟩
  dsimp at h
  subst j
  simp only [KPContCotangentOverlapRationalBranches.q]
  apply congrArg (KPFiniteCuspAtlas.componentMap F ζ hζ U
    ((H.atlas U).representative i))
  simp only [Arrow.psi, coordinateMap, targetChart, isotropyChart,
    ChartKind.representative, inv_one, one_mul, mul_one]
  have ha (v : KPCuspGenuineMonodromy.SymmetricSpace F) :
      labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) v) = v := by
    funext k; simp [labeledA, labeledAInv]
  rw [ha]
  apply Quotient.sound
  exact ⟨e.gamma, rfl⟩

private theorem sectionNorm_indicator_of_coeff
    (s u : Sections F ζ hζ U R P H) (D : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U))
    (h : ∀ i x, (u i).val x =
      (if Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U)
          (x, (H.atlas U).representative i) ∈ D then (s i).val x else 0)) :
    sectionNorm F ζ hζ U R P H u = D.indicator (sectionNorm F ζ hζ U R P H s) := by
  funext b
  obtain ⟨⟨i, y⟩, rfl⟩ := (H.atlas U).components.surjective b
  refine Quotient.inductionOn y (fun x => ?_)
  have hbc : (H.atlas U).components ⟨i, Quotient.mk _ x⟩ =
      Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U)
        (x, (H.atlas U).representative i) := by
    rw [(H.atlas U).components_formula]
    rfl
  rw [sectionNorm_component, hbc]
  by_cases hx : Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U)
      (x, (H.atlas U).representative i) ∈ D
  · rw [Set.indicator_of_mem hx, h i x, if_pos hx, ← hbc, sectionNorm_component]
  · rw [Set.indicator_of_notMem hx, h i x, if_neg hx]
    simp

private theorem sectionNorm_indicator_of_coeff_neg
    (s u : Sections F ζ hζ U R P H) (E : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U))
    (h : ∀ i x, (u i).val x =
      (if Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U)
          (x, (H.atlas U).representative i) ∈ E then 0 else (s i).val x)) :
    sectionNorm F ζ hζ U R P H u = Eᶜ.indicator (sectionNorm F ζ hζ U R P H s) := by
  funext b
  obtain ⟨⟨i, y⟩, rfl⟩ := (H.atlas U).components.surjective b
  refine Quotient.inductionOn y (fun x => ?_)
  have hbc : (H.atlas U).components ⟨i, Quotient.mk _ x⟩ =
      Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U)
        (x, (H.atlas U).representative i) := by
    rw [(H.atlas U).components_formula]
    rfl
  rw [sectionNorm_component, hbc]
  by_cases hx : Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U)
      (x, (H.atlas U).representative i) ∈ E
  · rw [Set.indicator_of_notMem (by simp [Set.mem_compl_iff, hx]), h i x, if_pos hx]
    simp
  · rw [Set.indicator_of_mem (by simp [Set.mem_compl_iff, hx]), h i x, if_neg hx,
      ← hbc, sectionNorm_component]

private theorem sectionNorm_nonneg' (s : Sections F ζ hζ U R P H)
    (b : KPMsFixedHaarDisintegration.Spherical F ζ hζ U) :
    0 ≤ sectionNorm F ζ hζ U R P H s b := by
  obtain ⟨⟨i, y⟩, rfl⟩ := (H.atlas U).components.surjective b
  refine Quotient.inductionOn y (fun x => ?_)
  rw [sectionNorm_component]
  exact norm_nonneg _

private theorem squaredNorm_indicator_of_sectionNorm
    {u w : Sections F ζ hζ U R P H} {D : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)}
    (h : sectionNorm F ζ hζ U R P H u =
      D.indicator (sectionNorm F ζ hζ U R P H w)) :
    squaredNorm F ζ hζ U R P H u = D.indicator (squaredNorm F ζ hζ U R P H w) := by
  funext b
  have hb := congrFun h b
  by_cases hD : b ∈ D
  · rw [Set.indicator_of_mem hD] at hb
    simp only [squaredNorm, hb, Set.indicator_of_mem hD]
  · rw [Set.indicator_of_notMem hD] at hb
    simp only [squaredNorm, hb, Set.indicator_of_notMem hD]
    simp

structure ScalarIndicatorSpec (E : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U))
    (s t : BorelL2Sections F ζ hζ U R P H) : Prop where
  coefficients : ∀ (i : Fin (H.atlas U).componentCount) (x : KPFiniteCuspAtlas.SymmetricSpace F),
    (t.val i).val x =
      (if Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U)
          (x, (H.atlas U).representative i) ∈ E then (s.val i).val x else 0)
  norm : sectionNorm F ζ hζ U R P H t.val =
    E.indicator (sectionNorm F ζ hζ U R P H s.val)
  error : squaredNorm F ζ hζ U R P H (s.val - t.val) =
    Eᶜ.indicator (squaredNorm F ζ hζ U R P H s.val)
  integral_le : normIntegral F ζ hζ U R P H t.val ≤ normIntegral F ζ hζ U R P H s.val

structure CotangentIndicatorSpec (E : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U))
    (r t : Family (U := U) (H := H)) : Prop where
  coefficients : ∀ (a : Chart (U := U) (H := H))
      (x : KPContCotangentOverlapRationalBranches.omega a),
    coefficient t a x =
      (if KPContCotangentOverlapRationalBranches.q a x.val ∈ E
        then coefficient r a x else 0)
  norm : normSquare t = E.indicator (normSquare r)
  error : normSquare (r - t) = Eᶜ.indicator (normSquare r)
  integral_le :
    (∫⁻ b, ENNReal.ofReal (normSquare t b : ℝ) ∂baseMeasure (U := U) (R := R) (P := P)) ≤
      ∫⁻ b, ENNReal.ofReal (normSquare r b : ℝ) ∂baseMeasure (U := U) (R := R) (P := P)

theorem indicator_truncation (E : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U))
    (hE : MeasurableSet E) :
    (∀ s : BorelL2Sections F ζ hζ U R P H,
      ∃ t : BorelL2Sections F ζ hζ U R P H, ScalarIndicatorSpec E s t) ∧
    (∀ r : Family (U := U) (H := H),
      ∃ t : Family (U := U) (H := H), CotangentIndicatorSpec E r t) := by
  classical
  constructor
  · intro s
    let tSec : Sections F ζ hζ U R P H := fun i =>
      ⟨fun x => if Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U)
          (x, (H.atlas U).representative i) ∈ E then (s.val i).val x else 0, by
        refine ⟨?_, ?_⟩
        · intro x
          by_cases hx : Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U)
              (x, (H.atlas U).representative i) ∈ E
          · dsimp only; rw [if_pos hx]; exact (s.val i).property.1 x
          · dsimp only; rw [if_neg hx]; exact (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).zero_mem
        · intro γ x
          have hq : Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U)
              ((γ : KPCuspArithmetic.PGL2 F) • x, (H.atlas U).representative i) =
              Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U)
                (x, (H.atlas U).representative i) := by
            obtain ⟨ε, u, hu⟩ := KPCuspGenuineMonodromy.finiteComparison_exists F ζ hζ U
              ((H.atlas U).representative i) γ
            refine Quotient.sound ⟨γ⁻¹, ε, u, by simp, ?_⟩
            calc (H.atlas U).representative i
                = (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ)⁻¹ *
                    (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ *
                      (H.atlas U).representative i) := by group
              _ = (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ)⁻¹ *
                    (KPCuspGenuineMonodromy.central F ζ hζ ε *
                      (H.atlas U).representative i * u) := by rw [hu]
              _ = KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ⁻¹ *
                    KPCuspGenuineMonodromy.central F ζ hζ ε *
                      (H.atlas U).representative i * u := by
                    rw [map_inv]; group
          by_cases hx : Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U)
              (x, (H.atlas U).representative i) ∈ E
          · dsimp only; rw [if_pos (hq ▸ hx), if_pos hx, (s.val i).property.2 γ x]
          · dsimp only; rw [if_neg (hq ▸ hx), if_neg hx, mul_zero]
      ⟩
    have hnorm : sectionNorm F ζ hζ U R P H tSec =
        E.indicator (sectionNorm F ζ hζ U R P H s.val) :=
      sectionNorm_indicator_of_coeff s.val tSec E (fun i x => rfl)
    have hmeas : ∀ i, Measurable (tSec i).val := by
      intro i
      have hcond : MeasurableSet {x : KPCuspGenuineMonodromy.SymmetricSpace F |
          Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U)
            (x, (H.atlas U).representative i) ∈ E} := by
        apply hE.preimage
        exact (continuous_quotient_mk'.comp
          (continuous_id.prodMk continuous_const)).measurable
      simpa only [tSec, Set.mem_setOf_eq] using
        Measurable.ite hcond (s.property.1 i) measurable_const
    have hle : ∀ b, squaredNorm F ζ hζ U R P H tSec b ≤
        squaredNorm F ζ hζ U R P H s.val b := by
      intro b
      have hL : E.indicator (sectionNorm F ζ hζ U R P H s.val) b ≤
          sectionNorm F ζ hζ U R P H s.val b := by
        by_cases h : b ∈ E
        · rw [Set.indicator_of_mem h]
        · rw [Set.indicator_of_notMem h]; exact sectionNorm_nonneg' s.val b
      have hL0 : 0 ≤ E.indicator (sectionNorm F ζ hζ U R P H s.val) b := by
        by_cases h : b ∈ E
        · rw [Set.indicator_of_mem h]; exact sectionNorm_nonneg' s.val b
        · rw [Set.indicator_of_notMem h]
      have h2 : (E.indicator (sectionNorm F ζ hζ U R P H s.val) b) ^ 2 ≤
          (sectionNorm F ζ hζ U R P H s.val b) ^ 2 := pow_le_pow_left₀ hL0 hL 2
      simp only [squaredNorm]
      rw [hnorm]
      exact ENNReal.ofReal_le_ofReal h2
    have hfin : normIntegral F ζ hζ U R P H tSec < ⊤ := by
      refine lt_of_le_of_lt ?_ s.property.2
      simp only [normIntegral]
      exact lintegral_mono hle
    refine ⟨⟨tSec, ⟨hmeas, hfin⟩⟩, ?_⟩
    refine ⟨fun i x => rfl, hnorm, ?_, ?_⟩
    ·
      have hcoeff : ∀ i x, ((s.val - tSec) i).val x =
          (if Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U)
              (x, (H.atlas U).representative i) ∈ E then 0 else (s.val i).val x) := by
        intro i x
        simp only [Pi.sub_apply, Submodule.coe_sub]
        by_cases h : Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U)
            (x, (H.atlas U).representative i) ∈ E
        · have ht : (tSec i).val x = (s.val i).val x := by
            simp only [tSec]; rw [if_pos h]
          rw [ht, sub_self, if_pos h]
        · have ht : (tSec i).val x = 0 := by
            simp only [tSec]; rw [if_neg h]
          rw [ht, sub_zero, if_neg h]
      exact squaredNorm_indicator_of_sectionNorm
        (sectionNorm_indicator_of_coeff_neg s.val (s.val - tSec) E hcoeff)
    · simp only [normIntegral]
      exact lintegral_mono hle
  · intro r
    let tFun : ChartFields F ζ hζ U R P H := fun a x =>
      if KPContCotangentOverlapRationalBranches.q a x.val ∈ E then r.val a x else 0
    have hisMeas : IsMeasurableCotangentFamily tFun := by
      refine ⟨?_, ?_, ?_⟩
      · intro a
        have hcond : MeasurableSet
            {x : KPContCotangentOverlapRationalBranches.omega a |
              KPContCotangentOverlapRationalBranches.q a x.val ∈ E} :=
          hE.preimage ((measurable_q a).comp measurable_subtype_coe)
        simpa only [tFun] using Measurable.ite hcond (r.property.1 a) measurable_const
      · intro a γ x hx
        have hq := q_isotropyArrow a γ x hx
        have hrc := r.property.2.1 a γ x hx
        by_cases hc : KPContCotangentOverlapRationalBranches.q a x ∈ E
        · have h1 : tFun a ⟨(isotropyArrow a γ).psi x, isotropy_mem a γ x hx⟩ =
              r.val a ⟨(isotropyArrow a γ).psi x, isotropy_mem a γ x hx⟩ := by
            simp only [tFun]; rw [if_pos (hq ▸ hc)]
          have h2 : tFun a ⟨x, hx⟩ = r.val a ⟨x, hx⟩ := by
            simp only [tFun]; rw [if_pos hc]
          rw [h1, h2, hrc]
        · have h1 : tFun a ⟨(isotropyArrow a γ).psi x, isotropy_mem a γ x hx⟩ = 0 := by
            simp only [tFun]; rw [if_neg (by rw [hq]; exact hc)]
          have h2 : tFun a ⟨x, hx⟩ = 0 := by
            simp only [tFun]; rw [if_neg hc]
          rw [h1, h2, map_zero]
      · intro a b e x hx
        have hq := q_actualBranch e x
        have hrc := r.property.2.2 a b e x hx
        by_cases hc : KPContCotangentOverlapRationalBranches.q a x ∈ E
        · have h1 : tFun b ⟨e.arrow.psi x, e.target_shrinking hx⟩ =
              r.val b ⟨e.arrow.psi x, e.target_shrinking hx⟩ := by
            simp only [tFun]; rw [if_pos (hq ▸ hc)]
          have h2 : tFun a ⟨x, e.source_shrinking hx⟩ =
              r.val a ⟨x, e.source_shrinking hx⟩ := by
            simp only [tFun]; rw [if_pos hc]
          rw [h1, h2, hrc]
        · have h1 : tFun b ⟨e.arrow.psi x, e.target_shrinking hx⟩ = 0 := by
            simp only [tFun]; rw [if_neg (by rw [hq]; exact hc)]
          have h2 : tFun a ⟨x, e.source_shrinking hx⟩ = 0 := by
            simp only [tFun]; rw [if_neg hc]
          rw [h1, h2, map_zero]
    let t : Family (U := U) (H := H) := ⟨tFun, hisMeas⟩
    have hnorm_sq : normSquare t = E.indicator (normSquare r) := by
      have huniq := (Classical.choose_spec (normSquare_descends t)).2
      exact (huniq _ (by
        refine ⟨(measurable_normSquare r).indicator hE, ?_⟩
        intro a x
        by_cases hc : KPContCotangentOverlapRationalBranches.q a x.val ∈ E
        · have ht : coefficient t a x = coefficient r a x := by
            simp only [coefficient, t, tFun]; rw [if_pos hc]
          rw [Set.indicator_of_mem hc, normSquare_chart r a x, ht]
        · have ht : coefficient t a x = 0 := by
            simp only [coefficient, t, tFun]; rw [if_neg hc]
          rw [Set.indicator_of_notMem hc, ht]; simp)).symm
    refine ⟨t, ?_⟩
    refine ⟨fun a x => rfl, hnorm_sq, ?_, ?_⟩
    · have huniq := (Classical.choose_spec (normSquare_descends (r - t))).2
      exact (huniq _ (by
        refine ⟨(measurable_normSquare r).indicator hE.compl, ?_⟩
        intro a x
        by_cases hc : KPContCotangentOverlapRationalBranches.q a x.val ∈ E
        · have ht : coefficient (r - t) a x = 0 := by
            have h2 : coefficient t a x = coefficient r a x := by
              simp only [coefficient, t, tFun]; rw [if_pos hc]
            simp only [coefficient, Pi.sub_apply, Submodule.coe_sub] at h2 ⊢
            rw [h2, sub_self]
          rw [Set.indicator_of_notMem (by simp [Set.mem_compl_iff, hc]), ht]; simp
        · have ht : coefficient (r - t) a x = coefficient r a x := by
            have h2 : coefficient t a x = 0 := by
              simp only [coefficient, t, tFun]; rw [if_neg hc]
            simp only [coefficient, Pi.sub_apply, Submodule.coe_sub] at h2 ⊢
            rw [h2, sub_zero]
          rw [Set.indicator_of_mem (by simp [Set.mem_compl_iff, hc]),
            normSquare_chart r a x, ht])).symm
    · apply lintegral_mono
      intro b
      apply ENNReal.ofReal_le_ofReal
      rw [hnorm_sq]
      by_cases h : b ∈ E
      · rw [Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h]; simp

def scalarIndicator (E : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U))
    (hE : MeasurableSet E) (s : BorelL2Sections F ζ hζ U R P H) :
    BorelL2Sections F ζ hζ U R P H :=
  Classical.choose ((indicator_truncation E hE).1 s)

def cotangentBorelIndicator (E : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U))
    (hE : MeasurableSet E) (r : Family (U := U) (H := H)) :
    Family (U := U) (H := H) :=
  Classical.choose ((indicator_truncation E hE).2 r)

theorem cotangentBorelIndicator_spec (E : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U))
    (hE : MeasurableSet E) (r : Family (U := U) (H := H)) :
    CotangentIndicatorSpec E r (cotangentBorelIndicator E hE r) :=
  Classical.choose_spec ((indicator_truncation E hE).2 r)

def cotangentIndicator (E : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U))
    (hE : MeasurableSet E) (r : SquareFiniteFamily (U := U) (H := H)) :
    SquareFiniteFamily (U := U) (H := H) :=
  ⟨cotangentBorelIndicator E hE r.val, by
    exact lt_of_le_of_lt (cotangentBorelIndicator_spec E hE r.val).integral_le r.property⟩

theorem scalarIndicator_spec (E : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U))
    (hE : MeasurableSet E) (s : BorelL2Sections F ζ hζ U R P H) :
    ScalarIndicatorSpec E s (scalarIndicator E hE s) :=
  Classical.choose_spec ((indicator_truncation E hE).1 s)

theorem cotangentIndicator_spec (E : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U))
    (hE : MeasurableSet E) (r : SquareFiniteFamily (U := U) (H := H)) :
    CotangentIndicatorSpec E r.val (cotangentIndicator E hE r).val :=
  cotangentBorelIndicator_spec E hE r.val

end DedekindZetaZeroFree.RepresentationTheory.ActualSectorTestDensity.CompactTailSources

end

end

section

noncomputable section
open scoped Classical NumberField ENNReal NNReal
open MeasureTheory Topology Filter

namespace DedekindZetaZeroFree.RepresentationTheory.ActualSectorTestDensity

namespace CompactTailSources

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContSectorLineL2Isometry KPContSectorSmoothFramesSupport
open KPContActualCotangentMeasurableFamilies

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

noncomputable def compactExhaustion :
    ℕ → Set (KPFiniteCuspAtlas.rawXU F ζ hζ U) :=
  compactCovering (KPFiniteCuspAtlas.rawXU F ζ hζ U)

theorem compactExhaustion_isCompact (n : ℕ) :
    IsCompact (compactExhaustion F ζ hζ U n) :=
  isCompact_compactCovering (KPFiniteCuspAtlas.rawXU F ζ hζ U) n

theorem compactExhaustion_measurable (n : ℕ) :
    MeasurableSet (compactExhaustion F ζ hζ U n) :=
  (compactExhaustion_isCompact F ζ hζ U n).isClosed.measurableSet

theorem compactExhaustion_monotone :
    Monotone (compactExhaustion F ζ hζ U) :=
  fun _ _ h => compactCovering_subset (KPFiniteCuspAtlas.rawXU F ζ hζ U) h

theorem compactExhaustion_covers :
    ⋃ n, compactExhaustion F ζ hζ U n = Set.univ :=
  iUnion_compactCovering (KPFiniteCuspAtlas.rawXU F ζ hζ U)

private theorem tendsto_indicator_compl_zero {α : Type*} (f : α → ℝ) (E : ℕ → Set α)
    (hmono : Monotone E) (hcov : ⋃ n, E n = Set.univ) (x : α) :
    Tendsto (fun n => (E n)ᶜ.indicator f x) atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨N, hN⟩ := Set.mem_iUnion.mp (by rw [hcov]; exact Set.mem_univ x)
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_atTop.mpr ⟨N, fun n hn => hmono hn hN⟩] with n hn
  exact (Set.indicator_of_notMem (s := (E n)ᶜ) (f := f) (show x ∉ (E n)ᶜ from fun h => h hn)).symm

private theorem antitone_indicator_compl {α : Type*} (f : α → ℝ) (hf0 : ∀ y, 0 ≤ f y)
    (E : ℕ → Set α) (hmono : Monotone E) (x : α) :
    Antitone fun n => (E n)ᶜ.indicator f x :=
  antitone_nat_of_succ_le fun n => by
    by_cases hx : x ∈ (E (n + 1))ᶜ
    · have hx' : x ∈ (E n)ᶜ := fun h => hx (hmono (Nat.le_succ n) h)
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
    · rw [Set.indicator_of_notMem hx]
      exact Set.indicator_nonneg (fun y _ => hf0 y) x

private theorem tendsto_setLIntegral_compl {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ≥0∞) (hf : AEMeasurable f μ) (E : ℕ → Set α)
    (hE : ∀ n, MeasurableSet (E n)) (hmono : Monotone E)
    (hcov : ⋃ n, E n = Set.univ) (hfin : ∫⁻ a, f a ∂μ ≠ ∞) :
    Tendsto (fun n => ∫⁻ a, (E n)ᶜ.indicator f a ∂μ) atTop (𝓝 0) := by
  have hmeas : ∀ n, AEMeasurable (fun a => (E n)ᶜ.indicator f a) μ :=
    fun n => hf.indicator (hE n).compl
  have hanti : ∀ᵐ x ∂μ, Antitone fun n => (E n)ᶜ.indicator f x :=
    Filter.Eventually.of_forall fun x => antitone_nat_of_succ_le fun n => by
      by_cases hx : x ∈ (E (n + 1))ᶜ
      · have hx' : x ∈ (E n)ᶜ := fun h => hx (hmono (Nat.le_succ n) h)
        rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
      · rw [Set.indicator_of_notMem hx]
        exact bot_le
  have h0 : ∫⁻ a, (E 0)ᶜ.indicator f a ∂μ ≠ ∞ :=
    ne_top_of_le_ne_top hfin (lintegral_mono fun a => Set.indicator_le_self _ _ a)
  have htend : ∀ᵐ x ∂μ, Tendsto (fun n => (E n)ᶜ.indicator f x) atTop (𝓝 0) :=
    Filter.Eventually.of_forall fun x => by
      obtain ⟨N, hN⟩ := Set.mem_iUnion.mp (by rw [hcov]; exact Set.mem_univ x)
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [Filter.eventually_atTop.mpr ⟨N, fun n hn => hmono hn hN⟩] with n hn
      exact (Set.indicator_of_notMem (s := (E n)ᶜ) (f := f) (show x ∉ (E n)ᶜ from fun h => h hn)).symm
  have := lintegral_tendsto_of_tendsto_of_antitone hmeas hanti h0 htend
  simpa using this

private theorem tendsto_setIntegral_compl {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (g : α → ℝ) (hg : Integrable g μ) (hg0 : ∀ y, 0 ≤ g y) (E : ℕ → Set α)
    (hE : ∀ n, MeasurableSet (E n)) (hmono : Monotone E)
    (hcov : ⋃ n, E n = Set.univ) :
    Tendsto (fun n => ∫ a, (E n)ᶜ.indicator g a ∂μ) atTop (𝓝 0) := by
  have hf : ∀ n, Integrable (fun a => (E n)ᶜ.indicator g a) μ :=
    fun n => hg.indicator (hE n).compl
  have hanti : ∀ᵐ x ∂μ, Antitone fun n => (E n)ᶜ.indicator g x :=
    Filter.Eventually.of_forall fun x => antitone_indicator_compl g hg0 E hmono x
  have htend : ∀ᵐ x ∂μ, Tendsto (fun n => (E n)ᶜ.indicator g x) atTop (𝓝 0) :=
    Filter.Eventually.of_forall fun x => tendsto_indicator_compl_zero g E hmono hcov x
  have := integral_tendsto_of_tendsto_of_antitone hf (integrable_zero α ℝ μ) hanti htend
  simpa using this

private theorem norm_eq_sqrt_of_sq_eq {E : Type*} [NormedAddCommGroup E] {x : E} {A : ℝ}
    (h : ‖x‖ ^ 2 = A) : ‖x‖ = Real.sqrt A := by
  rw [← h, Real.sqrt_sq (norm_nonneg x)]

private theorem toSector_norm_sq (s : BorelL2Sections F ζ hζ U R P H) :
    ‖toSector F ζ hζ U R P H s‖ ^ 2 =
      (normIntegral F ζ hζ U R P H s.val).toReal := by
  rw [← KPContSectorLineL2Isometry.norm_sq F ζ hζ U R P H s]
  rfl

private theorem ofFamily_norm_sq (r : SquareFiniteFamily (U := U) (H := H)) :
    ‖KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H r‖ ^ 2 =
      ∫ x, (normSquare r.val x : ℝ)
        ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U :=
  KPContActualCotangentIntrinsicHilbertIntegral.norm_sq_eq_integral
    (KPContActualSectorCotangentL2.chosenCover F ζ hζ U R P H)
    (KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H r) r rfl

private theorem coe_indicator (s : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U))
    (f : KPFiniteCuspAtlas.rawXU F ζ hζ U → NNReal)
    (x : KPFiniteCuspAtlas.rawXU F ζ hζ U) :
    ((s.indicator f x : NNReal) : ℝ) = s.indicator (fun y => (f y : ℝ)) x := by
  by_cases h : x ∈ s
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
    simp

theorem compact_indicator_norm_tendsto :
    (∀ s : BorelL2Sections F ζ hζ U R P H,
      Tendsto (fun n => ‖toSector F ζ hζ U R P H s -
        toSector F ζ hζ U R P H
          (scalarIndicator (compactExhaustion F ζ hζ U n)
            (compactExhaustion_measurable F ζ hζ U n) s)‖) atTop (𝓝 0)) ∧
    (∀ r : SquareFiniteFamily (U := U) (H := H),
      Tendsto (fun n => ‖KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H r -
        KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H
          (cotangentIndicator (compactExhaustion F ζ hζ U n)
            (compactExhaustion_measurable F ζ hζ U n) r)‖) atTop (𝓝 0)) := by
  constructor
  · intro s
    have hspec : ∀ n, ScalarIndicatorSpec (compactExhaustion F ζ hζ U n) s
        (scalarIndicator (compactExhaustion F ζ hζ U n)
          (compactExhaustion_measurable F ζ hζ U n) s) :=
      fun n => scalarIndicator_spec _ _ _
    have hconv : Tendsto (fun n => ∫⁻ b,
        ((compactExhaustion F ζ hζ U n)ᶜ).indicator
          (squaredNorm F ζ hζ U R P H s.val) b
        ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U) atTop (𝓝 0) :=
      tendsto_setLIntegral_compl _ _
        (squaredNorm_measurable F ζ hζ U R P H s.val s.property.1).aemeasurable
        (compactExhaustion F ζ hζ U) (compactExhaustion_measurable F ζ hζ U)
        (compactExhaustion_monotone F ζ hζ U) (compactExhaustion_covers F ζ hζ U)
        (ne_of_lt s.property.2)
    have ha : Tendsto (fun n => normIntegral F ζ hζ U R P H
        (s - scalarIndicator (compactExhaustion F ζ hζ U n)
          (compactExhaustion_measurable F ζ hζ U n) s).val) atTop (𝓝 0) := by
      refine hconv.congr' ?_
      filter_upwards with n
      simp only [normIntegral]
      rw [Submodule.coe_sub, ← (hspec n).error]
    have haR : Tendsto (fun n => (normIntegral F ζ hζ U R P H
        (s - scalarIndicator (compactExhaustion F ζ hζ U n)
          (compactExhaustion_measurable F ζ hζ U n) s).val).toReal) atTop (𝓝 0) :=
      (ENNReal.tendsto_toReal_zero_iff
        (fun n => ne_of_lt (s - scalarIndicator (compactExhaustion F ζ hζ U n)
          (compactExhaustion_measurable F ζ hζ U n) s).property.2)).mpr ha
    have hnorm : ∀ n, ‖toSector F ζ hζ U R P H s -
        toSector F ζ hζ U R P H
          (scalarIndicator (compactExhaustion F ζ hζ U n)
            (compactExhaustion_measurable F ζ hζ U n) s)‖ =
        Real.sqrt ((normIntegral F ζ hζ U R P H
          (s - scalarIndicator (compactExhaustion F ζ hζ U n)
            (compactExhaustion_measurable F ζ hζ U n) s).val).toReal) := by
      intro n
      have hlin : toSector F ζ hζ U R P H s -
          toSector F ζ hζ U R P H
            (scalarIndicator (compactExhaustion F ζ hζ U n)
              (compactExhaustion_measurable F ζ hζ U n) s) =
          toSector F ζ hζ U R P H (s - scalarIndicator (compactExhaustion F ζ hζ U n)
            (compactExhaustion_measurable F ζ hζ U n) s) :=
        (map_sub (toSector F ζ hζ U R P H) s _).symm
      rw [hlin]
      exact norm_eq_sqrt_of_sq_eq (toSector_norm_sq F ζ hζ U R P H _)
    have := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp haR
    simpa only [Real.sqrt_zero, Function.comp_def, hnorm] using this
  · intro r
    have hspec : ∀ n, CotangentIndicatorSpec (compactExhaustion F ζ hζ U n) r.val
        (cotangentIndicator (compactExhaustion F ζ hζ U n)
          (compactExhaustion_measurable F ζ hζ U n) r).val :=
      fun n => cotangentIndicator_spec _ _ _
    have hconv : Tendsto (fun n => ∫ x,
        ((compactExhaustion F ζ hζ U n)ᶜ).indicator
          (fun b => (normSquare r.val b : ℝ)) x
        ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U) atTop (𝓝 0) :=
      tendsto_setIntegral_compl _ _
        (KPContActualCotangentIntrinsicHilbertIntegral.integrable_normSquare r)
        (fun b => NNReal.coe_nonneg _)
        (compactExhaustion F ζ hζ U) (compactExhaustion_measurable F ζ hζ U)
        (compactExhaustion_monotone F ζ hζ U) (compactExhaustion_covers F ζ hζ U)
    have ha : Tendsto (fun n => ∫ x,
        (normSquare (r - cotangentIndicator (compactExhaustion F ζ hζ U n)
          (compactExhaustion_measurable F ζ hζ U n) r).val x : ℝ)
        ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U) atTop (𝓝 0) := by
      refine hconv.congr' ?_
      filter_upwards with n
      apply integral_congr_ae
      filter_upwards with x
      rw [← coe_indicator F ζ hζ U ((compactExhaustion F ζ hζ U n)ᶜ) (normSquare r.val) x]
      rw [Submodule.coe_sub]
      exact congrArg (fun v : NNReal => (v : ℝ)) (congrFun (hspec n).error x).symm
    have hnorm : ∀ n, ‖KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H r -
        KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H
          (cotangentIndicator (compactExhaustion F ζ hζ U n)
            (compactExhaustion_measurable F ζ hζ U n) r)‖ =
        Real.sqrt (∫ x, (normSquare
          (r - cotangentIndicator (compactExhaustion F ζ hζ U n)
            (compactExhaustion_measurable F ζ hζ U n) r).val x : ℝ)
          ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U) := by
      intro n
      have hlin : KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H r -
          KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H
            (cotangentIndicator (compactExhaustion F ζ hζ U n)
              (compactExhaustion_measurable F ζ hζ U n) r) =
          KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H
            (r - cotangentIndicator (compactExhaustion F ζ hζ U n)
              (compactExhaustion_measurable F ζ hζ U n) r) :=
        (map_sub (KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H) r _).symm
      rw [hlin]
      exact norm_eq_sqrt_of_sq_eq (ofFamily_norm_sq F ζ hζ U R P H _)
    have := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp ha
    simpa only [Real.sqrt_zero, Function.comp_def, hnorm] using this

end CompactTailSources

end DedekindZetaZeroFree.RepresentationTheory.ActualSectorTestDensity

end

end

section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.RepresentationTheory.ActualSectorTestDensity

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContSectorLineL2Isometry KPContSectorSmoothFramesSupport
open KPContActualCotangentMeasurableFamilies

theorem compact_tail
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (v : KPContActualSectorCotangentL2.V F ζ hζ U R P H)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)),
      IsCompact K ∧ MeasurableSet K ∧
      ∃ (s : BorelL2Sections F ζ hζ U R P H)
        (r : SquareFiniteFamily (U := U) (H := H)),
        (∀ᵐ b ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U,
          b ∉ K → sectionNorm F ζ hζ U R P H s.val b = 0) ∧
        (∀ᵐ b ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U,
          b ∉ K → normSquare r.val b = 0) ∧
        ‖u - toSector F ζ hζ U R P H s‖ < ε ∧
        ‖v - KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H r‖ < ε := by
  classical

  obtain ⟨g, hg, hgLp, hgu, f, hf, hfLp, hfg, hfu, hfeq, _⟩ :=
    KPContSectorExactBorelRepresentatives.exists_exact_borel_representative F ζ hζ R U u
  let f₀ : KPContSectorScalarLineAlgebra.GenuineCoveredScalars F ζ hζ U := ⟨f, hfeq⟩
  let f₁ : BorelL2Scalars F ζ hζ U R := ⟨f₀, hf, hfLp⟩
  let s₀ := borelS F ζ hζ U R P H f₁
  have hsu : toSector F ζ hζ U R P H s₀ = u := by
    apply Subtype.ext
    exact (scalarEmbedding_coe F ζ hζ U R P H f₁).trans hfu
  obtain ⟨r₀, hrv⟩ := KPContActualSectorCotangentL2.ofFamily_surjective F ζ hζ U R P H v
  obtain ⟨hs, hr⟩ := CompactTailSources.compact_indicator_norm_tendsto F ζ hζ U R P H
  have hsε := (hs s₀).eventually_lt_const hε
  have hrε := (hr r₀).eventually_lt_const hε
  obtain ⟨n, hsn, hrn⟩ := (hsε.and hrε).exists
  let K := CompactTailSources.compactExhaustion F ζ hζ U n
  have hK : MeasurableSet K := CompactTailSources.compactExhaustion_measurable F ζ hζ U n
  let s := CompactTailSources.scalarIndicator K hK s₀
  let r := CompactTailSources.cotangentIndicator K hK r₀
  refine ⟨K, CompactTailSources.compactExhaustion_isCompact F ζ hζ U n, hK, s, r,
    ?_, ?_, ?_, ?_⟩
  · exact Filter.Eventually.of_forall (fun b hb => by
      rw [(CompactTailSources.scalarIndicator_spec K hK s₀).norm]
      exact Set.indicator_of_notMem hb _)
  · exact Filter.Eventually.of_forall (fun b hb => by
      rw [(CompactTailSources.cotangentIndicator_spec K hK r₀).norm]
      exact Set.indicator_of_notMem hb _)
  · simpa only [hsu] using hsn
  · simpa only [hrv] using hrn

end DedekindZetaZeroFree.RepresentationTheory.ActualSectorTestDensity

end

end
