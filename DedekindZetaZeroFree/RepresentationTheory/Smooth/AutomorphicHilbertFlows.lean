module

public import DedekindZetaZeroFree.Adeles.Quotients.ArchimedeanFiniteProduct
public import DedekindZetaZeroFree.Eisenstein.Induction.HolomorphicSectionsAndResidueGerms
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.PGLComplex.ExponentialCoordinates

@[expose] public section

section
noncomputable section
namespace DedekindZetaZeroFree.KPSmoothQuotientTranslationFlow
open NumberField
open scoped Classical
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 def rawSection (v : InfinitePlace F) :
    Matrix.GeneralLinearGroup (Fin 2) ℂ →* KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl v) where
  toFun g := KPLocalCover.sectionMap F ζ hζ (Sum.inl v)
    (Matrix.GeneralLinearGroup.map
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ v)).symm.toRingHom g)
  map_one' := by simp [KPLocalCover.sectionMap]; rfl
  map_mul' := by
    intro g h
    change KPLocalCover.CubicGL2Raw.mk _ 1 = KPLocalCover.CubicGL2Raw.mk _ _
    congr 1
    · simp
    · simp [KPLocalChartTopology.complex_sigmaTwo_eq_one]

 theorem scalar_killed (v : InfinitePlace F) (u : ℂˣ) :
    KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inl v)
        (rawSection F ζ hζ v (Matrix.GeneralLinearGroup.scalar (Fin 2) u))) = 1 := by
  obtain ⟨j, _, _, hj⟩ := KPAdelicCoverRestrictedProduct.local_pgl_injection F ζ hζ (Sum.inl v)
  rw [← hj]
  have h : KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl v)
      (rawSection F ζ hζ v (Matrix.GeneralLinearGroup.scalar (Fin 2) u)) = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    refine ⟨Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ v)).symm.toRingHom u, ?_⟩
    simp [rawSection, KPScalarSplitCentral.scalarHom, KPScalarSplitCentral.scalarLift,
      KPScalarSplitCentral.scalarMatrix, Matrix.GeneralLinearGroup.map_scalar]
  rw [h, map_one]

 def localHom (v : InfinitePlace F) :
    Matrix.ProjGenLinGroup (Fin 2) ℂ →* ActualQuotient.actualCover F ζ hζ :=
  Matrix.ProjGenLinGroup.lift
    ((KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ).comp
      ((KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inl v)).comp
        (rawSection F ζ hζ v)))
    (by ext u; exact scalar_killed F ζ hζ v u)

theorem insertion_representative (r : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    RepresentationTheory.ArchFiniteSplitting.insertion F ζ hζ (fun v => Matrix.ProjGenLinGroup.mk (r v)) =
      ((Finset.univ : Finset (InfinitePlace F)).toList.map fun v =>
        KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
          (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inl v)
            (KPLocalCover.sectionMap F ζ hζ (Sum.inl v)
              (Matrix.GeneralLinearGroup.map
                (InfinitePlace.Completion.ringEquivComplexOfIsComplex
                  (KPHilbert.infinite_isComplex F ζ hζ v)).symm.toRingHom (r v))))).prod := by
  unfold RepresentationTheory.ArchFiniteSplitting.insertion
  congr 1
  apply List.map_congr_left
  intro v hv
  change ((KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ).comp
    ((KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inl v)).comp
      (rawSection F ζ hζ v))) (Matrix.ProjGenLinGroup.mk (r v)).out = _
  have hh : ∀ g, localHom F ζ hζ v g =
      ((KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ).comp
        ((KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inl v)).comp
          (rawSection F ζ hζ v))) g.out := by
    intro g
    conv_lhs => rw [← Quotient.out_eq g]
    rfl
  rw [← hh]
  rfl
end DedekindZetaZeroFree.KPSmoothQuotientTranslationFlow

end

end

section

noncomputable section

open MeasureTheory NumberField
open scoped NumberField Matrix ContDiff Manifold Classical Matrix.Norms.Operator ENNReal

namespace DedekindZetaZeroFree.KPSmoothActualFlowData

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev G := KPCubicCoverConstruction.AdelicPGL2Cover F ζ hζ

instance groupMeasurableSpace : MeasurableSpace (G F ζ hζ) := borel _

def rationalSubgroup : Subgroup (G F ζ hζ) :=
  (KPRationalAdelicSplitting.rationalPGLHom F ζ hζ).range

abbrev X := Quotient (QuotientGroup.rightRel (rationalSubgroup F ζ hζ))

instance quotientMeasurableSpace : MeasurableSpace (X F ζ hζ) := borel _

abbrev GInfinity := InfinitePlace F → Matrix.ProjGenLinGroup (Fin 2) ℂ

abbrev B := InfinitePlace F × Fin 6

abbrev LieCoordinates := B F → ℝ

def sl2Matrix (a : Fin 6 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(a 0 : ℂ) + Complex.I * (a 1 : ℂ), (a 2 : ℂ) + Complex.I * (a 3 : ℂ);
     (a 4 : ℂ) + Complex.I * (a 5 : ℂ), -((a 0 : ℂ) + Complex.I * (a 1 : ℂ))]

def matrixExponential (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.GeneralLinearGroup (Fin 2) ℂ :=
  (NormedSpace.isUnit_exp M).unit

def exponential (a : LieCoordinates F) : GInfinity F := fun v =>
  Matrix.ProjGenLinGroup.mk (matrixExponential (sl2Matrix (fun j => a (v, j))))

def flow (b : B F) (t : ℝ) : GInfinity F :=
  exponential F (fun c => if c = b then t else 0)

def archimedeanInsertion (g : GInfinity F) : G F ζ hζ :=
  ((Finset.univ : Finset (InfinitePlace F)).toList.map fun v =>
    KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inl v)
        (KPLocalCover.sectionMap F ζ hζ (Sum.inl v)
          (Matrix.GeneralLinearGroup.map
            (InfinitePlace.Completion.ringEquivComplexOfIsComplex
              (KPHilbert.infinite_isComplex F ζ hζ v)).symm.toRingHom (g v).out)))).prod

theorem archimedean_insertion_properties :
    archimedeanInsertion F ζ hζ 1 = 1 ∧
    (∀ g h, archimedeanInsertion F ζ hζ (g * h) =
      archimedeanInsertion F ζ hζ g * archimedeanInsertion F ζ hζ h) ∧
    Continuous (archimedeanInsertion F ζ hζ) ∧
    Function.Injective (archimedeanInsertion F ζ hζ) ∧
    ∀ r : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ,
      archimedeanInsertion F ζ hζ (fun v => Matrix.ProjGenLinGroup.mk (r v)) =
        ((Finset.univ : Finset (InfinitePlace F)).toList.map fun v =>
          KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
            (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inl v)
              (KPLocalCover.sectionMap F ζ hζ (Sum.inl v)
                (Matrix.GeneralLinearGroup.map
                  (InfinitePlace.Completion.ringEquivComplexOfIsComplex
                    (KPHilbert.infinite_isComplex F ζ hζ v)).symm.toRingHom (r v))))).prod := by
  obtain ⟨s, hs⟩ := RepresentationTheory.ArchFiniteSplitting.insertion_hom F ζ hζ
  have hi : Function.Injective (archimedeanInsertion F ζ hζ) := by
    have hleft : Function.LeftInverse (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ)
        (archimedeanInsertion F ζ hζ) :=
      PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion F ζ hζ
    exact hleft.injective
  refine ⟨?_, ?_, (RepresentationTheory.ArchFiniteSplitting.splitting_maps_continuous F ζ hζ).1,
    hi, KPSmoothQuotientTranslationFlow.insertion_representative F ζ hζ⟩
  · change RepresentationTheory.ArchFiniteSplitting.insertion F ζ hζ 1 = 1
    rw [← hs, map_one]
  · intro g h
    change RepresentationTheory.ArchFiniteSplitting.insertion F ζ hζ (g * h) =
      RepresentationTheory.ArchFiniteSplitting.insertion F ζ hζ g *
        RepresentationTheory.ArchFiniteSplitting.insertion F ζ hζ h
    rw [← hs, ← hs, ← hs, map_mul]

end DedekindZetaZeroFree.KPSmoothActualFlowData

end

end

section

noncomputable section
open MeasureTheory Topology
open scoped ContDiff ENNReal
namespace DedekindZetaZeroFree.KPSmoothQuotientTranslationFlow

theorem scalar_orbit_derivative {Y : Type*} (q : ℝ → Y → Y)
    (hadd : ∀ s t x, q (s + t) x = q t (q s x)) (f : Y → ℂ)
    (hsm : ∀ x, ContDiff ℝ (⊤ : ℕ∞) (fun t => f (q t x))) (x : Y) (t : ℝ) :
    HasDerivAt (fun s => f (q s x))
      (deriv (fun s => f (q s (q t x))) 0) t := by
  have hd := ((hsm (q t x)).differentiable (by simp)).differentiableAt (x := (0 : ℝ))
  have hd0 : HasDerivAt (fun s => f (q s (q t x)))
      (deriv (fun s => f (q s (q t x))) 0) (t - t) := by
    rw [sub_self]
    exact hd.hasDerivAt
  convert hd0.comp_sub_const t t using 1
  funext s
  rw [← hadd, add_sub_cancel]

end DedekindZetaZeroFree.KPSmoothQuotientTranslationFlow

end
end

section

noncomputable section
namespace DedekindZetaZeroFree.KPSmoothQuotientTranslationFlow
open MeasureTheory Topology
open scoped ENNReal
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (Γ : Subgroup G)

abbrev LeftQuotient := Quotient (QuotientGroup.rightRel Γ)

def rightTranslation (g : G) : LeftQuotient Γ → LeftQuotient Γ :=
  Quotient.map (fun a => a * g) (by
    intro a b hab
    apply QuotientGroup.rightRel_apply.mpr
    have hab' := QuotientGroup.rightRel_apply.mp hab
    simpa only [mul_inv_rev, mul_assoc, mul_inv_cancel_left] using hab')

theorem rightTranslation_one : rightTranslation Γ 1 = id := by
  funext x
  induction x using Quotient.inductionOn with
  | h a => exact congrArg Quotient.mk'' (mul_one a)

theorem rightTranslation_mul (g h : G) :
    rightTranslation Γ (g * h) = rightTranslation Γ h ∘ rightTranslation Γ g := by
  funext x
  induction x using Quotient.inductionOn with
  | h a => exact congrArg Quotient.mk'' (mul_assoc a g h).symm

def inversionHomeomorph : LeftQuotient Γ ≃ₜ (G ⧸ Γ) where
  __ := QuotientGroup.quotientRightRelEquivQuotientLeftRel Γ
  continuous_toFun := continuous_inv.quotient_map' (by
    intro a b h
    rw [QuotientGroup.leftRel_apply, QuotientGroup.rightRel_apply] at *
    simpa only [mul_inv_rev, inv_inv] using Γ.inv_mem h)
  continuous_invFun := continuous_inv.quotient_map' (by
    intro a b h
    rw [QuotientGroup.leftRel_apply, QuotientGroup.rightRel_apply] at *
    simpa only [mul_inv_rev, inv_inv] using Γ.inv_mem h)

theorem continuous_rightTranslation :
    Continuous (fun p : G × LeftQuotient Γ => rightTranslation Γ p.1 p.2) := by
  have hh : Continuous (fun p : G × LeftQuotient Γ =>
      p.1⁻¹ • inversionHomeomorph Γ p.2) :=
    continuous_fst.inv.smul ((inversionHomeomorph Γ).continuous.comp continuous_snd)
  convert (inversionHomeomorph Γ).symm.continuous.comp hh using 1
  funext p
  rcases p with ⟨g, x⟩
  induction x using Quotient.inductionOn with
  | h a =>
    simp [rightTranslation, inversionHomeomorph,
      QuotientGroup.quotientRightRelEquivQuotientLeftRel]

variable [MeasurableSpace (LeftQuotient Γ)] [BorelSpace (LeftQuotient Γ)]
  (μ : Measure (LeftQuotient Γ))
  (hμ : ∀ g, MeasurePreserving (rightTranslation Γ g) μ μ)

def translationIsometry (g : G) : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
  { Lp.compMeasurePreservingₗᵢ ℂ (rightTranslation Γ g) (hμ g) with
    invFun := Lp.compMeasurePreserving (rightTranslation Γ g⁻¹) (hμ g⁻¹)
    left_inv := by
      intro f
      change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
      rw [← Lp.compMeasurePreserving_comp_apply]
      have he : rightTranslation Γ g ∘ rightTranslation Γ g⁻¹ = id := by
        rw [← rightTranslation_mul, inv_mul_cancel, rightTranslation_one]
      simpa only [he] using Lp.compMeasurePreserving_id_apply f
    right_inv := by
      intro f
      change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
      rw [← Lp.compMeasurePreserving_comp_apply]
      have he : rightTranslation Γ g⁻¹ ∘ rightTranslation Γ g = id := by
        rw [← rightTranslation_mul, mul_inv_cancel, rightTranslation_one]
      simpa only [he] using Lp.compMeasurePreserving_id_apply f }

def translationHom : G →* (Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ) where
  toFun := translationIsometry Γ μ hμ
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro f
    change Lp.compMeasurePreserving (rightTranslation Γ 1) (hμ 1) f = f
    simpa only [rightTranslation_one] using Lp.compMeasurePreserving_id_apply f
  map_mul' g h := by
    apply LinearIsometryEquiv.ext
    intro f
    change Lp.compMeasurePreserving (rightTranslation Γ (g * h)) (hμ (g * h)) f =
      Lp.compMeasurePreserving (rightTranslation Γ g) (hμ g)
        (Lp.compMeasurePreserving (rightTranslation Γ h) (hμ h) f)
    rw [← Lp.compMeasurePreserving_comp_apply]
    simp only [rightTranslation_mul Γ g h]

theorem quotient_unitary_action (hμ : ∀ g, MeasurePreserving (rightTranslation Γ g) μ μ)
    (hΓ : IsClosed (Γ : Set G))
    [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure μ] :
    ∃ π : StronglyContinuousHilbertRepresentation
      (G := G) (H := Lp ℂ 2 μ),
      ∀ g f, (π.operator g f : LeftQuotient Γ → ℂ) =ᵐ[μ]
        fun x => f (rightTranslation Γ g x) := by
  have hq : IsOpenQuotientMap (Quotient.mk'' : G → LeftQuotient Γ) := by
    have he : (Quotient.mk'' : G → LeftQuotient Γ) =
        (inversionHomeomorph Γ).symm ∘ (QuotientGroup.mk ∘ Inv.inv) := by
      funext g
      simp [inversionHomeomorph, QuotientGroup.quotientRightRelEquivQuotientLeftRel]
    rw [he]
    exact (inversionHomeomorph Γ).symm.isOpenQuotientMap.comp
      ((QuotientGroup.isOpenQuotientMap_mk (N := Γ)).comp
        (Homeomorph.inv G).isOpenQuotientMap)
  haveI : T2Space (LeftQuotient Γ) :=
    (t2Space_iff_of_isOpenQuotientMap hq).mpr (by
      convert hΓ.preimage (continuous_snd.mul continuous_fst.inv) using 1
      ext p
      exact Quotient.eq.trans (QuotientGroup.rightRel_apply (s := Γ)))
  refine ⟨{ operator := translationHom Γ μ hμ, strongly_continuous := ?_ }, ?_⟩
  · intro f
    let c : C(G × LeftQuotient Γ, LeftQuotient Γ) :=
      ⟨_, continuous_rightTranslation Γ⟩
    exact (continuous_const.compMeasurePreservingLp c.curry.continuous hμ (by simp))
  · intro g f
    exact Lp.coeFn_compMeasurePreserving f (hμ g)

end DedekindZetaZeroFree.KPSmoothQuotientTranslationFlow

end
end

section

noncomputable section

open MeasureTheory NumberField
open scoped NumberField Matrix ContDiff Manifold Classical Matrix.Norms.Operator ENNReal

namespace DedekindZetaZeroFree.KPSmoothActualFlowData

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def rightTranslate (g : G F ζ hζ) : X F ζ hζ → X F ζ hζ :=
  Quotient.map (fun a => a * g) (by
    intro a b hab
    apply QuotientGroup.rightRel_apply.mpr
    have hab' := QuotientGroup.rightRel_apply.mp hab
    simpa only [mul_inv_rev, mul_assoc, mul_inv_cancel_left] using hab')

abbrev H (μ : Measure (X F ζ hζ)) := Lp ℂ 2 μ

structure QuotientMeasureData where

  ambientHaar : Measure (G F ζ hζ)
  ambientHaarIsHaar : ambientHaar.IsHaarMeasure

  measure : Measure (X F ζ hζ)
  regular : measure.Regular
  finiteOnCompacts : IsFiniteMeasureOnCompacts measure
  openPositive : measure.IsOpenPosMeasure
  rightInvariant : ∀ g : G F ζ hζ,
    MeasurePreserving (rightTranslate F ζ hζ g) measure measure

  unfolding : ∀ φ : G F ζ hζ → ℝ≥0∞, Measurable φ →
    (∫⁻ g, φ g ∂ambientHaar) =
      ∫⁻ x : X F ζ hζ,
        ∑' γ : KPRationalAdelicSplitting.RationalPGL2 F,
          φ (KPRationalAdelicSplitting.rationalPGLHom F ζ hζ γ *
            (Quotient.out x)) ∂measure

theorem actual_quotient_unitary_action (μ : QuotientMeasureData F ζ hζ) :
    ∃ π : StronglyContinuousHilbertRepresentation
      (G := G F ζ hζ) (H := H F ζ hζ μ.measure),
      ∀ (g : G F ζ hζ) (f : H F ζ hζ μ.measure),
        (π.operator g f : X F ζ hζ → ℂ) =ᵐ[μ.measure]
          fun x => f (rightTranslate F ζ hζ g x) := by
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  letI := μ.regular
  letI := μ.finiteOnCompacts
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.1
  haveI : BorelSpace (X F ζ hζ) := ⟨rfl⟩
  haveI : WeaklyLocallyCompactSpace (X F ζ hζ) := by
    let e := KPSmoothQuotientTranslationFlow.inversionHomeomorph (rationalSubgroup F ζ hζ)
    exact e.symm.isOpenQuotientMap.weaklyLocallyCompactSpace
  exact KPSmoothQuotientTranslationFlow.quotient_unitary_action
    (rationalSubgroup F ζ hζ) μ.measure μ.rightInvariant
    (ActualQuotient.actual_rational_closed_discrete F ζ hζ).1

def basisMatrix (j : Fin 6) : Matrix (Fin 2) (Fin 2) ℂ :=
  sl2Matrix (fun k => if k = j then 1 else 0)

def matrixCoordinates (M : Matrix (Fin 2) (Fin 2) ℂ) : Fin 6 → ℝ :=
  ![(M 0 0).re, (M 0 0).im, (M 0 1).re, (M 0 1).im, (M 1 0).re, (M 1 0).im]

def adjointMatrix (g : GInfinity F) : Matrix (B F) (B F) ℝ := fun a b =>
  if a.1 = b.1 then matrixCoordinates
    ((g a.1).out.val * basisMatrix b.2 * (g a.1).out⁻¹.val) a.2 else 0

theorem actual_archimedean_lie_data :
    ∃ C : ChartedSpace (LieCoordinates F) (GInfinity F),
      letI := C
      ∃ L : LieGroup (𝓘(ℝ, LieCoordinates F)) (↑(⊤ : ℕ∞) : ℕ∞ω) (GInfinity F),
        letI := L
        ∃ D : HilbertLieExponentialData (GInfinity F) (LieCoordinates F) (B F),
          D.exponential = exponential F ∧
          (∀ b c : B F, D.basis b c = if c = b then 1 else 0) ∧
          (∀ (g : GInfinity F) (a b : B F),
            D.basis.equivFun (D.adjoint g (D.basis b)) a = adjointMatrix F g a b) := by
  exact PGLComplex.product_lie_exponential_data (InfinitePlace F)

theorem flow_properties (b : B F) :
    flow F b 0 = 1 ∧
    (∀ s t, flow F b (s + t) = flow F b s * flow F b t) ∧
    Continuous (flow F b) := by
  have hr (t : ℝ) : (fun c : B F => if c = b then t else 0) =
      t • (fun c : B F => if c = b then (1 : ℝ) else 0) := by
    funext c
    simp only [Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  refine ⟨?_, ?_, ?_⟩
  · unfold flow
    rw [hr, zero_smul]
    exact PGLComplex.productExponential_zero (InfinitePlace F)
  · intro s t
    unfold flow
    rw [hr (s + t), hr s, hr t]
    exact PGLComplex.productExponential_add_ray (InfinitePlace F)
        (fun c : B F => if c = b then (1 : ℝ) else 0) s t
  · have hc : Continuous (exponential F) := by
      change Continuous (PGLComplex.productExponential (InfinitePlace F))
      exact continuous_pi fun v => PGLComplex.exponential_continuous.comp
        (continuous_pi fun j => continuous_apply (v, j))
    unfold flow
    have hcoords : Continuous (fun t : ℝ => fun c : B F => if c = b then t else 0) := by
      apply continuous_pi
      intro c
      by_cases h : c = b
      · simp only [h, if_true]
        exact continuous_id
      · simp only [h, if_false]
        exact continuous_const
    exact hc.comp hcoords

def pi (μ : QuotientMeasureData F ζ hζ) :
    StronglyContinuousHilbertRepresentation
      (G := G F ζ hζ) (H := H F ζ hζ μ.measure) :=
  (actual_quotient_unitary_action F ζ hζ μ).choose

def flowGroups (μ : QuotientMeasureData F ζ hζ) :
    HilbertOneParameterGroups (H F ζ hζ μ.measure) (B F) where
  operator b t := (pi F ζ hζ μ).operator
    (archimedeanInsertion F ζ hζ (flow F b t))
  operator_zero b := by
    rw [(flow_properties F b).1, (archimedean_insertion_properties F ζ hζ).1, map_one]
  operator_add b s t := by
    rw [(flow_properties F b).2.1, (archimedean_insertion_properties F ζ hζ).2.1,
      map_mul]
  strongly_continuous b v := by
    exact ((pi F ζ hζ μ).strongly_continuous v).comp
      ((archimedean_insertion_properties F ζ hζ).2.2.1.comp
        (flow_properties F b).2.2)

def SmoothAutomorphic (f : X F ζ hζ → ℂ) : Prop :=
  Continuous f ∧ ∀ x : X F ζ hζ,
    ContDiff ℝ (⊤ : ℕ∞) (fun a : LieCoordinates F =>
      f (rightTranslate F ζ hζ (archimedeanInsertion F ζ hζ (exponential F a)) x))

def flowDerivative (b : B F) (f : X F ζ hζ → ℂ) : X F ζ hζ → ℂ := fun x =>
  deriv (fun t : ℝ =>
    f (rightTranslate F ζ hζ (archimedeanInsertion F ζ hζ (flow F b t)) x)) 0

def wordDerivative : List (B F) → (X F ζ hζ → ℂ) → X F ζ hζ → ℂ
  | [], f => f
  | b :: w, f => flowDerivative F ζ hζ b (wordDerivative w f)

end DedekindZetaZeroFree.KPSmoothActualFlowData

end
end
