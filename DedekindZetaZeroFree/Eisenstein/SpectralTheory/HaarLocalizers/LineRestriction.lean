module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSector.TestFriedrichsRealization

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 100000
open scoped Classical NumberField ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualFixedHaarCoreLocalizers

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContSectorLineL2Isometry KPContSectorSmoothFramesSupport

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

abbrev X_U := KPFiniteCuspAtlas.rawXU F ζ hζ U
abbrev H_U := KPContSectorClosedLpSubspace.H F ζ hζ R U
abbrev muU := KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U

attribute [local instance 5000] KPContSectorLineL2Isometry.instNormedAddCommGroupL2Line
attribute [local instance 5000] KPContSectorLineL2Isometry.instNormedSpaceL2Line
attribute [local instance 5000] KPContSectorLineL2Isometry.instInnerProductSpaceL2Line

 abbrev instTopologicalSpaceL2LineLocal : TopologicalSpace (L2Line F ζ hζ U R P H) :=
  (KPContSectorLineL2Isometry.instNormedAddCommGroupL2Line F ζ hζ U R P H).toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

attribute [local instance 5000] instTopologicalSpaceL2LineLocal

 abbrev instAddCommMonoidL2LineLocal : AddCommMonoid (L2Line F ζ hζ U R P H) :=
  (KPContSectorLineL2Isometry.instNormedAddCommGroupL2Line F ζ hζ U R P H).toSeminormedAddCommGroup.toAddCommMonoid

attribute [local instance 5000] instAddCommMonoidL2LineLocal

 abbrev instTopologicalSpaceHULocal : TopologicalSpace (H_U F ζ hζ U R) :=
  (inferInstance : NormedAddCommGroup (H_U F ζ hζ U R)).toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

attribute [local instance 5000] instTopologicalSpaceHULocal

variable (K : Set (X_U F ζ hζ U))

private theorem componentNorm_nonneg (s : Sections F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount)
    (b : KPCuspSiegel.OrbitQuotient F
      (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))) :
    0 ≤ componentNorm F ζ hζ U R P H s i b := by
  refine Quotient.inductionOn b (fun x => ?_)
  simp only [componentNorm, Quotient.lift_mk]
  exact norm_nonneg _

 theorem sectionNorm_nonneg (s : Sections F ζ hζ U R P H)
    (b : X_U F ζ hζ U) : 0 ≤ sectionNorm F ζ hζ U R P H s b := by
  simp only [sectionNorm]
  exact componentNorm_nonneg F ζ hζ U R P H s _ _

private theorem componentNorm_add_le (s t : Sections F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount)
    (b : KPCuspSiegel.OrbitQuotient F
      (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))) :
    componentNorm F ζ hζ U R P H (s + t) i b ≤
      componentNorm F ζ hζ U R P H s i b + componentNorm F ζ hζ U R P H t i b := by
  refine Quotient.inductionOn b (fun x => ?_)
  simp only [componentNorm, Quotient.lift_mk]
  rw [show ((s + t) i).val x = (s i).val x + (t i).val x from rfl]
  exact norm_add_le _ _

 theorem sectionNorm_add_le (s t : Sections F ζ hζ U R P H) :
    sectionNorm F ζ hζ U R P H (s + t) ≤
      sectionNorm F ζ hζ U R P H s + sectionNorm F ζ hζ U R P H t := by
  intro b
  simp only [sectionNorm]
  exact componentNorm_add_le F ζ hζ U R P H s t _ _

 theorem sectionNorm_smul (c : ℂ) (s : Sections F ζ hζ U R P H) :
    sectionNorm F ζ hζ U R P H (c • s) =
      fun b => ‖c‖ * sectionNorm F ζ hζ U R P H s b := by
  funext b
  simp only [sectionNorm]
  refine Quotient.inductionOn ((H.atlas U).components.symm b).2 (fun x => ?_)
  simp only [componentNorm, Quotient.lift_mk]
  rw [show ((c • s) ((H.atlas U).components.symm b).1).val x =
    c * (s ((H.atlas U).components.symm b).1).val x from rfl]
  exact norm_mul _ _

 theorem sectionNorm_zero_of_squaredNorm_ae
    {ν : Measure (X_U F ζ hζ U)} {s : Sections F ζ hζ U R P H}
    (h : squaredNorm F ζ hζ U R P H s =ᵐ[ν] 0) :
    sectionNorm F ζ hζ U R P H s =ᵐ[ν] 0 := by
  filter_upwards [h] with b hb
  simp only [Pi.zero_apply] at hb
  have hb' : sectionNorm F ζ hζ U R P H s b ^ 2 ≤ 0 := by
    rw [squaredNorm, ENNReal.ofReal_eq_zero] at hb
    exact hb
  have hzero : sectionNorm F ζ hζ U R P H s b ^ 2 = 0 :=
    le_antisymm hb' (sq_nonneg _)
  exact sq_eq_zero_iff.mp hzero

private theorem sectionNorm_zero :
    sectionNorm F ζ hζ U R P H (0 : Sections F ζ hζ U R P H) = 0 := by
  funext b
  simp only [sectionNorm]
  refine Quotient.inductionOn ((H.atlas U).components.symm b).2 (fun x => ?_)
  simp only [componentNorm, Quotient.lift_mk]
  simp

 theorem squaredNorm_zero :
    squaredNorm F ζ hζ U R P H (0 : Sections F ζ hζ U R P H) = 0 := by
  funext b
  simp only [squaredNorm, sectionNorm_zero]
  simp

def nullOnK : Submodule ℂ (BorelL2Sections F ζ hζ U R P H) where
  carrier := {s | squaredNorm F ζ hζ U R P H s.val =ᵐ[
    (muU F ζ hζ U R P).restrict K] 0}
  zero_mem' := by
    change squaredNorm F ζ hζ U R P H (0 : BorelL2Sections F ζ hζ U R P H).val =ᵐ[
      (muU F ζ hζ U R P).restrict K] 0
    rw [show (0 : BorelL2Sections F ζ hζ U R P H).val =
      (0 : Sections F ζ hζ U R P H) from rfl, squaredNorm_zero]
  add_mem' := by
    intro s t hs ht
    change squaredNorm F ζ hζ U R P H (s + t).val =ᵐ[
      (muU F ζ hζ U R P).restrict K] 0
    rw [show (s + t).val = s.val + t.val from rfl]
    have hs' : squaredNorm F ζ hζ U R P H s.val =ᵐ[
        (muU F ζ hζ U R P).restrict K] 0 := hs
    have ht' : squaredNorm F ζ hζ U R P H t.val =ᵐ[
        (muU F ζ hζ U R P).restrict K] 0 := ht
    filter_upwards [sectionNorm_zero_of_squaredNorm_ae F ζ hζ U R P H hs',
      sectionNorm_zero_of_squaredNorm_ae F ζ hζ U R P H ht'] with b hbs hbt
    simp only [Pi.zero_apply] at hbs hbt
    have h1 : sectionNorm F ζ hζ U R P H (s.val + t.val) b ≤
        sectionNorm F ζ hζ U R P H s.val b + sectionNorm F ζ hζ U R P H t.val b :=
      sectionNorm_add_le F ζ hζ U R P H s.val t.val b
    rw [hbs, hbt, add_zero] at h1
    have h2 : 0 ≤ sectionNorm F ζ hζ U R P H (s.val + t.val) b :=
      sectionNorm_nonneg F ζ hζ U R P H (s.val + t.val) b
    have h3 : sectionNorm F ζ hζ U R P H (s.val + t.val) b = 0 := le_antisymm h1 h2
    simp [squaredNorm, h3]
  smul_mem' := by
    intro c s hs
    change squaredNorm F ζ hζ U R P H (c • s).val =ᵐ[
      (muU F ζ hζ U R P).restrict K] 0
    rw [show (c • s).val = c • s.val from rfl]
    have hs' : squaredNorm F ζ hζ U R P H s.val =ᵐ[
        (muU F ζ hζ U R P).restrict K] 0 := hs
    filter_upwards [sectionNorm_zero_of_squaredNorm_ae F ζ hζ U R P H hs'] with b hb
    simp only [Pi.zero_apply] at hb
    have hsm := congrFun (sectionNorm_smul F ζ hζ U R P H c s.val) b
    simp [squaredNorm, hsm, hb]

theorem nullOnK_zero_mem :
    (0 : BorelL2Sections F ζ hζ U R P H) ∈ nullOnK F ζ hζ U R P H K := by
  change squaredNorm F ζ hζ U R P H (0 : BorelL2Sections F ζ hζ U R P H).val =ᵐ[
    (muU F ζ hζ U R P).restrict K] 0
  rw [show (0 : BorelL2Sections F ζ hζ U R P H).val =
    (0 : Sections F ζ hζ U R P H) from rfl, squaredNorm_zero]

theorem nullOnK_add_mem {s t : BorelL2Sections F ζ hζ U R P H}
    (hs : s ∈ nullOnK F ζ hζ U R P H K) (ht : t ∈ nullOnK F ζ hζ U R P H K) :
    s + t ∈ nullOnK F ζ hζ U R P H K := by
  change squaredNorm F ζ hζ U R P H (s + t).val =ᵐ[
    (muU F ζ hζ U R P).restrict K] 0
  rw [show (s + t).val = s.val + t.val from rfl]
  have hs' : squaredNorm F ζ hζ U R P H s.val =ᵐ[
      (muU F ζ hζ U R P).restrict K] 0 := hs
  have ht' : squaredNorm F ζ hζ U R P H t.val =ᵐ[
      (muU F ζ hζ U R P).restrict K] 0 := ht
  filter_upwards [sectionNorm_zero_of_squaredNorm_ae F ζ hζ U R P H hs',
    sectionNorm_zero_of_squaredNorm_ae F ζ hζ U R P H ht'] with b hbs hbt
  simp only [Pi.zero_apply] at hbs hbt
  have h1 : sectionNorm F ζ hζ U R P H (s.val + t.val) b ≤
      sectionNorm F ζ hζ U R P H s.val b + sectionNorm F ζ hζ U R P H t.val b :=
    sectionNorm_add_le F ζ hζ U R P H s.val t.val b
  rw [hbs, hbt, add_zero] at h1
  have h2 : 0 ≤ sectionNorm F ζ hζ U R P H (s.val + t.val) b :=
    sectionNorm_nonneg F ζ hζ U R P H (s.val + t.val) b
  have h3 : sectionNorm F ζ hζ U R P H (s.val + t.val) b = 0 := le_antisymm h1 h2
  simp [squaredNorm, h3]

theorem nullOnK_smul_mem (c : ℂ) {s : BorelL2Sections F ζ hζ U R P H}
    (hs : s ∈ nullOnK F ζ hζ U R P H K) :
    c • s ∈ nullOnK F ζ hζ U R P H K := by
  change squaredNorm F ζ hζ U R P H (c • s).val =ᵐ[
    (muU F ζ hζ U R P).restrict K] 0
  rw [show (c • s).val = c • s.val from rfl]
  have hs' : squaredNorm F ζ hζ U R P H s.val =ᵐ[
      (muU F ζ hζ U R P).restrict K] 0 := hs
  filter_upwards [sectionNorm_zero_of_squaredNorm_ae F ζ hζ U R P H hs'] with b hb
  simp only [Pi.zero_apply] at hb
  have hsm := congrFun (sectionNorm_smul F ζ hζ U R P H c s.val) b
  simp [squaredNorm, hsm, hb]

local instance : HasQuotient (BorelL2Sections F ζ hζ U R P H)
    (Submodule ℂ (BorelL2Sections F ζ hζ U R P H)) :=
  @Submodule.hasQuotient ℂ (BorelL2Sections F ζ hζ U R P H)
    inferInstance inferInstance inferInstance

abbrev H_K := (BorelL2Sections F ζ hζ U R P H) ⧸ nullOnK F ζ hζ U R P H K

def mkK : BorelL2Sections F ζ hζ U R P H →ₗ[ℂ] H_K F ζ hζ U R P H K :=
  @Submodule.mkQ ℂ (BorelL2Sections F ζ hζ U R P H)
    inferInstance inferInstance inferInstance (nullOnK F ζ hζ U R P H K)

 def maskCoeff (s : BorelL2Sections F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount) :
    KPFiniteCuspAtlas.SymmetricSpace F → ℂ :=
  fun x => K.indicator (fun _ => (s.val i).val x)
    ((H.atlas U).components ⟨i, Quotient.mk _ x⟩)

 theorem maskCoeff_scalarFiber (s : BorelL2Sections F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount) (x : KPFiniteCuspAtlas.SymmetricSpace F) :
    maskCoeff F ζ hζ U R P H K s i x ∈
      KPCuspGenuineMonodromy.scalarFiber F ζ hζ U := by
  by_cases hx : (H.atlas U).components ⟨i, Quotient.mk _ x⟩ ∈ K
  · rw [maskCoeff, Set.indicator_of_mem hx]; exact (s.val i).property.1 x
  · rw [maskCoeff, Set.indicator_of_notMem hx]
    exact (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).zero_mem

 theorem maskCoeff_equivariant (s : BorelL2Sections F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount)
    (γ : KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))
    (x : KPFiniteCuspAtlas.SymmetricSpace F) :
    maskCoeff F ζ hζ U R P H K s i ((γ : KPCuspArithmetic.PGL2 F) • x) =
      (KPCuspGenuineMonodromy.chi F ζ hζ (((H.atlas U).line i).rho γ) : ℂ) *
        maskCoeff F ζ hζ U R P H K s i x := by
  have hq : (H.atlas U).components ⟨i, Quotient.mk _
        ((γ : KPCuspArithmetic.PGL2 F) • x)⟩ =
      (H.atlas U).components ⟨i, Quotient.mk _ x⟩ := by
    have hq2 : (Quotient.mk _ ((γ : KPCuspArithmetic.PGL2 F) • x) :
        KPCuspSiegel.OrbitQuotient F (KPCuspGenuineMonodromy.Component F ζ hζ U
          ((H.atlas U).representative i))) = Quotient.mk _ x :=
      (Quotient.sound (MulAction.orbitRel_apply.mpr
        (MulAction.mem_orbit_iff.mpr ⟨γ⁻¹, inv_smul_smul γ x⟩))).symm
    rw [hq2]
  rw [maskCoeff, maskCoeff, hq]
  by_cases hx : (H.atlas U).components ⟨i, Quotient.mk _ x⟩ ∈ K
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, (s.val i).property.2 γ x]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    simp

private theorem measurable_maskCoeff (hK : MeasurableSet K)
    (s : BorelL2Sections F ζ hζ U R P H) (i : Fin (H.atlas U).componentCount) :
    Measurable (maskCoeff F ζ hζ U R P H K s i) := by
  have hcont : Continuous (fun x : KPFiniteCuspAtlas.SymmetricSpace F =>
      (H.atlas U).components ⟨i, Quotient.mk _ x⟩) :=
    (H.atlas U).components.continuous.comp
      (continuous_sigmaMk.comp (KPCuspSiegel.continuous_projection F _))
  have hset : MeasurableSet {x : KPFiniteCuspAtlas.SymmetricSpace F |
      (H.atlas U).components ⟨i, Quotient.mk _ x⟩ ∈ K} := hK.preimage hcont.measurable
  have hfun : maskCoeff F ζ hζ U R P H K s i = fun x =>
      if (H.atlas U).components ⟨i, Quotient.mk _ x⟩ ∈ K then (s.val i).val x else 0 := by
    funext x
    by_cases hx : (H.atlas U).components ⟨i, Quotient.mk _ x⟩ ∈ K
    · rw [maskCoeff, Set.indicator_of_mem hx, if_pos hx]
    · rw [maskCoeff, Set.indicator_of_notMem hx, if_neg hx]
  rw [hfun]
  exact Measurable.ite hset (s.property.1 i) measurable_const

 def maskSections (hK : MeasurableSet K) (s : BorelL2Sections F ζ hζ U R P H) :
    Sections F ζ hζ U R P H :=
  fun i => ⟨maskCoeff F ζ hζ U R P H K s i,
    ⟨maskCoeff_scalarFiber F ζ hζ U R P H K s i,
      maskCoeff_equivariant F ζ hζ U R P H K s i⟩⟩

private theorem sectionNorm_maskSections_le (hK : MeasurableSet K)
    (s : BorelL2Sections F ζ hζ U R P H) (b : KPFiniteCuspAtlas.rawXU F ζ hζ U) :
    sectionNorm F ζ hζ U R P H (maskSections F ζ hζ U R P H K hK s) b ≤
      sectionNorm F ζ hζ U R P H s.val b := by
  rw [show b = (H.atlas U).components ((H.atlas U).components.symm b) from
    (Homeomorph.apply_symm_apply (H.atlas U).components b).symm]
  obtain ⟨i, q⟩ := (H.atlas U).components.symm b
  simp only [sectionNorm]
  rw [Homeomorph.symm_apply_apply]
  refine Quotient.inductionOn q (fun x => ?_)
  simp only [componentNorm, Quotient.lift_mk]
  by_cases hx : (H.atlas U).components ⟨i, Quotient.mk _ x⟩ ∈ K
  · rw [show (maskSections F ζ hζ U R P H K hK s i).val x = (s.val i).val x from by
      simp only [maskSections, maskCoeff]
      rw [Set.indicator_of_mem hx]]
  · rw [show (maskSections F ζ hζ U R P H K hK s i).val x = 0 from by
      simp only [maskSections, maskCoeff]
      rw [Set.indicator_of_notMem hx]]
    simp

private theorem normIntegral_maskSections_lt_top (hK : MeasurableSet K)
    (s : BorelL2Sections F ζ hζ U R P H) :
    normIntegral F ζ hζ U R P H (maskSections F ζ hζ U R P H K hK s) < ⊤ := by
  refine lt_of_le_of_lt ?_ s.property.2
  simp only [normIntegral, squaredNorm]
  refine lintegral_mono (fun b => ENNReal.ofReal_le_ofReal ?_)
  exact pow_le_pow_left₀
    (sectionNorm_nonneg F ζ hζ U R P H (maskSections F ζ hζ U R P H K hK s) b)
    (sectionNorm_maskSections_le F ζ hζ U R P H K hK s b) 2

 theorem maskSections_mem (hK : MeasurableSet K)
    (s : BorelL2Sections F ζ hζ U R P H) :
    maskSections F ζ hζ U R P H K hK s ∈ BorelL2Sections F ζ hζ U R P H :=
  ⟨fun i => measurable_maskCoeff F ζ hζ U R P H K hK s i,
    normIntegral_maskSections_lt_top F ζ hζ U R P H K hK s⟩

 theorem maskSections_add (hK : MeasurableSet K)
    (s t : BorelL2Sections F ζ hζ U R P H) :
    maskSections F ζ hζ U R P H K hK (s + t) =
      maskSections F ζ hζ U R P H K hK s + maskSections F ζ hζ U R P H K hK t := by
  funext i
  apply Subtype.ext
  funext x
  simp only [Submodule.coe_add, Pi.add_apply, maskSections, maskCoeff]
  by_cases hx : (H.atlas U).components ⟨i, Quotient.mk _ x⟩ ∈ K
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx,
      Set.indicator_of_notMem hx]
    simp

 theorem maskSections_smul (hK : MeasurableSet K) (c : ℂ)
    (s : BorelL2Sections F ζ hζ U R P H) :
    maskSections F ζ hζ U R P H K hK (c • s) =
      c • maskSections F ζ hζ U R P H K hK s := by
  funext i
  apply Subtype.ext
  funext x
  simp only [Submodule.coe_smul, Pi.smul_apply, maskSections, maskCoeff, smul_eq_mul]
  by_cases hx : (H.atlas U).components ⟨i, Quotient.mk _ x⟩ ∈ K
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    simp

def mask (hK : MeasurableSet K) :
    BorelL2Sections F ζ hζ U R P H →ₗ[ℂ] BorelL2Sections F ζ hζ U R P H where
  toFun s := ⟨maskSections F ζ hζ U R P H K hK s,
    maskSections_mem F ζ hζ U R P H K hK s⟩
  map_add' := by
    intro s t
    exact Subtype.ext (maskSections_add F ζ hζ U R P H K hK s t)
  map_smul' := by
    intro c s
    exact Subtype.ext (maskSections_smul F ζ hζ U R P H K hK c s)

theorem mask_val_apply (hK : MeasurableSet K) (s : BorelL2Sections F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount) (x : KPFiniteCuspAtlas.SymmetricSpace F) :
    ((mask F ζ hζ U R P H K hK s).val i).val x =
      K.indicator (fun _ => (s.val i).val x)
        ((H.atlas U).components ⟨i, Quotient.mk _ x⟩) := rfl

theorem sectionNorm_mask_components (hK : MeasurableSet K)
    (s : BorelL2Sections F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount) (x : KPFiniteCuspAtlas.SymmetricSpace F) :
    sectionNorm F ζ hζ U R P H (mask F ζ hζ U R P H K hK s).val
        ((H.atlas U).components ⟨i, Quotient.mk _ x⟩) =
      K.indicator (sectionNorm F ζ hζ U R P H s.val)
        ((H.atlas U).components ⟨i, Quotient.mk _ x⟩) := by
  rw [sectionNorm_component F ζ hζ U R P H (mask F ζ hζ U R P H K hK s).val i x]
  by_cases h : (H.atlas U).components ⟨i, Quotient.mk _ x⟩ ∈ K
  · rw [Set.indicator_of_mem h, mask_val_apply, Set.indicator_of_mem h,
      sectionNorm_component F ζ hζ U R P H s.val i x]
  · rw [Set.indicator_of_notMem h, mask_val_apply, Set.indicator_of_notMem h]
    simp

theorem squaredNorm_mask (hK : MeasurableSet K) (s : BorelL2Sections F ζ hζ U R P H) :
    squaredNorm F ζ hζ U R P H (mask F ζ hζ U R P H K hK s).val =
      K.indicator (squaredNorm F ζ hζ U R P H s.val) := by
  funext b
  rw [show b = (H.atlas U).components ((H.atlas U).components.symm b) from
    (Homeomorph.apply_symm_apply (H.atlas U).components b).symm]
  obtain ⟨i, q⟩ := (H.atlas U).components.symm b
  refine Quotient.inductionOn q (fun x => ?_)
  simp only [squaredNorm]
  rw [sectionNorm_mask_components]
  by_cases h : (H.atlas U).components ⟨i, Quotient.mk _ x⟩ ∈ K
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
    simp

 theorem mask_mem_nullSections (hK : MeasurableSet K)
    {s : BorelL2Sections F ζ hζ U R P H} (hs : s ∈ nullOnK F ζ hζ U R P H K) :
    mask F ζ hζ U R P H K hK s ∈ nullSections F ζ hζ U R P H := by
  change squaredNorm F ζ hζ U R P H (mask F ζ hζ U R P H K hK s).val =ᵐ[
    muU F ζ hζ U R P] 0
  rw [squaredNorm_mask F ζ hζ U R P H K hK s]
  have hs' : squaredNorm F ζ hζ U R P H s.val =ᵐ[
      (muU F ζ hζ U R P).restrict K] 0 := hs
  have hmem : ∀ᵐ b ∂(muU F ζ hζ U R P), b ∈ K →
      squaredNorm F ζ hζ U R P H s.val b = 0 := by
    rw [← ae_restrict_iff' hK]
    filter_upwards [hs'] with b hb
    simpa only [Pi.zero_apply] using hb
  filter_upwards [hmem] with b hb
  by_cases hx : b ∈ K
  · rw [Set.indicator_of_mem hx]; exact hb hx
  · rw [Set.indicator_of_notMem hx]; rfl

 def zeroExtensionLinearMap (hK : MeasurableSet K) :
    BorelL2Sections F ζ hζ U R P H →ₗ[ℂ] L2Line F ζ hζ U R P H :=
  (mk F ζ hζ U R P H).comp (mask F ζ hζ U R P H K hK)

def zeroExtension (hK : MeasurableSet K) :
    H_K F ζ hζ U R P H K →ₗ[ℂ] L2Line F ζ hζ U R P H :=
  @Submodule.liftQ ℂ (BorelL2Sections F ζ hζ U R P H)
    inferInstance inferInstance inferInstance (nullOnK F ζ hζ U R P H K)
    ℂ (L2Line F ζ hζ U R P H) inferInstance inferInstance inferInstance (RingHom.id ℂ)
    (zeroExtensionLinearMap F ζ hζ U R P H K hK) (by
      intro s hs
      rw [LinearMap.mem_ker]
      change (mk F ζ hζ U R P H) ((mask F ζ hζ U R P H K hK) s) = 0
      rw [show (0 : L2Line F ζ hζ U R P H) = mk F ζ hζ U R P H 0 from
        (map_zero (mk F ζ hζ U R P H)).symm]
      rw [mk_eq_mk_iff]
      rw [show ((mask F ζ hζ U R P H K hK) s).val -
          (0 : BorelL2Sections F ζ hζ U R P H).val =
          ((mask F ζ hζ U R P H K hK) s).val from sub_zero _]
      exact mask_mem_nullSections F ζ hζ U R P H K hK hs)

private theorem zeroExtension_mkK (hK : MeasurableSet K) (s : BorelL2Sections F ζ hζ U R P H) :
    zeroExtension F ζ hζ U R P H K hK (mkK F ζ hζ U R P H K s) =
      mk F ζ hζ U R P H (mask F ζ hζ U R P H K hK s) := by
  simp only [zeroExtension, zeroExtensionLinearMap, LinearMap.comp_apply,
    Submodule.liftQ_apply, mkK, Submodule.mkQ_apply]

 theorem nullSections_le_nullOnK :
    nullSections F ζ hζ U R P H ≤ nullOnK F ζ hζ U R P H K := by
  intro s hs
  change squaredNorm F ζ hζ U R P H s.val =ᵐ[(muU F ζ hζ U R P).restrict K] 0
  exact ae_restrict_of_ae hs

 def lineRestrictionLin :
    L2Line F ζ hζ U R P H →ₗ[ℂ] H_K F ζ hζ U R P H K :=
  @Submodule.mapQ ℂ (BorelL2Sections F ζ hζ U R P H)
    inferInstance inferInstance inferInstance (nullSections F ζ hζ U R P H)
    ℂ (BorelL2Sections F ζ hζ U R P H) inferInstance inferInstance inferInstance (RingHom.id ℂ)
    (nullOnK F ζ hζ U R P H K) (LinearMap.id) (by
      intro s hs
      rw [Submodule.mem_comap]
      exact nullSections_le_nullOnK F ζ hζ U R P H K hs)

private theorem lineRestrictionLin_mk (s : BorelL2Sections F ζ hζ U R P H) :
    lineRestrictionLin F ζ hζ U R P H K (mk F ζ hζ U R P H s) =
      mkK F ζ hζ U R P H K s := by
  rw [lineRestrictionLin, show (mk F ζ hζ U R P H) s = Submodule.Quotient.mk s from
    Submodule.mkQ_apply _ s, Submodule.mapQ_apply, LinearMap.id_apply]
  rfl

theorem zeroExtension_injective (hK : MeasurableSet K) :
    Function.Injective (zeroExtension F ζ hζ U R P H K hK) := by
  intro u v huv
  obtain ⟨s, hs⟩ := Quotient.exists_rep u
  obtain ⟨t, ht⟩ := Quotient.exists_rep v
  change mkK F ζ hζ U R P H K s = u at hs
  change mkK F ζ hζ U R P H K t = v at ht
  rw [← hs, ← ht] at huv ⊢
  rw [zeroExtension_mkK, zeroExtension_mkK] at huv
  have h2 : squaredNorm F ζ hζ U R P H
      ((mask F ζ hζ U R P H K hK (s - t)).val) =ᵐ[muU F ζ hζ U R P] 0 := by
    have h0 := (mk_eq_mk_iff F ζ hζ U R P H (mask F ζ hζ U R P H K hK s)
      (mask F ζ hζ U R P H K hK t)).mp huv
    have hsub : (mask F ζ hζ U R P H K hK s - mask F ζ hζ U R P H K hK t :
        BorelL2Sections F ζ hζ U R P H) = mask F ζ hζ U R P H K hK (s - t) :=
      (map_sub (mask F ζ hζ U R P H K hK) s t).symm
    rw [← Submodule.coe_sub, hsub] at h0
    exact h0
  have h3 : K.indicator (squaredNorm F ζ hζ U R P H (s - t).val) =ᵐ[muU F ζ hζ U R P] 0 := by
    rw [← squaredNorm_mask F ζ hζ U R P H K hK (s - t)]
    exact h2
  have h4 : squaredNorm F ζ hζ U R P H (s - t).val =ᵐ[(muU F ζ hζ U R P).restrict K] 0 := by
    change ∀ᵐ b ∂(muU F ζ hζ U R P).restrict K,
      squaredNorm F ζ hζ U R P H (s - t).val b = 0
    rw [ae_restrict_iff' hK]
    filter_upwards [h3] with b hb
    intro hbK
    rwa [Set.indicator_of_mem hbK] at hb
  change Submodule.Quotient.mk s = Submodule.Quotient.mk t
  rw [Submodule.Quotient.eq]
  exact h4

 def hullK : Set (X_U F ζ hζ U) := toMeasurable (muU F ζ hζ U R P) K

 theorem measurableSet_hullK : MeasurableSet (hullK F ζ hζ U R P K) :=
  measurableSet_toMeasurable _ _

private theorem restrict_hullK :
    (muU F ζ hζ U R P).restrict (hullK F ζ hζ U R P K) =
      (muU F ζ hζ U R P).restrict K := by
  haveI : SigmaFinite (muU F ζ hζ U R P) :=
    KPContSectorFixedMeasureLocalFiniteness.sphericalMeasure_sigmaFinite F ζ hζ R P U
  haveI : SFinite (muU F ζ hζ U R P) := inferInstance
  exact Measure.restrict_toMeasurable_of_sFinite K

 theorem nullOnK_hullK :
    nullOnK F ζ hζ U R P H K = nullOnK F ζ hζ U R P H (hullK F ζ hζ U R P K) := by
  refine Submodule.ext fun s => ?_
  change (squaredNorm F ζ hζ U R P H s.val =ᵐ[(muU F ζ hζ U R P).restrict K] 0) ↔
    (squaredNorm F ζ hζ U R P H s.val =ᵐ[
      (muU F ζ hζ U R P).restrict (hullK F ζ hζ U R P K)] 0)
  rw [restrict_hullK]

 def extToHull :
    H_K F ζ hζ U R P H K ≃ₗ[ℂ] H_K F ζ hζ U R P H (hullK F ζ hζ U R P K) :=
  @Submodule.quotEquivOfEq ℂ (BorelL2Sections F ζ hζ U R P H)
    inferInstance inferInstance inferInstance
    (nullOnK F ζ hζ U R P H K)
    (nullOnK F ζ hζ U R P H (hullK F ζ hζ U R P K)) (nullOnK_hullK F ζ hζ U R P H K)

 def normMap : H_K F ζ hζ U R P H K →ₗ[ℂ] L2Line F ζ hζ U R P H :=
  (zeroExtension F ζ hζ U R P H (hullK F ζ hζ U R P K)
      (measurableSet_hullK F ζ hζ U R P K)).comp
    (extToHull F ζ hζ U R P H K).toLinearMap

 theorem normMap_injective : Function.Injective (normMap F ζ hζ U R P H K) :=
  (zeroExtension_injective F ζ hζ U R P H (hullK F ζ hζ U R P K)
    (measurableSet_hullK F ζ hζ U R P K)).comp (extToHull F ζ hζ U R P H K).injective

instance instNormedAddCommGroupHK :
    NormedAddCommGroup (H_K F ζ hζ U R P H K) :=
  NormedAddCommGroup.induced _ _ (normMap F ζ hζ U R P H K).toAddMonoidHom
    (normMap_injective F ζ hζ U R P H K)

instance instNormedSpaceHK : NormedSpace ℂ (H_K F ζ hζ U R P H K) :=
  NormedSpace.induced ℂ _ _ (normMap F ζ hζ U R P H K)

instance instInnerProductSpaceHK : InnerProductSpace ℂ (H_K F ζ hζ U R P H K) :=
  InnerProductSpace.induced (normMap F ζ hζ U R P H K)

 abbrev instTopologicalSpaceHKLocal : TopologicalSpace (H_K F ζ hζ U R P H K) :=
  (inferInstance : NormedAddCommGroup (H_K F ζ hζ U R P H K)).toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

attribute [local instance 5000] instTopologicalSpaceHKLocal

 abbrev instAddCommMonoidHKLocal : AddCommMonoid (H_K F ζ hζ U R P H K) :=
  (inferInstance : NormedAddCommGroup (H_K F ζ hζ U R P H K)).toSeminormedAddCommGroup.toAddCommMonoid

attribute [local instance 5000] instAddCommMonoidHKLocal

section RestrictedNorm
variable (hK : MeasurableSet K)

theorem norm_mkK_sq (s : BorelL2Sections F ζ hζ U R P H) :
    ‖mkK F ζ hζ U R P H K s‖ ^ 2 =
      (∫⁻ b in K, squaredNorm F ζ hζ U R P H s.val b ∂muU F ζ hζ U R P).toReal := by
  have hnorm : ‖mkK F ζ hζ U R P H K s‖ =
      ‖mk F ζ hζ U R P H (mask F ζ hζ U R P H (hullK F ζ hζ U R P K)
        (measurableSet_hullK F ζ hζ U R P K) s)‖ := by
    change ‖normMap F ζ hζ U R P H K (mkK F ζ hζ U R P H K s)‖ = _
    rw [normMap, LinearMap.comp_apply]
    change ‖zeroExtension F ζ hζ U R P H (hullK F ζ hζ U R P K)
        (measurableSet_hullK F ζ hζ U R P K)
        ((extToHull F ζ hζ U R P H K) (mkK F ζ hζ U R P H K s))‖ = _
    rw [show (extToHull F ζ hζ U R P H K) (mkK F ζ hζ U R P H K s) =
        mkK F ζ hζ U R P H (hullK F ζ hζ U R P K) s from by
      rw [extToHull, show (mkK F ζ hζ U R P H K) s = Submodule.Quotient.mk s from
        Submodule.mkQ_apply _ s, Submodule.quotEquivOfEq_mk]
      rfl]
    rw [zeroExtension_mkK]
  rw [hnorm, norm_sq]
  congr 1
  rw [normIntegral, squaredNorm_mask,
    lintegral_indicator (measurableSet_hullK F ζ hζ U R P K), restrict_hullK]

theorem zeroExtension_norm (u : H_K F ζ hζ U R P H K) :
    ‖zeroExtension F ζ hζ U R P H K hK u‖ = ‖u‖ := by
  obtain ⟨s, hs⟩ := Quotient.exists_rep u
  change mkK F ζ hζ U R P H K s = u at hs
  rw [← hs]
  have hZ : ‖zeroExtension F ζ hζ U R P H K hK (mkK F ζ hζ U R P H K s)‖ =
      ‖mk F ζ hζ U R P H (mask F ζ hζ U R P H K hK s)‖ := by
    rw [zeroExtension_mkK]
  have h2 : ‖mk F ζ hζ U R P H (mask F ζ hζ U R P H K hK s)‖ ^ 2 =
      ‖mkK F ζ hζ U R P H K s‖ ^ 2 := by
    rw [norm_sq, norm_mkK_sq]
    congr 1
    rw [normIntegral, squaredNorm_mask, lintegral_indicator hK]
  rw [hZ]
  calc ‖mk F ζ hζ U R P H (mask F ζ hζ U R P H K hK s)‖
      = Real.sqrt (‖mk F ζ hζ U R P H (mask F ζ hζ U R P H K hK s)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖mkK F ζ hζ U R P H K s‖ ^ 2) := by rw [h2]
    _ = ‖mkK F ζ hζ U R P H K s‖ := Real.sqrt_sq (norm_nonneg _)

theorem mkK_eq_iff (s t : BorelL2Sections F ζ hζ U R P H) :
    mkK F ζ hζ U R P H K s = mkK F ζ hζ U R P H K t ↔
      squaredNorm F ζ hζ U R P H (s.val - t.val) =ᵐ[
        (muU F ζ hζ U R P).restrict K] 0 := by
  change Submodule.Quotient.mk s = Submodule.Quotient.mk t ↔ _
  rw [Submodule.Quotient.eq]
  rfl

private theorem mkK_mask (hK : MeasurableSet K) (s : BorelL2Sections F ζ hζ U R P H) :
    mkK F ζ hζ U R P H K (mask F ζ hζ U R P H K hK s) = mkK F ζ hζ U R P H K s := by
  rw [mkK_eq_iff]
  change ∀ᵐ b ∂(muU F ζ hζ U R P).restrict K,
    squaredNorm F ζ hζ U R P H ((mask F ζ hζ U R P H K hK s).val - s.val) b = 0
  rw [ae_restrict_iff' hK]
  refine Filter.Eventually.of_forall fun b => ?_
  rw [show b = (H.atlas U).components ((H.atlas U).components.symm b) from
    (Homeomorph.apply_symm_apply (H.atlas U).components b).symm]
  obtain ⟨i, q⟩ := (H.atlas U).components.symm b
  refine Quotient.inductionOn q (fun x => ?_)
  intro hb
  simp only [squaredNorm, sectionNorm]
  rw [Homeomorph.symm_apply_apply]
  simp only [componentNorm, Quotient.lift_mk]
  rw [show (((mask F ζ hζ U R P H K hK s).val - s.val) i).val x =
      ((mask F ζ hζ U R P H K hK s).val i).val x - (s.val i).val x from rfl,
    mask_val_apply, Set.indicator_of_mem hb]
  simp

 theorem lineRestrictionLin_norm_le (u : L2Line F ζ hζ U R P H) :
    ‖lineRestrictionLin F ζ hζ U R P H K u‖ ≤ ‖u‖ := by
  obtain ⟨s, hs⟩ := Quotient.exists_rep u
  change mk F ζ hζ U R P H s = u at hs
  rw [← hs, lineRestrictionLin_mk]
  have h2 : ‖mkK F ζ hζ U R P H K s‖ ^ 2 ≤ ‖mk F ζ hζ U R P H s‖ ^ 2 := by
    rw [norm_mkK_sq, norm_sq]
    refine ENNReal.toReal_mono (ne_of_lt s.property.2) ?_
    rw [normIntegral]
    exact lintegral_mono' Measure.restrict_le_self le_rfl
  calc ‖mkK F ζ hζ U R P H K s‖
      = Real.sqrt (‖mkK F ζ hζ U R P H K s‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖mk F ζ hζ U R P H s‖ ^ 2) := Real.sqrt_le_sqrt h2
    _ = ‖mk F ζ hζ U R P H s‖ := Real.sqrt_sq (norm_nonneg _)

def lineRestriction (hK : MeasurableSet K) : L2Line F ζ hζ U R P H →L[ℂ] H_K F ζ hζ U R P H K :=
  (lineRestrictionLin F ζ hζ U R P H K).mkContinuous 1 fun u => by
    rw [one_mul]
    exact lineRestrictionLin_norm_le F ζ hζ U R P H K u

theorem lineRestriction_mk (s : BorelL2Sections F ζ hζ U R P H) :
    lineRestriction F ζ hζ U R P H K hK (mk F ζ hζ U R P H s) =
      mkK F ζ hζ U R P H K s := by
  rw [lineRestriction, LinearMap.mkContinuous_apply]
  exact lineRestrictionLin_mk F ζ hζ U R P H K s

def res_K : H_U F ζ hζ U R →L[ℂ] H_K F ζ hζ U R P H K where
  toFun u := lineRestriction F ζ hζ U R P H K hK
    (sectorLineIsometry F ζ hζ U R P H u)
  map_add' := by
    intro u v
    rw [map_add, map_add]
  map_smul' := by
    intro c u
    simp only [map_smul, RingHom.id_apply]
  cont := by
    have hcont : Continuous fun u : H_U F ζ hζ U R =>
        lineRestriction F ζ hζ U R P H K hK
          (sectorLineIsometry F ζ hζ U R P H u) :=
      (lineRestriction F ζ hζ U R P H K hK).cont.comp
        (sectorLineIsometry F ζ hζ U R P H).continuous
    exact hcont

theorem norm_res_K_le (u : H_U F ζ hζ U R) :
    ‖res_K F ζ hζ U R P H K hK u‖ ≤ ‖u‖ := by
  obtain ⟨s, hs⟩ := @Submodule.Quotient.mk_surjective ℂ
    (BorelL2Sections F ζ hζ U R P H) inferInstance inferInstance inferInstance
    (nullSections F ζ hζ U R P H) (sectorLineIsometry F ζ hζ U R P H u)
  change mk F ζ hζ U R P H s = sectorLineIsometry F ζ hζ U R P H u at hs
  change ‖lineRestriction F ζ hζ U R P H K hK
    (sectorLineIsometry F ζ hζ U R P H u)‖ ≤ ‖u‖
  rw [← hs, lineRestriction_mk, ← (sectorLineIsometry F ζ hζ U R P H).norm_map u, ← hs]
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_mkK_sq, norm_sq]
  exact ENNReal.toReal_mono (ne_of_lt s.property.2)
    (lintegral_mono' Measure.restrict_le_self le_rfl)

private theorem mkK_mask_hullK (hK : MeasurableSet K) (s : BorelL2Sections F ζ hζ U R P H) :
    mkK F ζ hζ U R P H K (mask F ζ hζ U R P H (hullK F ζ hζ U R P K)
      (measurableSet_hullK F ζ hζ U R P K) s) = mkK F ζ hζ U R P H K s := by
  rw [mkK_eq_iff]
  change ∀ᵐ b ∂(muU F ζ hζ U R P).restrict K,
    squaredNorm F ζ hζ U R P H ((mask F ζ hζ U R P H (hullK F ζ hζ U R P K)
      (measurableSet_hullK F ζ hζ U R P K) s).val - s.val) b = 0
  rw [ae_restrict_iff' hK]
  refine Filter.Eventually.of_forall fun b => ?_
  rw [show b = (H.atlas U).components ((H.atlas U).components.symm b) from
    (Homeomorph.apply_symm_apply (H.atlas U).components b).symm]
  obtain ⟨i, q⟩ := (H.atlas U).components.symm b
  refine Quotient.inductionOn q (fun x => ?_)
  intro hb
  simp only [squaredNorm, sectionNorm]
  rw [Homeomorph.symm_apply_apply]
  simp only [componentNorm, Quotient.lift_mk]
  rw [show (((mask F ζ hζ U R P H (hullK F ζ hζ U R P K)
        (measurableSet_hullK F ζ hζ U R P K) s).val - s.val) i).val x =
      ((mask F ζ hζ U R P H (hullK F ζ hζ U R P K)
        (measurableSet_hullK F ζ hζ U R P K) s).val i).val x - (s.val i).val x from rfl,
    mask_val_apply,
    Set.indicator_of_mem (show (H.atlas U).components ⟨i, Quotient.mk _ x⟩ ∈
      hullK F ζ hζ U R P K from subset_toMeasurable (muU F ζ hζ U R P) K hb)]
  simp

 theorem normMap_norm (x : H_K F ζ hζ U R P H K) :
    ‖normMap F ζ hζ U R P H K x‖ = ‖x‖ := rfl

private theorem normMap_isometry : Isometry (normMap F ζ hζ U R P H K) := by
  refine Isometry.of_dist_eq fun x y => ?_
  simp only [dist_eq_norm, ← map_sub, normMap_norm]

 def normMapCLM : H_K F ζ hζ U R P H K →L[ℂ] L2Line F ζ hζ U R P H :=
  (normMap F ζ hζ U R P H K).mkContinuous 1 fun x => by
    rw [one_mul]
    exact le_of_eq (normMap_norm F ζ hζ U R P H K x)

private theorem normMapCLM_apply (x : H_K F ζ hζ U R P H K) :
    normMapCLM F ζ hζ U R P H K x = normMap F ζ hζ U R P H K x := rfl

private theorem lineRestriction_normMap (hK : MeasurableSet K)
    (x : H_K F ζ hζ U R P H K) :
    lineRestriction F ζ hζ U R P H K hK (normMapCLM F ζ hζ U R P H K x) = x := by
  obtain ⟨s, hs⟩ := Quotient.exists_rep x
  change mkK F ζ hζ U R P H K s = x at hs
  rw [← hs, normMapCLM_apply]
  show lineRestriction F ζ hζ U R P H K hK
    (zeroExtension F ζ hζ U R P H (hullK F ζ hζ U R P K)
      (measurableSet_hullK F ζ hζ U R P K)
      ((extToHull F ζ hζ U R P H K) (mkK F ζ hζ U R P H K s))) = mkK F ζ hζ U R P H K s
  rw [show (extToHull F ζ hζ U R P H K) (mkK F ζ hζ U R P H K s) =
      mkK F ζ hζ U R P H (hullK F ζ hζ U R P K) s from by
      rw [extToHull, show (mkK F ζ hζ U R P H K) s = Submodule.Quotient.mk s from
        Submodule.mkQ_apply _ s, Submodule.quotEquivOfEq_mk]
      rfl,
    zeroExtension_mkK, lineRestriction_mk]
  exact mkK_mask_hullK F ζ hζ U R P H K hK s

theorem restricted_complete : CompleteSpace (H_K F ζ hζ U R P H K) := by
  have hh : MeasurableSet (hullK F ζ hζ U R P K) := measurableSet_hullK F ζ hζ U R P K
  let Z : H_K F ζ hζ U R P H (hullK F ζ hζ U R P K) →L[ℂ] L2Line F ζ hζ U R P H :=
    (zeroExtension F ζ hζ U R P H (hullK F ζ hζ U R P K) hh).mkContinuous 1 fun y => by
      rw [one_mul]
      exact le_of_eq (zeroExtension_norm F ζ hζ U R P H (hullK F ζ hζ U R P K) hh y)
  let L : L2Line F ζ hζ U R P H →L[ℂ] H_K F ζ hζ U R P H (hullK F ζ hζ U R P K) :=
    lineRestriction F ζ hζ U R P H (hullK F ζ hζ U R P K) hh
  have hLZ : ∀ y, L (Z y) = y := by
    intro y
    obtain ⟨s, hs⟩ := Quotient.exists_rep y
    change mkK F ζ hζ U R P H (hullK F ζ hζ U R P K) s = y at hs
    rw [← hs]
    show lineRestriction F ζ hζ U R P H (hullK F ζ hζ U R P K) hh
      (zeroExtension F ζ hζ U R P H (hullK F ζ hζ U R P K) hh
        (mkK F ζ hζ U R P H (hullK F ζ hζ U R P K) s)) =
      mkK F ζ hζ U R P H (hullK F ζ hζ U R P K) s
    rw [zeroExtension_mkK, lineRestriction_mk, mkK_mask]
  let Q : L2Line F ζ hζ U R P H →L[ℂ] L2Line F ζ hζ U R P H := Z.comp L
  have hQ : ∀ x, Q (Q x) = Q x := by
    intro x
    show Z (L (Z (L x))) = Z (L x)
    rw [hLZ]
  have hrange : Set.range Q = {x : L2Line F ζ hζ U R P H | (1 - Q) x = 0} := by
    ext x; constructor
    · rintro ⟨y, rfl⟩
      show (1 - Q) (Q y) = 0
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hQ, sub_self]
    · intro hx
      change (1 - Q) x = 0 at hx
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] at hx
      exact ⟨x, (sub_eq_zero.mp hx).symm⟩
  have hclosedZ : IsClosed (Set.range Z) := by
    have hrangeZ : Set.range Z = Set.range Q := by
      ext x; constructor
      · rintro ⟨y, rfl⟩
        exact ⟨Z y, by show Z (L (Z y)) = Z y; rw [hLZ]⟩
      · rintro ⟨y, rfl⟩
        exact ⟨L y, rfl⟩
    rw [hrangeZ, hrange]
    exact ContinuousLinearMap.isClosed_ker (1 - Q)
  have hclosed : IsClosed (Set.range (normMap F ζ hζ U R P H K)) := by
    have hrangeN : Set.range (normMap F ζ hζ U R P H K) = Set.range Z := by
      ext x; constructor
      · rintro ⟨y, rfl⟩
        exact ⟨(extToHull F ζ hζ U R P H K) y, by
          show Z ((extToHull F ζ hζ U R P H K) y) = normMap F ζ hζ U R P H K y
          rfl⟩
      · rintro ⟨y, rfl⟩
        exact ⟨(extToHull F ζ hζ U R P H K).symm y, by
          show normMap F ζ hζ U R P H K ((extToHull F ζ hζ U R P H K).symm y) = Z y
          rw [show normMap F ζ hζ U R P H K ((extToHull F ζ hζ U R P H K).symm y) =
            Z ((extToHull F ζ hζ U R P H K) ((extToHull F ζ hζ U R P H K).symm y)) from rfl,
            LinearEquiv.apply_symm_apply]⟩
    rw [hrangeN]
    exact hclosedZ
  rw [completeSpace_iff_isComplete_range (normMap_isometry F ζ hζ U R P H K).isUniformInducing]
  exact hclosed.isComplete

end RestrictedNorm

abbrev Chart := KPCoreChartLocalizers.Chart F ζ hζ H.totallyComplex U (H.atlas U)

def actualWeight (C : Chart F ζ hζ U R P H) (x : KPCoreChartLocalizers.E C.n) : ℝ :=
  ((H.disintegration U).componentWeight C.component).toReal * C.weight x

variable (hK : IsCompact K)

structure Localizers (hK : IsCompact K) where
  count : ℕ
  empty_case : K = ∅ → count = 0
  chart : Fin count → Chart F ζ hζ U R P H
  open_image : ∀ i, IsOpen ((chart i).O F ζ hζ H.totallyComplex U)
  quotient_chart : ∀ i, Quotient ((chart i).relation F ζ hζ H.totallyComplex U) ≃ₜ
    ((chart i).O F ζ hζ H.totallyComplex U)
  quotient_chart_formula : ∀ i (x : Metric.ball (0 : KPCoreChartLocalizers.E (chart i).n)
      (chart i).radius),
    (quotient_chart i (Quotient.mk _ x)).val =
      (chart i).toBase F ζ hζ H.totallyComplex U x.val
  orbit_relation : ∀ i (x y : Metric.ball (0 : KPCoreChartLocalizers.E (chart i).n)
      (chart i).radius),
    ((chart i).relation F ζ hζ H.totallyComplex U).r x y ↔
      ∃ g : (chart i).G F ζ hζ H.totallyComplex U, (chart i).orthogonal g x.val = y.val

  line_orbit_relation : ∀ i
      (x y : Metric.ball (0 : KPCoreChartLocalizers.E (chart i).n) (chart i).radius)
      (a b : KPCuspGenuineMonodromy.scalarFiber F ζ hζ U),
    ((chart i).lineRelation F ζ hζ H.totallyComplex U).r (x,a) (y,b) ↔
      ∃ g : (chart i).G F ζ hζ H.totallyComplex U,
        (chart i).orthogonal g x.val = y.val ∧
        (b : ℂ) = ((chart i).rho F ζ hζ H.totallyComplex U g : ℂ) * (a : ℂ)
  line_chart_surjective : ∀ i
      (l : KPCoreChartLocalizers.Line F ζ hζ H.totallyComplex U (H.atlas U)),
    KPCoreChartLocalizers.lineBase F ζ hζ H.totallyComplex U (H.atlas U) l ∈
      (chart i).O F ζ hζ H.totallyComplex U →
      ∃ (x : Metric.ball (0 : KPCoreChartLocalizers.E (chart i).n) (chart i).radius)
        (a : KPCuspGenuineMonodromy.scalarFiber F ζ hζ U),
        (chart i).toLine F ζ hζ H.totallyComplex U x.val a = l
  invariant_ball : ∀ i (g : (chart i).G F ζ hζ H.totallyComplex U),
    (chart i).orthogonal g '' Metric.ball 0 (chart i).radius = Metric.ball 0 (chart i).radius
  unitary_character : ∀ i (g : (chart i).G F ζ hζ H.totallyComplex U),
    ‖((chart i).rho F ζ hζ H.totallyComplex U g : ℂ)‖ = 1

  chart_measure : ∀ i, Measure.map ((chart i).toBase F ζ hζ H.totallyComplex U)
    ((Fintype.card ((chart i).G F ζ hζ H.totallyComplex U) : ℝ≥0∞)⁻¹ •
      (volume.restrict (Metric.ball 0 (chart i).radius)).withDensity
        (fun x => ENNReal.ofReal (actualWeight F ζ hζ U R P H (chart i) x))) =
    (muU F ζ hζ U R P).restrict ((chart i).O F ζ hζ H.totallyComplex U)
  lower : Fin count → ℝ
  upper : Fin count → ℝ
  positive_lower : ∀ i, 0 < lower i

  density_bounds : ∀ i x, x ∈ closure (Metric.ball (0 : KPCoreChartLocalizers.E
      (chart i).n) (chart i).radius) →
    lower i ≤ actualWeight F ζ hζ U R P H (chart i) x ∧
      actualWeight F ζ hζ U R P H (chart i) x ≤ upper i
  phi : Fin count → X_U F ζ hζ U → ℝ
  nonnegative_phi : ∀ i x, 0 ≤ phi i x
  compact_phi : ∀ i, HasCompactSupport (phi i)
  support_phi : ∀ i, tsupport (phi i) ⊆ (chart i).O F ζ hζ H.totallyComplex U
  smooth_phi : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun z =>
    phi i (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative j)
      (KPCuspSiegel.projection F _ z)))
  neighborhood : Set (X_U F ζ hζ U)
  open_neighborhood : IsOpen neighborhood
  covers_compact : K ⊆ neighborhood
  partition : ∀ x ∈ neighborhood, ∑ i, phi i x = 1
  cutoff : ∀ i, KPCoreChartLocalizers.E (chart i).n → ℝ
  cutoff_formula : ∀ i, cutoff i = (Metric.ball 0 (chart i).radius).indicator
    (fun x => phi i ((chart i).toBase F ζ hζ H.totallyComplex U x))
  smooth_cutoff : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (cutoff i)
  compact_cutoff : ∀ i, HasCompactSupport (cutoff i)
  support_cutoff : ∀ i, tsupport (cutoff i) ⊆ Metric.ball 0 (chart i).radius
  invariant_cutoff : ∀ i (g : (chart i).G F ζ hζ H.totallyComplex U) x,
    cutoff i ((chart i).orthogonal g x) = cutoff i x
  derivativeBound : Fin count → ℕ → ℝ
  nonnegative_derivativeBound : ∀ i k, 0 ≤ derivativeBound i k
  derivative_bounds : ∀ i k x, x ∈ tsupport (cutoff i) →
    ‖iteratedFDeriv ℝ k (cutoff i) x‖ ≤ derivativeBound i k
  ellipticity : Fin count → ℝ
  metricUpper : Fin count → ℝ
  positive_ellipticity : ∀ i, 0 < ellipticity i

  metric_bounds : ∀ i x, x ∈ tsupport (cutoff i) → ∀ ξ : KPCoreChartLocalizers.E (chart i).n,
    ellipticity i * ‖ξ‖ ^ 2 ≤
      ∑ j, ∑ k, (chart i).energyMatrix F ζ hζ H.totallyComplex U x j k * ξ j * ξ k ∧
    (∑ j, ∑ k, (chart i).energyMatrix F ζ hζ H.totallyComplex U x j k * ξ j * ξ k) ≤
      metricUpper i * ‖ξ‖ ^ 2
  T : ∀ i, H_U F ζ hζ U R →L[ℂ]
    Lp ℂ 2 (volume.restrict (KPCoreChartLocalizers.cube (chart i).n (chart i).a))

  T_formula : ∀ i (u : H_U F ζ hζ U R) (s : BorelL2Sections F ζ hζ U R P H),
    sectorLineIsometry F ζ hζ U R P H u = mk F ζ hζ U R P H s →
    T i u =ᵐ[volume.restrict (KPCoreChartLocalizers.cube (chart i).n (chart i).a)]
      (fun x => (cutoff i x : ℂ) * (s.val (chart i).component).val ((chart i).coordinates x))
  Rmap : ∀ i, Lp ℂ 2
    (volume.restrict (KPCoreChartLocalizers.cube (chart i).n (chart i).a)) →L[ℂ]
      H_K F ζ hζ U R P H K

  R_formula : ∀ i f, ∃ t : BorelL2Sections F ζ hζ U R P H,
    Rmap i f = mkK F ζ hζ U R P H K t ∧
    (∀ᵐ x ∂volume.restrict (Metric.ball 0 (chart i).radius),
      (chart i).toBase F ζ hζ H.totallyComplex U x ∈ K →
      (t.val (chart i).component).val ((chart i).coordinates x) =
        ((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).orthogonalProjectionOnto
          ((chart i).average F ζ hζ H.totallyComplex U f x) : ℂ)) ∧
    (∀ᵐ b ∂(muU F ζ hζ U R P).restrict K,
      b ∉ (chart i).O F ζ hζ H.totallyComplex U → squaredNorm F ζ hζ U R P H t.val b = 0)
  reconstruction : res_K F ζ hζ U R P H K hK.measurableSet =
    ∑ i, (Rmap i).comp (T i)
  smooth_test_image : ∀ i (f : KPContActualSectorSmoothTestModules.S_U F ζ hζ U R P H),
    ∃ g : KPCoreChartLocalizers.E (chart i).n → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
      tsupport g ⊆ interior (KPCoreChartLocalizers.cube (chart i).n (chart i).a) ∧
      T i (KPContActualSectorTestEmbeddings.iota f) =ᵐ[
        volume.restrict (KPCoreChartLocalizers.cube (chart i).n (chart i).a)] g

end DedekindZetaZeroFree.KPContActualFixedHaarCoreLocalizers

end
