module

public import DedekindZetaZeroFree.Adeles.Archimedean.MatrixInsertion
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.MixedTensorGeneration

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace DedekindZetaZeroFree.KPLiteralScalarHCCompactOrbit
open KPLiteralRaw KPAdelicCoverRestrictedProduct KPLiteralChamber
open KPCplxCharacterHaar KPLiteralScalarArchUniformBands KPLiteralScalarMixedTensorGeneration
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
open _root_.DedekindZetaZeroFree.KPLiteralChamber renaming complexSectionHom → complexSectionHom
open _root_.DedekindZetaZeroFree.KPLiteralChamber renaming tuple_prod → tuple_prod

variable {Y : Type*}

def archRestriction (anchor : Y → G F ζ hζ) :
    Functions F ζ hζ →ₗ[ℂ] (Y → (InfinitePlace F → ComplexGL2) → ℂ) where
  toFun φ y a := φ (anchor y * archMatrixInsertion F ζ hζ a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def scalarFamilyTranslate (k : InfinitePlace F → ComplexSU2) :
    (Y → (InfinitePlace F → ComplexGL2) → ℂ) →ₗ[ℂ]
      (Y → (InfinitePlace F → ComplexGL2) → ℂ) where
  toFun h y a := h y (fun w => a w * complexSU2Embedding (k w))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem archRestriction_translate (anchor : Y → G F ζ hζ)
    (φ : Functions F ζ hζ) (k : InfinitePlace F → ComplexSU2) :
    scalarFamilyTranslate F k (archRestriction F ζ hζ anchor φ) =
      archRestriction F ζ hζ anchor (rightAction F ζ hζ
        (archMatrixInsertion F ζ hζ (fun w => complexSU2Embedding (k w))) φ) := by
  funext y a
  change φ (anchor y * archMatrixInsertion F ζ hζ
      (a * (fun w => complexSU2Embedding (k w)))) =
    φ ((anchor y * archMatrixInsertion F ζ hζ a) *
      archMatrixInsertion F ζ hζ (fun w => complexSU2Embedding (k w)))
  rw [map_mul, mul_assoc]

theorem archRestriction_orbit_finite (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (φ : Functions F ζ hζ)
    (hφ : KFinite F ζ hζ K φ) (anchor : Y → G F ζ hζ) :
    Module.Finite ℂ (Submodule.span ℂ (Set.range (fun k =>
      scalarFamilyTranslate F k (archRestriction F ζ hζ anchor φ)))) := by
  obtain ⟨V, hV, hφV, hstable⟩ := hφ
  let : Module.Finite ℂ V := hV
  let L := (archRestriction F ζ hζ anchor).comp V.subtype
  have hle : Submodule.span ℂ (Set.range (fun k =>
      scalarFamilyTranslate F k (archRestriction F ζ hζ anchor φ))) ≤ L.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    refine ⟨⟨rightAction F ζ hζ
      (archMatrixInsertion F ζ hζ (fun w => complexSU2Embedding (k w))) φ,
      hstable ⟨_, archMatrixInsertion_compact_mem F ζ hζ K hK k⟩ φ hφV⟩, ?_⟩
    exact (archRestriction_translate F ζ hζ anchor φ k).symm
  exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

def forgetFamily : (Y → multiPrincipalSeries KPCplxPrincipalSeriesCharts.positiveParameter
    (InfinitePlace F)) →ₗ[ℂ] (Y → (InfinitePlace F → ComplexGL2) → ℂ) :=
  LinearMap.pi (fun y => (multiPrincipalSeries
    KPCplxPrincipalSeriesCharts.positiveParameter (InfinitePlace F)).subtype.comp (LinearMap.proj y))

private theorem forgetFamily_injective : Function.Injective (forgetFamily (Y := Y) F) := by
  intro h l he
  funext y
  apply Subtype.ext
  exact congrFun he y

theorem forgetFamily_translate
    (h : Y → multiPrincipalSeries KPCplxPrincipalSeriesCharts.positiveParameter (InfinitePlace F))
    (k : InfinitePlace F → ComplexSU2) :
    forgetFamily F (familyTranslate k h) = scalarFamilyTranslate F k (forgetFamily F h) := rfl

theorem actual_familyOrbit_finite (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (φ : Functions F ζ hζ)
    (hφ : KFinite F ζ hζ K φ) (anchor : Y → G F ζ hζ)
    (h : Y → multiPrincipalSeries KPCplxPrincipalSeriesCharts.positiveParameter (InfinitePlace F))
    (hpin : forgetFamily F h = archRestriction F ζ hζ anchor φ) :
    Module.Finite ℂ (familyOrbit h) := by
  let V := Submodule.span ℂ (Set.range (fun k =>
    scalarFamilyTranslate F k (archRestriction F ζ hζ anchor φ)))
  let : Module.Finite ℂ V := archRestriction_orbit_finite F ζ hζ K hK φ hφ anchor
  have hle : familyOrbit h ≤ V.comap (forgetFamily F) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    change forgetFamily F (familyTranslate k h) ∈ V
    rw [forgetFamily_translate, hpin]
    exact Submodule.subset_span ⟨k, rfl⟩
  let L : familyOrbit h →ₗ[ℂ] V :=
    ((forgetFamily F).comp (familyOrbit h).subtype).codRestrict V (fun v => hle v.property)
  apply Module.Finite.of_injective L
  intro x y he
  apply Subtype.ext
  apply forgetFamily_injective F
  exact congrArg Subtype.val he

end DedekindZetaZeroFree.KPLiteralScalarHCCompactOrbit

end
