module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Archimedean.HarmonicTensorInterpolation
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ProductSections.HarishChandraCompatibility
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.TensorProducts.MixedTensorGeneration

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.FourierContinuation.CurrentFiniteFamily
open KPLiteralRaw KPAdelicCoverRestrictedProduct KPLiteralScalarHCFiniteInsertion
open KPLiteralScalarHCFiniteProduct KPLiteralScalarHCFiniteOutside
open KPLiteralScalarHCCompactOrbit KPLiteralScalarHCSliceCharts KPLiteralScalarHCExtraction
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues
open KPLiteralScalarArchUniformBands KPLiteralScalarArchIndependentSlices
open NativeScalarMixedTensorGeneration CurrentArchFamily
open KPLocalPrincipalSeries
variable {F : Type} [Field F] [NumberField F]
variable (A : SArithmeticData F)
local notation "ζ" => A.zeta12
local notation "hζ" => A.primitive_zeta12
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F A.zeta12 A.primitive_zeta12 P)
variable (K : Subgroup (KPLiteralRaw.G F A.zeta12 A.primitive_zeta12)) (hK : IwasawaCompact F A.zeta12 A.primitive_zeta12 K)
variable (f : Flat F A.zeta12 A.primitive_zeta12 K)
abbrev nativeInducingData : SourceReconstruction.InducingData F ζ hζ :=
  fun q => { C.canonical q with polarization := C.polarization q }

theorem scalar_canonical_borel
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (b : (C.canonical q).borel.B)
    (hb : (C.canonical q).heisenberg.π ((C.canonical q).borel.retract b) ∈ (C.polarization q).L)
    (g : KPLiteralRaw.G F ζ hζ) :
    productHCScalar F ζ hζ K hK P f ((finiteInsertion F ζ hζ q b.val).val * g) =
      deltaHalf (C.canonical q).borel b *
        ((C.polarization q).ωL ⟨(C.canonical q).borel.retract b, hb⟩ : ℂ) *
          productHCScalar F ζ hζ K hK P f g := by
  simpa only [LiteralSource.originalProductScalar_HC A P K hK f] using
    LiteralSource.originalProductScalar_finite_borel A P C (f.val 0) (f.property.1 0) q b hb g
theorem productHCScalar_product_right_level :
    ∃ J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      ∀ (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
        (j : productInsertionLevel F ζ hζ T J)
        (a : FiniteProductCover F ζ hζ T)
        (b : KPGlobalTorusFunctionData.finitePart F ζ hζ)
        (m : InfinitePlace F → KPCplxCharacterHaar.ComplexGL2),
        productHCScalar F ζ hζ K hK P f
          ((b * finiteProductInsertion F ζ hζ T (a * j.val)).val * archMatrixInsertion F ζ hζ m) =
        productHCScalar F ζ hζ K hK P f
          ((b * finiteProductInsertion F ζ hζ T a).val * archMatrixInsertion F ζ hζ m) := by
  obtain ⟨J, hJ⟩ := productHCScalar_right_level F ζ hζ K hK P f
  refine ⟨J, ?_⟩
  intro T j a b m
  let d := finiteProductInsertion F ζ hζ T j.val
  have hd : d ∈ J.toOpenSubgroup := finiteProductInsertion_mem_level F ζ hζ T J j.val j.property
  have hdc := (archMatrixInsertion_commutes_finite F ζ hζ m d).eq
  have hc := hJ ((b * finiteProductInsertion F ζ hζ T a).val * archMatrixInsertion F ζ hζ m)
    d.val ⟨d, hd, rfl⟩
  change productHCScalar F ζ hζ K hK P f
    ((b.val * (finiteProductInsertion F ζ hζ T (a * j.val)).val) * archMatrixInsertion F ζ hζ m) = _
  rw [map_mul]
  change productHCScalar F ζ hζ K hK P f
    ((b.val * ((finiteProductInsertion F ζ hζ T a).val * d.val)) * archMatrixInsertion F ζ hζ m) = _
  rw [← mul_assoc, mul_assoc, ← hdc, ← mul_assoc]
  exact hc

theorem productHCScalar_product_smooth
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (b : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (m : InfinitePlace F → KPCplxCharacterHaar.ComplexGL2) :
    SmoothVector KPLocalPrincipalSeries.vectorRightTranslation
      (fun a : FiniteProductCover F ζ hζ T =>
        productHCScalar F ζ hζ K hK P f
          ((b * finiteProductInsertion F ζ hζ T a).val * archMatrixInsertion F ζ hζ m)) := by
  obtain ⟨J, hJ⟩ := productHCScalar_product_right_level A P K hK f
  refine ⟨productInsertionLevel F ζ hζ T J, ?_⟩
  intro j hj
  funext a
  exact hJ T ⟨j, hj⟩ a b m

variable (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
def productHCFamily (b : KPGlobalTorusFunctionData.finitePart F ζ hζ) :
    FiniteProductCover F ζ hζ T → multiPrincipalSeries positiveParameter (InfinitePlace F) :=
  fun a => positiveHCFamily F ζ hζ K hK P f (b * finiteProductInsertion F ζ hζ T a)

theorem productHCFamily_pin (b : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (a : FiniteProductCover F ζ hζ T) (m : InfinitePlace F → ComplexGL2) :
    (productHCFamily A P K hK f T b a).val m =
      productHCScalar F ζ hζ K hK P f
        ((b * finiteProductInsertion F ζ hζ T a).val * archMatrixInsertion F ζ hζ m) := rfl

theorem productHCFamily_orbit_finite (b : KPGlobalTorusFunctionData.finitePart F ζ hζ) :
    Module.Finite ℂ (familyOrbit (productHCFamily A P K hK f T b)) := by
  apply actual_familyOrbit_finite F ζ hζ K hK
    (productHCScalar F ζ hζ K hK P f)
    (productHCScalar_kFinite F ζ hζ K hK P f)
    (fun a : FiniteProductCover F ζ hζ T => (b * finiteProductInsertion F ζ hζ T a).val)
  rfl

theorem productHCFamily_columns_smooth (b : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (m : InfinitePlace F → ComplexGL2) :
    SmoothVector KPLocalPrincipalSeries.vectorRightTranslation
      (fun a : FiniteProductCover F ζ hζ T => (productHCFamily A P K hK f T b a).val m) :=
  productHCScalar_product_smooth A P K hK f T b m
theorem productHCFamily_slot_borel
    (d : outsideStage F ζ hζ T) (j : T) (b : (C.canonical j.val).borel.B)
    (hb : (C.canonical j.val).heisenberg.π ((C.canonical j.val).borel.retract b) ∈ (C.polarization j.val).L)
    (a : FiniteProductCover F ζ hζ T) (m : InfinitePlace F → ComplexGL2) :
    (productHCFamily A P K hK f T d.val (Function.update a j (b.val * a j))).val m =
      (deltaHalf (C.canonical j.val).borel b *
        ((C.polarization j.val).ωL ⟨(C.canonical j.val).borel.retract b, hb⟩ : ℂ)) *
        (productHCFamily A P K hK f T d.val a).val m := by
  have he : Function.update a j (b.val * a j) = Pi.mulSingle j b.val * a := by
    funext i
    by_cases hi : i = j
    · subst i; simp
    · simp [Function.update_of_ne hi, Pi.mulSingle_eq_of_ne hi]
  rw [productHCFamily_pin, productHCFamily_pin, he, map_mul, finiteProductInsertion_single]
  rw [← mul_assoc, (outsideStage_commute_local F ζ hζ T d j b.val).eq, mul_assoc]
  change productHCScalar F ζ hζ K hK P f
    (((finiteInsertion F ζ hζ j.val b.val).val *
      (d.val * finiteProductInsertion F ζ hζ T a).val) * archMatrixInsertion F ζ hζ m) = _
  rw [mul_assoc]
  exact scalar_canonical_borel A P C K hK f j.val b hb _

private theorem independent_slot_covariance
    {ι : Type*} [Fintype ι] [DecidableEq ι] {G : ι → Type*} [∀ i, Group (G i)]
    (φ : (∀ i, G i) → ℂ) (b : ∀ i, G i) (c : ι → ℂ)
    (h : ∀ i g, φ (Function.update g i (b i * g i)) = c i * φ g) (g : ∀ i, G i) :
    φ (b * g) = (∏ i, c i) * φ g := by
  have he (s : Finset ι) :
      φ (fun i => if i ∈ s then b i * g i else g i) = (∏ i ∈ s, c i) * φ g := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      have hf : (fun j => if j ∈ insert i s then b j * g j else g j) =
          Function.update (fun j => if j ∈ s then b j * g j else g j) i (b i * g i) := by
        funext j
        by_cases hj : j = i
        · subst j; simp [hi]
        · simp [hj]
      rw [hf]
      have hx := h i (fun j => if j ∈ s then b j * g j else g j)
      simp only [ite_eq_right hi] at hx
      rw [hx, ih, Finset.prod_insert hi, mul_assoc]
  change φ (fun i => b i * g i) = _
  simpa using he Finset.univ

theorem productHCFamily_product_borel
    (d : outsideStage F ζ hζ T) (b : ∀ j : T, (C.canonical j.val).borel.B)
    (hb : ∀ j, (C.canonical j.val).heisenberg.π ((C.canonical j.val).borel.retract (b j)) ∈ (C.polarization j.val).L)
    (a : FiniteProductCover F ζ hζ T) (m : InfinitePlace F → ComplexGL2) :
    (productHCFamily A P K hK f T d.val (fun j => (b j).val * a j)).val m =
      (∏ j, deltaHalf (C.canonical j.val).borel (b j) *
        ((C.polarization j.val).ωL ⟨(C.canonical j.val).borel.retract (b j), hb j⟩ : ℂ)) *
          (productHCFamily A P K hK f T d.val a).val m := by
  exact independent_slot_covariance
    (fun a : FiniteProductCover F ζ hζ T => (productHCFamily A P K hK f T d.val a).val m)
    (fun j => (b j).val)
    (fun j => deltaHalf (C.canonical j.val).borel (b j) *
      ((C.polarization j.val).ωL ⟨(C.canonical j.val).borel.retract (b j), hb j⟩ : ℂ))
    (fun j g => productHCFamily_slot_borel A P C K hK f T d j (b j) (hb j) g m) a
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductScalarInverse renaming scalarSections → scalarSections
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductScalarInverse renaming scalarCovariance → scalarCovariance
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductScalarInverse renaming scalarTensorEquiv → scalarTensorEquiv
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming Source → Source
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming ProductCover → ProductCover

private theorem productHCFamily_slot_borel_transport
    (d : outsideStage F ζ hζ T) (j : T)
    (R : KPLocalExceptionalConstruction.CanonicalFiniteInducingData F ζ hζ j.val)
    (hR : R = { C.canonical j.val with polarization := C.polarization j.val })
    (b : R.borel.B) (hb : R.heisenberg.π (R.borel.retract b) ∈ R.polarization.L)
    (a : FiniteProductCover F ζ hζ T) (m : InfinitePlace F → ComplexGL2) :
    (productHCFamily A P K hK f T d.val (Function.update a j (b.val * a j))).val m =
      (deltaHalf R.borel b * (R.polarization.ωL ⟨R.borel.retract b, hb⟩ : ℂ)) *
        (productHCFamily A P K hK f T d.val a).val m := by
  cases hR
  exact productHCFamily_slot_borel A P C K hK f T d j b hb a m

theorem productHCFamily_mem_scalarSections
    (d : outsideStage F ζ hζ T) (m : InfinitePlace F → ComplexGL2) :
    (fun a : ProductCover F ζ hζ T =>
      (productHCFamily A P K hK f T d.val a).val m) ∈
        scalarSections F ζ hζ (nativeInducingData A P C) T := by
  refine ⟨?_, (mem_smoothSubmodule _ _).mpr
      (productHCFamily_columns_smooth A P K hK f T d.val m)⟩
  intro b hb a
  exact independent_slot_covariance
    (fun a : FiniteProductCover F ζ hζ T => (productHCFamily A P K hK f T d.val a).val m)
    (fun j => (b j).val)
    (fun j => deltaHalf (nativeInducingData A P C j.val).borel (b j) *
      ((nativeInducingData A P C j.val).polarization.ωL
        ⟨(nativeInducingData A P C j.val).borel.retract (b j), hb j⟩ : ℂ))
    (fun j g => productHCFamily_slot_borel_transport A P C K hK f T d j _
      rfl (b j) (hb j) g m) a

open NativeScalarMixedTensorGeneration
open KPLiteralScalarArchIndependentSlices

theorem productHCFamily_mixed_tensor
    (d : outsideStage F ζ hζ T) :
    ∃ x : (PiTensorProduct ℂ (fun _ : InfinitePlace F => KPLiteralTensor.harmonicPlus)) ⊗[ℂ]
      (PiTensorProduct ℂ (Source F ζ hζ (nativeInducingData A P C) T)),
      ∀ m a, mixedTensorEvaluation F ζ hζ (nativeInducingData A P C) T x m a =
        productHCScalar F ζ hζ K hK P f
          ((d.val * finiteProductInsertion F ζ hζ T a).val * archMatrixInsertion F ζ hζ m) := by
  let := productHCFamily_orbit_finite A P K hK f T d.val
  exact mixed_tensor_exists F ζ hζ (nativeInducingData A P C) T
    (productHCFamily A P K hK f T d.val)
    (productHCFamily_mem_scalarSections A P C K hK f T d)
local instance (j : InfinitePlace F ⊕ T) :
    AddCommGroup (mixedSource F ζ hζ (nativeInducingData A P C) T j) := by
  cases j with
  | inl w => dsimp [mixedSource]; infer_instance
  | inr q => exact SourceReconstruction.localPlusAdd F ζ hζ (nativeInducingData A P C) (Sum.inr q.val)
local instance (j : InfinitePlace F ⊕ T) :
    Module ℂ (mixedSource F ζ hζ (nativeInducingData A P C) T j) := by
  cases j with
  | inl w => dsimp [mixedSource]; infer_instance
  | inr q => exact SourceReconstruction.localPlusModule F ζ hζ (nativeInducingData A P C) (Sum.inr q.val)

theorem productHCFamily_all_slot_tensor
    (d : outsideStage F ζ hζ T) :
    ∃ x : PiTensorProduct ℂ (mixedSource (ι := InfinitePlace F) F ζ hζ (nativeInducingData A P C) T),
      ∀ m a, allSlotEvaluation F ζ hζ (nativeInducingData A P C) T x m a =
        productHCScalar F ζ hζ K hK P f
          ((d.val * finiteProductInsertion F ζ hζ T a).val * archMatrixInsertion F ζ hζ m) := by
  let := productHCFamily_orbit_finite A P K hK f T d.val
  exact all_slot_tensor_exists F ζ hζ (nativeInducingData A P C) T
    (productHCFamily A P K hK f T d.val)
    (productHCFamily_mem_scalarSections A P C K hK f T d)

end DedekindZetaZeroFree.FourierContinuation.CurrentFiniteFamily

end
