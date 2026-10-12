module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.FiniteProducts.ScalarizationCovariance
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.FiniteProducts.SamplingGeneration

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.NativeScalarFiniteProductScalarInverse
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming Cover → Cover
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming Fiber → Fiber
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming Source → Source
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming ProductCover → ProductCover
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming ProductFiber → ProductFiber
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming ProductFunctions → ProductFunctions
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming productCovariance → productCovariance
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming tensorEvaluation → tensorEvaluation
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming tensorEvaluation_covariant → tensorEvaluation_covariant
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming tensorEvaluation_smooth → tensorEvaluation_smooth
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductScalarTransitivity renaming fiberEvaluation → fiberEvaluation
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductScalarTransitivity renaming scalarization → scalarization
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductScalarTransitivity renaming coordinates_scaled → coordinates_scaled
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductScalarTransitivity renaming scalarization_injective → scalarization_injective
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductScalarTransitivity renaming scalarization_polarized_borel → scalarization_polarized_borel
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductScalarTransitivity renaming scalarization_smooth → scalarization_smooth
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductScalarTransitivity renaming scalarization_recovery → scalarization_recovery
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductScalarTransitivity renaming deltaHalf_ne_zero → deltaHalf_ne_zero
open _root_.DedekindZetaZeroFree.NativeScalarFiniteSamplingGeneration renaming functionTensorEquiv → functionTensorEquiv
open _root_.DedekindZetaZeroFree.NativeScalarFiniteSamplingGeneration renaming functionTensorEquiv_formula → functionTensorEquiv_formula
open _root_.DedekindZetaZeroFree.NativeScalarFiniteSamplingGeneration renaming actualTensorSections → actualTensorSections
open _root_.DedekindZetaZeroFree.NativeScalarFiniteSamplingGeneration renaming actualTensorSections_bijective → actualTensorSections_bijective
open _root_.DedekindZetaZeroFree.NativeScalarFiniteSamplingGeneration renaming productSections → productSections
open _root_.DedekindZetaZeroFree.KPLocalStoneVonNeumann renaming inducedCosetEquiv → inducedCosetEquiv
local notation "Coordinates" => KPLiteralTensor.KernelAndHCRange.PointwiseKernel.tensorEvaluation

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (M : FourierContinuation.SourceReconstruction.InducingData F ζ hζ)
variable (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))

 abbrev Torus (q : S) := KPLocalExceptionalConstruction.actualTorus F ζ hζ q.val
 abbrev Polar (q : S) := (M q.val).polarization.L.comap
  (M q.val).heisenberg.π
 abbrev Cosets (q : S) := Torus F ζ hζ S q ⧸ Polar F ζ hζ M S q
local instance (q : S) : Finite (Cosets F ζ hζ M S q) := inferInstance
local instance (q : S) : Fintype (Cosets F ζ hζ M S q) := Fintype.ofFinite _

 def representative (q : S) : Cosets F ζ hζ M S q → Torus F ζ hζ S q :=
  Function.surjInv (QuotientGroup.mk'_surjective (Polar F ζ hζ M S q))

 theorem representative_coset (q : S) (c : Cosets F ζ hζ M S q) :
    QuotientGroup.mk (representative F ζ hζ M S q c) = c :=
  Function.surjInv_eq (QuotientGroup.mk'_surjective (Polar F ζ hζ M S q)) c

 def polarPart (q : S) (t : Torus F ζ hζ S q) : Polar F ζ hζ M S q :=
  ⟨t * (representative F ζ hζ M S q (QuotientGroup.mk t))⁻¹, by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (Polar F ζ hζ M S q) (_ * _⁻¹) = 1
    rw [map_mul, map_inv]
    change QuotientGroup.mk t * (QuotientGroup.mk
      (representative F ζ hζ M S q (QuotientGroup.mk t)))⁻¹ = 1
    rw [representative_coset, mul_inv_cancel]⟩

private theorem polarPart_representative (q : S) (t : Torus F ζ hζ S q) :
    (polarPart F ζ hζ M S q t : Torus F ζ hζ S q) *
      representative F ζ hζ M S q (QuotientGroup.mk t) = t := by
  dsimp [polarPart]
  simp

 def fiberCosets (q : S) : Fiber F ζ hζ M S q ≃ₗ[ℂ]
    (Cosets F ζ hζ M S q → ℂ) :=
  inducedCosetEquiv (Polar F ζ hζ M S q) (M q.val).polarization.ωL.toMonoidHom

private theorem fiberCosets_apply (q : S) (v : Fiber F ζ hζ M S q)
    (c : Cosets F ζ hζ M S q) :
    fiberCosets F ζ hζ M S q v c =
      fiberEvaluation F ζ hζ M S q (representative F ζ hζ M S q c) v := rfl

 def tensorFiberCosets : ProductFiber F ζ hζ M S ≃ₗ[ℂ]
    ((∀ q : S, Cosets F ζ hζ M S q) → ℂ) :=
  (PiTensorProduct.congr (fiberCosets F ζ hζ M S)).trans
    (functionTensorEquiv.trans (LinearEquiv.piCongrRight fun _ =>
      (PiTensorProduct.constantBaseRingEquiv S ℂ).toLinearEquiv))

private theorem tensorFiberCosets_apply (v : ProductFiber F ζ hζ M S)
    (c : ∀ q : S, Cosets F ζ hζ M S q) :
    tensorFiberCosets F ζ hζ M S v c =
      Coordinates (fun q => fiberEvaluation F ζ hζ M S q
        (representative F ζ hζ M S q (c q))) v := by
  induction v using PiTensorProduct.induction_on with
  | smul_tprod a v =>
    simp only [map_smul]
    change a * _ = a * _
    congr 1
    simp only [tensorFiberCosets, LinearEquiv.trans_apply, PiTensorProduct.congr_tprod,
      functionTensorEquiv_formula, PiTensorProduct.map_tprod,
      LinearEquiv.piCongrRight_apply,
      LinearMap.proj_apply, fiberCosets_apply,
      KPLiteralTensor.KernelAndHCRange.PointwiseKernel.tensorEvaluation,
      PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply]
    exact PiTensorProduct.constantBaseRingEquiv_tprod _
  | add v w hv hw => simpa only [map_add, Pi.add_apply] using congrArg₂ (· + ·) hv hw

private theorem coordinates_polarPart (v : ProductFiber F ζ hζ M S)
    (t : ∀ q : S, Torus F ζ hζ S q) :
    Coordinates (fun q => fiberEvaluation F ζ hζ M S q (t q)) v =
      (∏ q, ((M q.val).polarization.ωL (polarPart F ζ hζ M S q (t q)) : ℂ)) *
        tensorFiberCosets F ζ hζ M S v (fun q => QuotientGroup.mk (t q)) := by
  rw [tensorFiberCosets_apply]
  have h (q : S) : fiberEvaluation F ζ hζ M S q (t q) =
      ((M q.val).polarization.ωL (polarPart F ζ hζ M S q (t q)) : ℂ) •
        fiberEvaluation F ζ hζ M S q
          (representative F ζ hζ M S q (QuotientGroup.mk (t q))) := by
    ext u
    change u.val (t q) = _ * u.val _
    conv_lhs => rw [← polarPart_representative F ζ hζ M S q (t q)]
    exact u.property _ _
  simp only [h]
  exact coordinates_scaled F ζ hζ M S _ _ v

open _root_.DedekindZetaZeroFree.KPLocalPrincipalSeries renaming normPower_mul → normPower_mul
open _root_.DedekindZetaZeroFree.KPLocalPrincipalSeries renaming normPower_one → normPower_one

private theorem half_mul (q : S) (b c : (M q.val).borel.B) :
    KPLocalPrincipalSeries.deltaHalf (M q.val).borel (b * c) =
      KPLocalPrincipalSeries.deltaHalf (M q.val).borel b *
        KPLocalPrincipalSeries.deltaHalf (M q.val).borel c := by
  simp only [KPLocalPrincipalSeries.deltaHalf, map_mul, normPower_mul]

private theorem half_one (q : S) :
    KPLocalPrincipalSeries.deltaHalf (M q.val).borel 1 = 1 := by
  simp only [KPLocalPrincipalSeries.deltaHalf, map_one, normPower_one]

 def scalarCovariance : Submodule ℂ (ProductCover F ζ hζ S → ℂ) where
  carrier := { φ | ∀ (b : ∀ q : S, (M q.val).borel.B)
    (hb : ∀ q, (M q.val).heisenberg.π ((M q.val).borel.retract (b q)) ∈
      (M q.val).polarization.L) g,
    φ (fun q => b q * g q) =
      (∏ q, KPLocalPrincipalSeries.deltaHalf (M q.val).borel (b q) *
        ((M q.val).polarization.ωL
          ⟨(M q.val).borel.retract (b q), hb q⟩ : ℂ)) * φ g }
  zero_mem' := by simp
  add_mem' := by intro f h hf hh b hb g; simp only [Pi.add_apply, hf b hb g, hh b hb g, mul_add]
  smul_mem' := by
    intro c f hf b hb g
    simp only [Pi.smul_apply, smul_eq_mul, hf b hb g]
    ring

 def recoveredCoordinate (φ : ProductCover F ζ hζ S → ℂ)
    (t : ∀ q : S, Torus F ζ hζ S q) (g : ProductCover F ζ hζ S) : ℂ :=
  (∏ q, KPLocalPrincipalSeries.deltaHalf (M q.val).borel
    ((M q.val).borel.torus (t q)))⁻¹ *
      φ (fun q => (M q.val).borel.torus (t q) * g q)

 def vectorization : (ProductCover F ζ hζ S → ℂ) →ₗ[ℂ]
    ProductFunctions F ζ hζ M S where
  toFun φ g := (tensorFiberCosets F ζ hζ M S).symm
    (fun c => recoveredCoordinate F ζ hζ M S φ
      (fun q => representative F ζ hζ M S q (c q)) g)
  map_add' φ ψ := by
    funext g
    simp only [Pi.add_apply]
    rw [← map_add]
    congr 1
    funext c
    exact mul_add _ _ _
  map_smul' a φ := by
    funext g
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [← map_smul]
    congr 1
    funext c
    change _ * (a * _) = a * (_ * _)
    ring

private theorem recoveredCoordinate_polarPart
    (φ : ProductCover F ζ hζ S → ℂ) (hφ : φ ∈ scalarCovariance F ζ hζ M S)
    (t : ∀ q : S, Torus F ζ hζ S q) (g : ProductCover F ζ hζ S) :
    recoveredCoordinate F ζ hζ M S φ t g =
      (∏ q, ((M q.val).polarization.ωL (polarPart F ζ hζ M S q (t q)) : ℂ)) *
        recoveredCoordinate F ζ hζ M S φ
          (fun q => representative F ζ hζ M S q (QuotientGroup.mk (t q))) g := by
  let a q := polarPart F ζ hζ M S q (t q)
  let r q := representative F ζ hζ M S q (QuotientGroup.mk (t q))
  let b q := (M q.val).borel.torus (a q)
  have hb q : (M q.val).heisenberg.π ((M q.val).borel.retract (b q)) ∈
      (M q.val).polarization.L := by
    rw [(M q.val).borel.retract_torus]
    exact (a q).property
  have he : (fun q => (b q : Cover F ζ hζ S q) *
      ((M q.val).borel.torus (r q) * g q)) =
      (fun q => (M q.val).borel.torus (t q) * g q) := by
    funext q
    dsimp [b]
    rw [← mul_assoc, ← Subgroup.coe_mul, ← map_mul, polarPart_representative]
  have hd : (∏ q, KPLocalPrincipalSeries.deltaHalf (M q.val).borel
      ((M q.val).borel.torus (t q))) =
      (∏ q, KPLocalPrincipalSeries.deltaHalf (M q.val).borel (b q)) *
        (∏ q, KPLocalPrincipalSeries.deltaHalf (M q.val).borel
          ((M q.val).borel.torus (r q))) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro q _
    rw [← half_mul, ← map_mul]
    congr 2
    exact (polarPart_representative F ζ hζ M S q (t q)).symm
  have hc := hφ b hb (fun q => (M q.val).borel.torus (r q) * g q)
  rw [he] at hc
  have hchar : (∏ q, KPLocalPrincipalSeries.deltaHalf (M q.val).borel (b q) *
      ((M q.val).polarization.ωL
        ⟨(M q.val).borel.retract (b q), hb q⟩ : ℂ)) =
      (∏ q, KPLocalPrincipalSeries.deltaHalf (M q.val).borel (b q)) *
        (∏ q, ((M q.val).polarization.ωL (a q) : ℂ)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro q _
    congr 3
    apply Subtype.ext
    exact (M q.val).borel.retract_torus _
  unfold recoveredCoordinate
  rw [hc, hd, hchar, mul_inv_rev]
  have hn : (∏ q, KPLocalPrincipalSeries.deltaHalf (M q.val).borel (b q)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun q _ => deltaHalf_ne_zero F ζ hζ M S q _)
  dsimp only [a, r]
  field_simp

private theorem vectorization_coordinates
    (φ : ProductCover F ζ hζ S → ℂ) (hφ : φ ∈ scalarCovariance F ζ hζ M S)
    (t : ∀ q : S, Torus F ζ hζ S q) (g : ProductCover F ζ hζ S) :
    Coordinates (fun q => fiberEvaluation F ζ hζ M S q (t q))
      (vectorization F ζ hζ M S φ g) = recoveredCoordinate F ζ hζ M S φ t g := by
  rw [coordinates_polarPart, recoveredCoordinate_polarPart F ζ hζ M S φ hφ]
  congr 1
  change (tensorFiberCosets F ζ hζ M S
    ((tensorFiberCosets F ζ hζ M S).symm _)) _ = _
  rw [LinearEquiv.apply_symm_apply]

 theorem scalarization_vectorization
    (φ : ProductCover F ζ hζ S → ℂ) (hφ : φ ∈ scalarCovariance F ζ hζ M S) :
    scalarization F ζ hζ M S (vectorization F ζ hζ M S φ) = φ := by
  funext g
  change Coordinates _ (vectorization F ζ hζ M S φ g) = _
  rw [vectorization_coordinates F ζ hζ M S φ hφ]
  simp [recoveredCoordinate, map_one, half_one]

private theorem recoveredCoordinate_borel
    (φ : ProductCover F ζ hζ S → ℂ) (hφ : φ ∈ scalarCovariance F ζ hζ M S)
    (t : ∀ q : S, Torus F ζ hζ S q)
    (b : ∀ q : S, (M q.val).borel.B) (g : ProductCover F ζ hζ S) :
    recoveredCoordinate F ζ hζ M S φ t (fun q => b q * g q) =
      (∏ q, KPLocalPrincipalSeries.deltaHalf (M q.val).borel (b q)) *
        recoveredCoordinate F ζ hζ M S φ
          (fun q => t q * (M q.val).borel.retract (b q)) g := by
  let a q := (M q.val).borel.torus (t q)
  let d q := (M q.val).borel.torus
    (t q * (M q.val).borel.retract (b q))
  let c q := a q * b q * (d q)⁻¹
  have hc q : (M q.val).borel.retract (c q) = 1 := by
    simp only [c, a, d, map_mul, map_inv, (M q.val).borel.retract_torus]
    exact mul_inv_cancel _
  have hcp q : (M q.val).heisenberg.π ((M q.val).borel.retract (c q)) ∈
      (M q.val).polarization.L := by rw [hc, map_one]; exact Subgroup.one_mem _
  have hhalf q : KPLocalPrincipalSeries.deltaHalf (M q.val).borel (c q) = 1 := by
    simp only [KPLocalPrincipalSeries.deltaHalf, hc, map_one, normPower_one]
  have hchar q : (M q.val).polarization.ωL
      ⟨(M q.val).borel.retract (c q), hcp q⟩ = 1 := by
    convert map_one (M q.val).polarization.ωL using 1
    exact congrArg _ (Subtype.ext (hc q))
  have hv := hφ c hcp (fun q => d q * g q)
  simp only [hhalf, hchar, Units.val_one, mul_one, Finset.prod_const_one, one_mul] at hv
  have he : (fun q => (c q : Cover F ζ hζ S q) * ((d q : Cover F ζ hζ S q) * g q)) =
      (fun q => (a q : Cover F ζ hζ S q) * ((b q : Cover F ζ hζ S q) * g q)) := by
    funext q
    simp only [c, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [he] at hv
  have hd q : KPLocalPrincipalSeries.deltaHalf (M q.val).borel (d q) =
      KPLocalPrincipalSeries.deltaHalf (M q.val).borel (a q) *
        KPLocalPrincipalSeries.deltaHalf (M q.val).borel (b q) := by
    have hh := half_mul F ζ hζ M S q (c q) (d q)
    have heq' : c q * d q = a q * b q := by dsimp only [c]; group
    rw [heq', hhalf, one_mul, half_mul] at hh
    exact hh.symm
  unfold recoveredCoordinate
  change (∏ q, KPLocalPrincipalSeries.deltaHalf (M q.val).borel (a q))⁻¹ *
      φ (fun q => a q * (b q * g q)) = _
  rw [hv, show (∏ q, KPLocalPrincipalSeries.deltaHalf (M q.val).borel (d q)) =
      (∏ q, KPLocalPrincipalSeries.deltaHalf (M q.val).borel (a q)) *
        (∏ q, KPLocalPrincipalSeries.deltaHalf (M q.val).borel (b q)) by
        simp only [hd, Finset.prod_mul_distrib], mul_inv_rev]
  have hn : (∏ q, KPLocalPrincipalSeries.deltaHalf (M q.val).borel (b q)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun q _ => deltaHalf_ne_zero F ζ hζ M S q _)
  field_simp
  rfl

open _root_.DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.PointwiseKernel renaming tensorEvaluation_map → tensorEvaluation_map

private theorem coordinates_inducingAction
    (v : ProductFiber F ζ hζ M S) (t : ∀ q : S, Torus F ζ hζ S q)
    (b : ∀ q : S, (M q.val).borel.B) :
    Coordinates (fun q => fiberEvaluation F ζ hζ M S q (t q))
      (PiTensorProduct.map (fun q => KPLocalPrincipalSeries.inducingAction
        (M q.val).borel (M q.val).polarization .plus 0 (b q)) v) =
      (∏ q, KPLocalPrincipalSeries.deltaHalf (M q.val).borel (b q)) *
        Coordinates (fun q => fiberEvaluation F ζ hζ M S q
          (t q * (M q.val).borel.retract (b q))) v := by
  rw [tensorEvaluation_map]
  have he : (fun q => (fiberEvaluation F ζ hζ M S q (t q)).comp
      (KPLocalPrincipalSeries.inducingAction (M q.val).borel
        (M q.val).polarization .plus 0 (b q))) =
      fun q => KPLocalPrincipalSeries.deltaHalf (M q.val).borel (b q) •
        fiberEvaluation F ζ hζ M S q (t q * (M q.val).borel.retract (b q)) := by
    funext q
    ext u
    change KPLocalPrincipalSeries.inducingScalar (M q.val).borel 0 (b q) *
      u.val (t q * (M q.val).borel.retract (b q)) = _
    simp [KPLocalPrincipalSeries.inducingScalar, KPLocalPrincipalSeries.normPower,
      fiberEvaluation]
  rw [he, coordinates_scaled]

 theorem vectorization_covariant
    (φ : ProductCover F ζ hζ S → ℂ) (hφ : φ ∈ scalarCovariance F ζ hζ M S) :
    vectorization F ζ hζ M S φ ∈ productCovariance F ζ hζ M S := by
  intro b g
  apply sub_eq_zero.mp
  apply KPLiteralTensor.KernelAndHCRange.PointwiseKernel.tensor_evaluations_separate
    (fun q t => fiberEvaluation F ζ hζ M S q t)
  · intro q v hv
    apply Subtype.ext
    funext t
    exact hv t
  · intro t
    rw [map_sub, coordinates_inducingAction,
      vectorization_coordinates F ζ hζ M S φ hφ,
      vectorization_coordinates F ζ hζ M S φ hφ,
      recoveredCoordinate_borel F ζ hζ M S φ hφ, sub_self]

private theorem vectorization_right_stabilizer
    (φ : ProductCover F ζ hζ S → ℂ) (J : OpenSubgroup (ProductCover F ζ hζ S))
    (hJ : ∀ a ∈ J, KPLocalPrincipalSeries.vectorRightTranslation a φ = φ) :
    ∀ a ∈ J, KPLocalPrincipalSeries.vectorRightTranslation a
      (vectorization F ζ hζ M S φ) = vectorization F ζ hζ M S φ := by
  intro a ha
  funext g
  change (tensorFiberCosets F ζ hζ M S).symm _ = (tensorFiberCosets F ζ hζ M S).symm _
  congr 1
  funext c
  unfold recoveredCoordinate
  congr 1
  have he : (fun q => (M q.val).borel.torus
      (representative F ζ hζ M S q (c q)) * (g * a) q) =
      (fun q => (M q.val).borel.torus
        (representative F ζ hζ M S q (c q)) * g q) * a := by
    funext q
    exact (mul_assoc _ _ _).symm
  rw [he]
  exact congrFun (hJ a ha) _

 theorem vectorization_smooth
    (φ : ProductCover F ζ hζ S → ℂ)
    (hφ : SmoothVector KPLocalPrincipalSeries.vectorRightTranslation φ) :
    SmoothVector KPLocalPrincipalSeries.vectorRightTranslation (vectorization F ζ hζ M S φ) := by
  obtain ⟨J, hJ⟩ := hφ
  exact ⟨J, vectorization_right_stabilizer F ζ hζ M S φ J hJ⟩

 theorem vectorization_scalarization
    (f : ProductFunctions F ζ hζ M S) (hf : f ∈ productCovariance F ζ hζ M S) :
    vectorization F ζ hζ M S (scalarization F ζ hζ M S f) = f := by
  apply scalarization_injective F ζ hζ M S
  · exact vectorization_covariant F ζ hζ M S _
      (scalarization_polarized_borel F ζ hζ M S f hf)
  · exact hf
  · exact scalarization_vectorization F ζ hζ M S _
      (scalarization_polarized_borel F ζ hζ M S f hf)

 def scalarSections : Submodule ℂ (ProductCover F ζ hζ S → ℂ) :=
  scalarCovariance F ζ hζ M S ⊓ smoothSubmodule KPLocalPrincipalSeries.vectorRightTranslation

 def scalarTransitivity : productSections F ζ hζ M S ≃ₗ[ℂ]
    scalarSections F ζ hζ M S where
  toFun f := ⟨scalarization F ζ hζ M S f.val,
    scalarization_polarized_borel F ζ hζ M S f.val f.property.1,
    (mem_smoothSubmodule _ _).mpr (scalarization_smooth F ζ hζ M S f.val f.property.2)⟩
  invFun φ := ⟨vectorization F ζ hζ M S φ.val,
    vectorization_covariant F ζ hζ M S φ.val φ.property.1,
    vectorization_smooth F ζ hζ M S φ.val ((mem_smoothSubmodule _ _).mp φ.property.2)⟩
  left_inv f := Subtype.ext (vectorization_scalarization F ζ hζ M S f.val f.property.1)
  right_inv φ := Subtype.ext (scalarization_vectorization F ζ hζ M S φ.val φ.property.1)
  map_add' f h := Subtype.ext (map_add (scalarization F ζ hζ M S) f.val h.val)
  map_smul' a f := Subtype.ext (map_smul (scalarization F ζ hζ M S) a f.val)

local instance (q : S) : AddCommGroup (Source F ζ hζ M S q) :=
  FourierContinuation.SourceReconstruction.localPlusAdd F ζ hζ M (Sum.inr q.val)
local instance (q : S) : Module ℂ (Source F ζ hζ M S q) :=
  FourierContinuation.SourceReconstruction.localPlusModule F ζ hζ M (Sum.inr q.val)

 def scalarTensorEquiv : PiTensorProduct ℂ (Source F ζ hζ M S) ≃ₗ[ℂ]
    scalarSections F ζ hζ M S :=
  (LinearEquiv.ofBijective (actualTensorSections F ζ hζ M S)
    (actualTensorSections_bijective F ζ hζ M S)).trans (scalarTransitivity F ζ hζ M S)

private theorem scalarTensorEquiv_formula
    (x : PiTensorProduct ℂ (Source F ζ hζ M S)) (g : ProductCover F ζ hζ S) :
    (scalarTensorEquiv F ζ hζ M S x).val g =
      scalarization F ζ hζ M S (tensorEvaluation F ζ hζ M S x) g := rfl

private theorem scalarTensorEquiv_surjective
    (φ : ProductCover F ζ hζ S → ℂ) (hφ : φ ∈ scalarCovariance F ζ hζ M S)
    (hs : SmoothVector KPLocalPrincipalSeries.vectorRightTranslation φ) :
    ∃ x : PiTensorProduct ℂ (Source F ζ hζ M S),
      scalarization F ζ hζ M S (tensorEvaluation F ζ hζ M S x) = φ := by
  obtain ⟨x, hx⟩ := (scalarTensorEquiv F ζ hζ M S).surjective
    ⟨φ, hφ, (mem_smoothSubmodule _ _).mpr hs⟩
  exact ⟨x, congrArg Subtype.val hx⟩

open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductScalarTransitivity renaming scalarization_tensor_slot_action → scalarization_tensor_slot_action
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductScalarTransitivity renaming scalarization_tensor_pure → scalarization_tensor_pure

 theorem scalarTensorEquiv_pure
    (x : ∀ q : S, Source F ζ hζ M S q) (g : ProductCover F ζ hζ S) :
    (scalarTensorEquiv F ζ hζ M S (PiTensorProduct.tprod ℂ x)).val g =
      ∏ q, ((x q).val (g q)).val 1 :=
  scalarization_tensor_pure F ζ hζ M S x g

private theorem scalarTensorEquiv_slot_action
    (q : S) (a : Cover F ζ hζ S q)
    (x : PiTensorProduct ℂ (Source F ζ hζ M S)) (g : ProductCover F ζ hζ S) :
    (scalarTensorEquiv F ζ hζ M S
      (PiTensorProduct.map (Function.update
        (fun _j => LinearMap.id : ∀ j : S, Source F ζ hζ M S j →ₗ[ℂ] Source F ζ hζ M S j)
        q (KPLocalPrincipalSeries.IPlus (M q.val).borel
          (M q.val).polarization a)) x)).val g =
      (scalarTensorEquiv F ζ hζ M S x).val
        (g * Function.update (fun j : S => (1 : Cover F ζ hζ S j)) q a) :=
  scalarization_tensor_slot_action F ζ hζ M S q a x g

end DedekindZetaZeroFree.NativeScalarFiniteProductScalarInverse

end
