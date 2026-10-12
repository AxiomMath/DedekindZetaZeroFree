module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.FiniteProducts.TensorEvaluation
public import DedekindZetaZeroFree.Algebra.TensorProducts.SeparatingEvaluations

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.NativeScalarFiniteProductScalarTransitivity
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming Cover → Cover
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming Fiber → Fiber
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming Source → Source
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming ProductCover → ProductCover
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming ProductFiber → ProductFiber
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming ProductFunctions → ProductFunctions
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming productCovariance → productCovariance
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming tensorEvaluation → tensorEvaluation
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming tensorEvaluation_slot_action → tensorEvaluation_slot_action

local notation "Coordinates" => KPLiteralTensor.KernelAndHCRange.PointwiseKernel.tensorEvaluation

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (M : FourierContinuation.SourceReconstruction.InducingData F ζ hζ)
variable (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))

 def fiberEvaluation (q : S) (t : KPLocalExceptionalConstruction.actualTorus F ζ hζ q.val) :
    Fiber F ζ hζ M S q →ₗ[ℂ] ℂ where
  toFun v := v.val t
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 def scalarization : ProductFunctions F ζ hζ M S →ₗ[ℂ]
    (ProductCover F ζ hζ S → ℂ) where
  toFun f g := Coordinates (fun q => fiberEvaluation F ζ hζ M S q 1) (f g)
  map_add' f h := by
    funext g
    exact map_add (Coordinates (fun q => fiberEvaluation F ζ hζ M S q 1)) (f g) (h g)
  map_smul' c f := by
    funext g
    exact map_smul (Coordinates (fun q => fiberEvaluation F ζ hζ M S q 1)) c (f g)

private theorem fiberEvaluation_torus_action (q : S)
    (t : KPLocalExceptionalConstruction.actualTorus F ζ hζ q.val)
    (v : Fiber F ζ hζ M S q) :
    fiberEvaluation F ζ hζ M S q 1
      (KPLocalPrincipalSeries.inducingAction (M q.val).borel
        (M q.val).polarization .plus 0
        ((M q.val).borel.torus t) v) =
      KPLocalPrincipalSeries.deltaHalf (M q.val).borel
        ((M q.val).borel.torus t) * fiberEvaluation F ζ hζ M S q t v := by
  change KPLocalPrincipalSeries.inducingScalar (M q.val).borel 0
    ((M q.val).borel.torus t) *
    v.val (1 * (M q.val).borel.retract ((M q.val).borel.torus t)) = _
  rw [(M q.val).borel.retract_torus]
  simp [KPLocalPrincipalSeries.inducingScalar, KPLocalPrincipalSeries.normPower,
    fiberEvaluation]

open _root_.DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.PointwiseKernel renaming tensorEvaluation_map → tensorEvaluation_map

 theorem coordinates_scaled
    (c : ∀ _q : S, ℂ) (l : ∀ q : S, Fiber F ζ hζ M S q →ₗ[ℂ] ℂ)
    (v : ProductFiber F ζ hζ M S) :
    Coordinates (fun q => c q • l q) v = (∏ q, c q) * Coordinates l v := by
  induction v using PiTensorProduct.induction_on with
  | smul_tprod a v =>
    simp only [map_smul,
      KPLiteralTensor.KernelAndHCRange.PointwiseKernel.tensorEvaluation,
      PiTensorProduct.lift.tprod,
      MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
      LinearMap.smul_apply, smul_eq_mul]
    rw [Finset.prod_mul_distrib]
    ring
  | add v w hv hw => simp only [map_add, hv, hw, mul_add]

private theorem scalarization_torus
    (f : ProductFunctions F ζ hζ M S) (hf : f ∈ productCovariance F ζ hζ M S)
    (t : ∀ q : S, KPLocalExceptionalConstruction.actualTorus F ζ hζ q.val)
    (g : ProductCover F ζ hζ S) :
    scalarization F ζ hζ M S f
      (fun q => (M q.val).borel.torus (t q) * g q) =
      (∏ q, KPLocalPrincipalSeries.deltaHalf (M q.val).borel
        ((M q.val).borel.torus (t q))) *
      Coordinates (fun q => fiberEvaluation F ζ hζ M S q (t q)) (f g) := by
  change Coordinates _ (f _) = _
  rw [hf, tensorEvaluation_map]
  have he : (fun q => (fiberEvaluation F ζ hζ M S q 1).comp
        (KPLocalPrincipalSeries.inducingAction (M q.val).borel
          (M q.val).polarization .plus 0
          ((M q.val).borel.torus (t q)))) =
      fun q => KPLocalPrincipalSeries.deltaHalf (M q.val).borel
        ((M q.val).borel.torus (t q)) •
          fiberEvaluation F ζ hζ M S q (t q) := by
    funext q
    ext v
    exact fiberEvaluation_torus_action F ζ hζ M S q (t q) v
  rw [he, coordinates_scaled]

 theorem deltaHalf_ne_zero (q : S) (b : (M q.val).borel.B) :
    KPLocalPrincipalSeries.deltaHalf (M q.val).borel b ≠ 0 := by
  exact Complex.exp_ne_zero _

 theorem scalarization_recovery
    (f : ProductFunctions F ζ hζ M S) (hf : f ∈ productCovariance F ζ hζ M S)
    (t : ∀ q : S, KPLocalExceptionalConstruction.actualTorus F ζ hζ q.val)
    (g : ProductCover F ζ hζ S) :
    Coordinates (fun q => fiberEvaluation F ζ hζ M S q (t q)) (f g) =
      (∏ q, KPLocalPrincipalSeries.deltaHalf (M q.val).borel
        ((M q.val).borel.torus (t q)))⁻¹ *
      scalarization F ζ hζ M S f
        (fun q => (M q.val).borel.torus (t q) * g q) := by
  rw [scalarization_torus F ζ hζ M S f hf, inv_mul_cancel_left₀]
  exact Finset.prod_ne_zero_iff.mpr fun q _ => deltaHalf_ne_zero F ζ hζ M S q _

 theorem scalarization_injective
    (f h : ProductFunctions F ζ hζ M S)
    (hf : f ∈ productCovariance F ζ hζ M S)
    (hh : h ∈ productCovariance F ζ hζ M S)
    (he : scalarization F ζ hζ M S f = scalarization F ζ hζ M S h) : f = h := by
  funext g
  apply sub_eq_zero.mp
  apply KPLiteralTensor.KernelAndHCRange.PointwiseKernel.tensor_evaluations_separate
    (fun q t => fiberEvaluation F ζ hζ M S q t)
  · intro q v hv
    apply Subtype.ext
    funext t
    exact hv t
  · intro t
    rw [map_sub, scalarization_recovery F ζ hζ M S f hf,
      scalarization_recovery F ζ hζ M S h hh, he, sub_self]

private theorem fiberEvaluation_borel_action (q : S)
    (b : (M q.val).borel.B) (v : Fiber F ζ hζ M S q) :
    fiberEvaluation F ζ hζ M S q 1
      (KPLocalPrincipalSeries.inducingAction (M q.val).borel
        (M q.val).polarization .plus 0 b v) =
      KPLocalPrincipalSeries.deltaHalf (M q.val).borel b *
        fiberEvaluation F ζ hζ M S q ((M q.val).borel.retract b) v := by
  change KPLocalPrincipalSeries.inducingScalar (M q.val).borel 0 b *
    v.val (1 * (M q.val).borel.retract b) = _
  simp [KPLocalPrincipalSeries.inducingScalar, KPLocalPrincipalSeries.normPower,
    fiberEvaluation]

private theorem fiberEvaluation_polarized_borel_action (q : S)
    (b : (M q.val).borel.B)
    (hb : (M q.val).heisenberg.π ((M q.val).borel.retract b) ∈
      (M q.val).polarization.L)
    (v : Fiber F ζ hζ M S q) :
    fiberEvaluation F ζ hζ M S q 1
      (KPLocalPrincipalSeries.inducingAction (M q.val).borel
        (M q.val).polarization .plus 0 b v) =
      (KPLocalPrincipalSeries.deltaHalf (M q.val).borel b *
        ((M q.val).polarization.ωL
          ⟨(M q.val).borel.retract b, hb⟩ : ℂ)) *
        fiberEvaluation F ζ hζ M S q 1 v := by
  rw [fiberEvaluation_borel_action]
  have hv := v.property ⟨(M q.val).borel.retract b, hb⟩ 1
  simp only [mul_one] at hv
  change _ * v.val ((M q.val).borel.retract b) = _ * v.val 1
  rw [hv, mul_assoc]
  rfl

 theorem scalarization_polarized_borel
    (f : ProductFunctions F ζ hζ M S) (hf : f ∈ productCovariance F ζ hζ M S)
    (b : ∀ q : S, (M q.val).borel.B)
    (hb : ∀ q, (M q.val).heisenberg.π ((M q.val).borel.retract (b q)) ∈
      (M q.val).polarization.L)
    (g : ProductCover F ζ hζ S) :
    scalarization F ζ hζ M S f (fun q => b q * g q) =
      (∏ q, KPLocalPrincipalSeries.deltaHalf (M q.val).borel (b q) *
        ((M q.val).polarization.ωL
          ⟨(M q.val).borel.retract (b q), hb q⟩ : ℂ)) *
      scalarization F ζ hζ M S f g := by
  change Coordinates _ (f _) = _
  rw [hf, tensorEvaluation_map]
  have he : (fun q => (fiberEvaluation F ζ hζ M S q 1).comp
        (KPLocalPrincipalSeries.inducingAction (M q.val).borel
          (M q.val).polarization .plus 0 (b q))) =
      fun q => (KPLocalPrincipalSeries.deltaHalf (M q.val).borel (b q) *
        ((M q.val).polarization.ωL
          ⟨(M q.val).borel.retract (b q), hb q⟩ : ℂ)) •
          fiberEvaluation F ζ hζ M S q 1 := by
    funext q
    ext v
    exact fiberEvaluation_polarized_borel_action F ζ hζ M S q (b q) (hb q) v
  rw [he, coordinates_scaled]
  rfl

private theorem scalarization_right_stabilizer
    (f : ProductFunctions F ζ hζ M S)
    (J : OpenSubgroup (ProductCover F ζ hζ S))
    (hJ : ∀ a ∈ J, KPLocalPrincipalSeries.vectorRightTranslation a f = f) :
    ∀ a ∈ J, KPLocalPrincipalSeries.vectorRightTranslation a
      (scalarization F ζ hζ M S f) = scalarization F ζ hζ M S f := by
  intro a ha
  funext g
  exact congrArg (Coordinates (fun q => fiberEvaluation F ζ hζ M S q 1))
    (congrFun (hJ a ha) g)

 theorem scalarization_smooth
    (f : ProductFunctions F ζ hζ M S)
    (hf : SmoothVector KPLocalPrincipalSeries.vectorRightTranslation f) :
    SmoothVector KPLocalPrincipalSeries.vectorRightTranslation
      (scalarization F ζ hζ M S f) := by
  obtain ⟨J, hJ⟩ := hf
  exact ⟨J, scalarization_right_stabilizer F ζ hζ M S f J hJ⟩

 theorem scalarization_tensor_pure (x : ∀ q : S, Source F ζ hζ M S q)
    (g : ProductCover F ζ hζ S) :
    scalarization F ζ hζ M S (tensorEvaluation F ζ hζ M S (PiTensorProduct.tprod ℂ x)) g =
      ∏ q, ((x q).val (g q)).val 1 := by
  change Coordinates _ (PiTensorProduct.map _ (PiTensorProduct.tprod ℂ x)) = _
  simp [PiTensorProduct.map_tprod,
    KPLiteralTensor.KernelAndHCRange.PointwiseKernel.tensorEvaluation,
    PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, fiberEvaluation]
  rfl

 theorem scalarization_tensor_slot_action
    (q : S) (a : Cover F ζ hζ S q)
    (x : PiTensorProduct ℂ (Source F ζ hζ M S)) (g : ProductCover F ζ hζ S) :
    scalarization F ζ hζ M S
      (tensorEvaluation F ζ hζ M S
        (PiTensorProduct.map (Function.update
          (fun _j => LinearMap.id : ∀ j : S, Source F ζ hζ M S j →ₗ[ℂ] Source F ζ hζ M S j)
          q (KPLocalPrincipalSeries.IPlus (M q.val).borel
            (M q.val).polarization a)) x)) g =
    scalarization F ζ hζ M S (tensorEvaluation F ζ hζ M S x)
      (g * Function.update (fun j : S => (1 : Cover F ζ hζ S j)) q a) := by
  exact congrArg (Coordinates (fun j => fiberEvaluation F ζ hζ M S j 1))
    (tensorEvaluation_slot_action F ζ hζ M S q a x g)

end DedekindZetaZeroFree.NativeScalarFiniteProductScalarTransitivity

end
