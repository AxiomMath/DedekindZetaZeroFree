module

public import DedekindZetaZeroFree.Eisenstein.Induction.ScalarCompactPicturesAndLocalQuotientTensors

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.SourceReconstruction
abbrev InducingData (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12) :=
  ∀ q : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
    KPLocalExceptionalConstruction.CanonicalFiniteInducingData F ζ hζ q
abbrev localPlus (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (M : InducingData F ζ hζ) : KPHilbert.Place F → Type
  | Sum.inl _ => KPLiteralTensor.harmonicPlus
  | Sum.inr q => KPLocalPrincipalSeries.sectionSpace (M q).borel (M q).polarization .plus 0
instance localPlusAdd (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (M : InducingData F ζ hζ) (v : KPHilbert.Place F) : AddCommGroup (localPlus F ζ hζ M v) := by
  cases v <;> dsimp [localPlus] <;> infer_instance
instance localPlusModule (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (M : InducingData F ζ hζ) (v : KPHilbert.Place F) : Module ℂ (localPlus F ζ hζ M v) := by
  cases v <;> dsimp [localPlus] <;> infer_instance
end DedekindZetaZeroFree.FourierContinuation.SourceReconstruction
noncomputable section
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open scoped NumberField Classical TensorProduct
open NumberField
namespace DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (M : FourierContinuation.SourceReconstruction.InducingData F ζ hζ)
variable (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
 abbrev Cover (q : S) := KPLocalExceptionalConstruction.ActualCover F ζ hζ q.val
 abbrev Fiber (q : S) : Type := ↥(KPLocalStoneVonNeumann.InducedModule (M q.val).polarization)
 abbrev Source (q : S) := FourierContinuation.SourceReconstruction.localPlus F ζ hζ M (Sum.inr q.val)
 abbrev ProductCover := ∀ q : S, Cover F ζ hζ S q
 abbrev ProductFiber := PiTensorProduct ℂ (Fiber F ζ hζ M S)
 abbrev ProductFunctions := ProductCover F ζ hζ S → ProductFiber F ζ hζ M S

 def evaluation (q : S) (g : Cover F ζ hζ S q) :
    Source F ζ hζ M S q →ₗ[ℂ] Fiber F ζ hζ M S q where
  toFun f := f.val g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 def tensorEvaluation : PiTensorProduct ℂ (Source F ζ hζ M S) →ₗ[ℂ]
    ProductFunctions F ζ hζ M S where
  toFun x g := PiTensorProduct.map (fun q => evaluation F ζ hζ M S q (g q)) x
  map_add' x y := by funext g; exact map_add _ x y
  map_smul' c x := by funext g; exact map_smul _ c x

 def productCovariance : Submodule ℂ (ProductFunctions F ζ hζ M S) where
  carrier := { f | ∀ (b : ∀ q : S, (M q.val).borel.B) g,
    f (fun q => b q * g q) =
      PiTensorProduct.map (fun q =>
        KPLocalPrincipalSeries.inducingAction (M q.val).borel
          (M q.val).polarization .plus 0 (b q)) (f g) }
  zero_mem' := by intro b g; exact (map_zero _).symm
  add_mem' := by intro f h hf hh b g; exact (congrArg₂ (· + ·) (hf b g) (hh b g)).trans (map_add _ _ _).symm
  smul_mem' := by intro c f hf b g; exact (congrArg (c • ·) (hf b g)).trans (map_smul _ _ _).symm

 theorem tensorEvaluation_covariant
    (x : PiTensorProduct ℂ (Source F ζ hζ M S)) :
    tensorEvaluation F ζ hζ M S x ∈ productCovariance F ζ hζ M S := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    rw [map_smul]
    apply (productCovariance F ζ hζ M S).smul_mem c
    intro b g
    change PiTensorProduct.map _ (PiTensorProduct.tprod ℂ x) =
      PiTensorProduct.map _ (PiTensorProduct.map _ (PiTensorProduct.tprod ℂ x))
    simp only [PiTensorProduct.map_tprod]
    congr 1
    funext q
    exact (x q).property.1 (b q) (g q)
  | add x y hx hy =>
    rw [map_add]
    exact (productCovariance F ζ hζ M S).add_mem hx hy

private theorem tensorEvaluation_smooth_pure
    (x : ∀ q : S, Source F ζ hζ M S q) :
    SmoothVector KPLocalPrincipalSeries.vectorRightTranslation
      (tensorEvaluation F ζ hζ M S (PiTensorProduct.tprod ℂ x)) := by
  choose J hJ using fun q => (x q).property.2
  let U : OpenSubgroup (ProductCover F ζ hζ S) :=
    { toSubgroup := Subgroup.pi Set.univ (fun q => (J q).toSubgroup)
      isOpen' := isOpen_set_pi Set.finite_univ (fun q _ => (J q).isOpen) }
  refine ⟨U, ?_⟩
  intro j hj
  funext g
  change PiTensorProduct.map _ (PiTensorProduct.tprod ℂ x) =
    PiTensorProduct.map _ (PiTensorProduct.tprod ℂ x)
  simp only [PiTensorProduct.map_tprod]
  congr 1
  funext q
  exact congrFun (hJ q (j q) (hj q (Set.mem_univ q))) (g q)

 theorem tensorEvaluation_smooth
    (x : PiTensorProduct ℂ (Source F ζ hζ M S)) :
    SmoothVector KPLocalPrincipalSeries.vectorRightTranslation
      (tensorEvaluation F ζ hζ M S x) := by
  apply (mem_smoothSubmodule _ _).mp
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    rw [map_smul]
    exact (smoothSubmodule _).smul_mem c
      ((mem_smoothSubmodule _ _).mpr (tensorEvaluation_smooth_pure F ζ hζ M S x))
  | add x y hx hy =>
    rw [map_add]
    exact (smoothSubmodule _).add_mem hx hy

 theorem tensorEvaluation_slot_action
    (q : S) (a : Cover F ζ hζ S q)
    (x : PiTensorProduct ℂ (Source F ζ hζ M S)) (g : ProductCover F ζ hζ S) :
    tensorEvaluation F ζ hζ M S
      (PiTensorProduct.map (Function.update
        (fun _j => LinearMap.id : ∀ j : S, Source F ζ hζ M S j →ₗ[ℂ] Source F ζ hζ M S j)
        q (KPLocalPrincipalSeries.IPlus (M q.val).borel
          (M q.val).polarization a)) x) g =
      tensorEvaluation F ζ hζ M S x
        (g * Function.update (fun j : S => (1 : Cover F ζ hζ S j)) q a) := by
  change PiTensorProduct.map _ (PiTensorProduct.map _ x) = PiTensorProduct.map _ x
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  congr 2
  funext j
  ext f
  by_cases hj : j = q
  · subst j
    simp only [Function.update_self, LinearMap.comp_apply, evaluation, Pi.mul_apply]
    rfl
  · simp only [Function.update_of_ne hj, LinearMap.comp_apply, LinearMap.id_apply,
      evaluation, Pi.mul_apply, mul_one]

end DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation

end
end
