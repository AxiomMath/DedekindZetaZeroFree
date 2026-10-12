module

public import DedekindZetaZeroFree.Eisenstein.Residues.Cofactors.BoxFiberIntegral

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators
open NumberField MeasureTheory
local instance currentArchProductMeasurable (F : Type) [Field F] [NumberField F] : MeasurableSpace (InfiniteAdeleRing F) := borel _
local instance currentArchProductBorel (F : Type) [Field F] [NumberField F] : BorelSpace (InfiniteAdeleRing F) := ⟨rfl⟩
namespace DedekindZetaZeroFree.FourierContinuation.CurrentArchProductHaar
variable (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
set_option backward.isDefEq.respectTransparency false

def coordinate (w : InfinitePlace F) (x : InfiniteAdeleRing F) : ℂ :=
  InfinitePlace.Completion.ringEquivComplexOfIsComplex (NumberField.IsTotallyComplex.isComplex w) (x w)

theorem arch_product_integral (f : InfinitePlace F → ℂ → ℂ) :
    (∫ x : InfiniteAdeleRing F, ∏ w, f w (coordinate F w x)
      ∂KPAdditiveHaar.archMeasure F) =
    ∏ w, ∫ z : ℂ, f w z ∂((2 : ENNReal) • KPCplxCharacterHaar.euclideanArea) := by
  let e : InfinitePlace F ≃ {w : InfinitePlace F // w.IsComplex} :=
    { toFun := fun w => ⟨w, NumberField.IsTotallyComplex.isComplex w⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hp (x : InfiniteAdeleRing F) :
      (∏ w, f w (coordinate F w x)) =
        TateTensorProfile.archTensor F (fun w => f w.val) (PoissonArch.infiniteAdeleToSpace F x) := by
    rw [TateTensorProfile.archTensor, PoissonArch.infiniteAdeleToSpace_coordinates]
    rw [← e.prod_comp]
    apply Finset.prod_congr rfl
    intro w _
    simp [coordinate, e, InfiniteAdeleRing.ringEquiv_mixedSpace_apply, InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply]
  simp_rw [hp]
  have he : MeasurableEmbedding ((PoissonArch.infiniteAdeleToSpace F).symm :
      PoissonArch.Space F → InfiniteAdeleRing F) :=
    (PoissonArch.infiniteAdeleToSpace F).symm.toHomeomorph.measurableEmbedding
  rw [KPAdditiveHaar.archMeasure, he.integral_map]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  rw [TateTensorProfile.archTensor_integral]
  rw [← e.prod_comp (fun w => ∫ z : ℂ, f w.val z)]
  simp only [integral_smul_measure, ENNReal.toReal_ofNat, RCLike.real_smul_eq_coe_mul,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  congr 1
  simp [PoissonArch.haarScalar, InfinitePlace.nrComplexPlaces]
  rw [Fintype.card_congr e.symm]

theorem arch_product_integrable (f : InfinitePlace F → ℂ → ℂ)
    (hf : ∀ w, Integrable (f w) ((2 : ENNReal) • KPCplxCharacterHaar.euclideanArea)) :
    Integrable (fun x : InfiniteAdeleRing F => ∏ w, f w (coordinate F w x))
      (KPAdditiveHaar.archMeasure F) := by
  let e : InfinitePlace F ≃ {w : InfinitePlace F // w.IsComplex} :=
    { toFun := fun w => ⟨w, NumberField.IsTotallyComplex.isComplex w⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hp (x : InfiniteAdeleRing F) :
      (∏ w, f w (coordinate F w x)) =
        TateTensorProfile.archTensor F (fun w => f w.val) (PoissonArch.infiniteAdeleToSpace F x) := by
    rw [TateTensorProfile.archTensor, PoissonArch.infiniteAdeleToSpace_coordinates]
    rw [← e.prod_comp]
    apply Finset.prod_congr rfl
    intro w _
    simp [coordinate, e, InfiniteAdeleRing.ringEquiv_mixedSpace_apply,
      InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply]
  simp_rw [hp]
  have he : MeasurableEmbedding ((PoissonArch.infiniteAdeleToSpace F).symm :
      PoissonArch.Space F → InfiniteAdeleRing F) :=
    (PoissonArch.infiniteAdeleToSpace F).symm.toHomeomorph.measurableEmbedding
  rw [KPAdditiveHaar.archMeasure, he.integrable_map_iff]
  change Integrable (fun x => TateTensorProfile.archTensor F (fun w => f w.val)
    ((PoissonArch.infiniteAdeleToSpace F) ((PoissonArch.infiniteAdeleToSpace F).symm x))) _
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  apply TateTensorProfile.archTensor_integrable_of_factors
  intro w
  exact (integrable_smul_measure (by norm_num : (2 : ENNReal) ≠ 0)
    (by norm_num : (2 : ENNReal) ≠ ⊤)).mp (hf w.val)

end DedekindZetaZeroFree.FourierContinuation.CurrentArchProductHaar

end
