module

public import DedekindZetaZeroFree.Theta.Whittaker.Complex.RestrictedTensorInsertionBounds
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.Complex.OperatorWordBounds
public import DedekindZetaZeroFree.Eisenstein.Residues.RestrictedTensors.OperatorWords

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ComplexLines
open LiteralSource MomentSources HCGeneration TensorActionSource
open KPContActualSphericalRightFieldIdentification KPGlobalResidualConstruction
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
variable (H : ∀ q, LocalImageData R q)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

 theorem stageImageWord_variable_slot
    (s : RestrictedTensorSimple.Level (bad R.A P C))
    (x : ∀ j : s.val, actualLocal R (imageData R P C H) j.val)
    (w : InfinitePlace F) (hw : Sum.inl w ∈ s.val)
    (b : List (Fin (groupDimension F))) :
    ∃ (y : ∀ j : s.val, actualLocal R (imageData R P C H) j.val)
      (a : List ComplexGenerator), ∀ v : complexCore,
      stageImageWord R P C H s (b.map StageGenerator.lie)
        (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inl w,hw⟩ v)) =
      PiTensorProduct.tprod ℂ (Function.update y ⟨Sum.inl w,hw⟩ (complexWord a v)) := by
  induction b with
  | nil => exact ⟨x,[],fun _ => rfl⟩
  | cons i b ih =>
    obtain ⟨y,a,ha⟩ := ih
    let q := (actualLieIndexEquiv (F := F) i).1
    let k := (actualLieIndexEquiv (F := F) i).2
    have hq : Sum.inl q ∈ s.val := s.property (by simp [bad, ScalarAbsorption.fullBad])
    let j : s.val := ⟨Sum.inl q,hq⟩
    let j₀ : s.val := ⟨Sum.inl w,hw⟩
    let T := localOperation R (imageData R P C H) (Sum.inl q) [Sum.inr k]
    have hstep (v : complexCore) :
        stageImageWord R P C H s ((i::b).map StageGenerator.lie)
          (PiTensorProduct.tprod ℂ (Function.update x j₀ v)) =
        PiTensorProduct.tprod ℂ (Function.update (Function.update y j₀ (complexWord a v)) j
          (T ((Function.update y j₀ (complexWord a v)) j))) := by
      change tensorSlot j T (stageImageWord R P C H s (b.map StageGenerator.lie)
        (PiTensorProduct.tprod ℂ (Function.update x j₀ v))) = _
      rw [ha, tensorSlot_tprod]
    by_cases hqw : q = w
    · have hj : j = j₀ := Subtype.ext (congrArg Sum.inl hqw)
      refine ⟨y,Sum.inr k :: a,?_⟩
      intro v
      rw [hstep]
      subst q
      simp only [j,j₀] at hj
      cases hqw
      simp only [j,j₀,Function.update_self,Function.update_idem]
      rfl
    · have hj : j ≠ j₀ := fun h => hqw (Sum.inl.inj (congrArg Subtype.val h))
      refine ⟨Function.update y j (T (y j)),a,?_⟩
      intro v
      rw [hstep]
      change PiTensorProduct.tprod ℂ _ = PiTensorProduct.tprod ℂ
        (Function.update (Function.update y j (T (y j))) j₀ (complexWord a v))
      congr 1
      funext z
      by_cases hz : z = j
      · subst z
        simp only [Function.update_self,Function.update_of_ne hj]
      · by_cases hz₀ : z = j₀
        · subst z
          simp only [Function.update_self,Function.update_of_ne (Ne.symm hj)]
        · simp only [Function.update_of_ne hz,Function.update_of_ne hz₀]

end DedekindZetaZeroFree.FourierContinuation.ComplexLines

end
