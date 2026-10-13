module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.FixedData

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RowNonprincipal

noncomputable section

open DedekindZetaZeroFree NumberField
open PrincipalMellinComparison.NonprincipalContinuation

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem inducers_nonprincipal (u : D.Row) (hu : u.u ≠ 1) :
    ¬ (D.inducers u).plus.character.IsPrincipal ∧ ¬ (D.omega u).character.IsPrincipal := by
  classical
  obtain ⟨h0, hmem⟩ := u.isRep
  let f : PrincipalMellinComparison.Frequency D.recipe := ⟨⟨u.u, h0⟩, hmem⟩
  have hf : f ≠ PrincipalMellinComparison.principalFrequency D.recipe := by
    intro h
    apply hu
    have := congrArg (fun x : PrincipalMellinComparison.Frequency D.recipe => x.val.val) h
    simpa [f, PrincipalMellinComparison.principalFrequency] using this
  let U : AllRowEuler.InitialSeparation.RawFrequency D.recipe.A :=
    { u := u.u, ideal := u.toFrequency.ideal, generates := u.toFrequency.generates,
      sixthFree := u.toFrequency.sixthFree }
  have hU : U.u = f.val.val := rfl
  have hP : ∀ I : D.recipe.A.Exterior,
      AllRowEuler.InitialSeparation.plusExteriorCoefficient D.recipe.σ U I =
        Detector.deletedPrimitiveIdealCoefficient F (D.inducers u).plus
          (RawHeckeRows.rawDeletionSet U) I.val := by
    intro I
    have h := (D.inducers u).plus_mask I.val
    unfold FrequencyCharacterMasks.plusCoefficient at h
    rw [dif_pos I.property] at h
    exact h
  have hM : ∀ I : D.recipe.A.Exterior,
      AllRowEuler.InitialSeparation.minusExteriorCoefficient D.recipe.σ D.recipe.target U I =
        Detector.deletedPrimitiveIdealCoefficient F (D.inducers u).minus
          (RawHeckeRows.rawDeletionSet U) I.val := by
    intro I
    have h := (D.inducers u).minus_mask I.val
    unfold FrequencyCharacterMasks.minusCoefficient FrequencyCharacterMasks.plusCoefficient at h
    rw [dif_pos I.property] at h
    exact h
  exact RawHeckeRows.actual_raw_inducers_nonprincipal D.recipe f U hU hf
    (D.inducers u).plus (D.inducers u).minus hP hM

end

end DedekindZetaZeroFree.Quantitative.RowNonprincipal
