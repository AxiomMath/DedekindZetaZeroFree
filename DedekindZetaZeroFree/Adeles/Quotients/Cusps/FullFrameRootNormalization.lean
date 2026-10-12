module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.CuspCoordinatesAndTruncation

@[expose] public section

noncomputable section
open scoped NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace DedekindZetaZeroFree.KPGlobalResidualKernel.RawStageL2.Measurability
open KPAdelicCoverRestrictedProduct

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private theorem finiteProjection_local_infinite (v : NumberField.InfinitePlace F)
    (g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl v)) :
    KPCuspGenuineMonodromy.finiteProjection F ζ hζ
      (scalarQuotient F ζ hζ (localInjection F ζ hζ (Sum.inl v) g)) = 1 := by
  classical
  change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map (RingHom.snd _ _)
    (restrictedProjection F ζ hζ (localToRestricted F ζ hζ (Sum.inl v) g))) = 1
  have he : Matrix.GeneralLinearGroup.map (RingHom.snd _ _)
      (restrictedProjection F ζ hζ (localToRestricted F ζ hζ (Sum.inl v) g)) = 1 := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    apply Subtype.ext
    funext q
    have h := restrictedProjection_eval F ζ hζ (localToRestricted F ζ hζ (Sum.inl v) g) (Sum.inr q)
    have hn : localToRestricted F ζ hζ (Sum.inl v) g (Sum.inr q) = 1 := by
      exact RestrictedProduct.mulSingle_eq_of_ne' _ _ (by simp)
    rw [hn, map_one] at h
    convert congrArg (fun m => m i j) h using 1
    · rfl
    · by_cases hij : i = j <;> subst_vars <;> simp [Matrix.one_apply, *] <;> rfl
  rw [he, map_one]

theorem finiteProjection_archimedeanInsertion (a : KPSmoothActualFlowData.GInfinity F) :
    KPCuspGenuineMonodromy.finiteProjection F ζ hζ
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a) = 1 := by
  unfold KPSmoothActualFlowData.archimedeanInsertion
  rw [map_list_prod]
  simp only [List.map_map, Function.comp_def, finiteProjection_local_infinite]
  simp

theorem finiteProjection_rationalLift (σ : KPCuspArithmetic.PGL2 F) :
    KPCuspGenuineMonodromy.finiteProjection F ζ hζ
      (KPMsClearedTruncationL2.rationalLift F ζ hζ σ) = KPFiniteComponents.diagonal F σ := by
  obtain ⟨m, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective σ
  rw [KPMsClearedTruncationL2.rationalLift_mk]
  change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map (RingHom.snd _ _)
    (projection F ζ hζ (rationalHom F ζ hζ m))) = _
  exact congrArg (fun k => Matrix.ProjGenLinGroup.mk
    (Matrix.GeneralLinearGroup.map (RingHom.snd _ _) k))
      (projection_rationalSection F ζ hζ m)

variable {F ζ hζ}
local instance : MulAction (KPCuspArithmetic.PGL2 F) (KPArch.Space (KPCuspLogShape.dimension F)) :=
  KPCuspSiegel.instMulActionPGL2SpaceDimension F
open KPMsClearedTruncationL2
open KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent
variable {C : ModelData F ζ hζ} {D : Iwasawa F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
variable {A : KPMsRationalCompactCrossPairing.RawCompactComparison F ζ hζ C D R P H}
variable {U : Level F ζ hζ}

end DedekindZetaZeroFree.KPGlobalResidualKernel.RawStageL2.Measurability

end
