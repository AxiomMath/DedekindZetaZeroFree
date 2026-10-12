module

public import DedekindZetaZeroFree.Theta.Whittaker.SelectedJacquet.SelectedJacquetImage
public import DedekindZetaZeroFree.Theta.Whittaker.SelectedJacquet.SelectedJacquetTransport
public import DedekindZetaZeroFree.Theta.Whittaker.SelectedJacquet.SelectedWeylPeriod

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.SheetRescaling
open MomentSources NumberField KPCplxCharacterHaar KPCplxPrincipalSeriesCharts
open KPLiteralScalarHCCompactOrbit KPAdelicCoverRestrictedProduct
open KPRationalAdelicSplitting (eval_localIdele)
open KPCplxJacquetFunctional (standardWeylJacquet)
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem archMatrixInsertion_local_diagonal (w : InfinitePlace F) (y : ℂˣ) :
    archMatrixInsertion F R.A.zeta12 R.A.primitive_zeta12
      (Function.update (fun _ => 1) w (diagonal y)) =
    KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
      (KPRationalAdelicSplitting.localIdele F (Sum.inl w)
        (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (R.A.complex_place w)).symm.toMonoidHom y)) := by
  unfold KPRationalAdelicSplitting.pglA KPRationalAdelicSplitting.A
  change scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
    (amalgamation F R.A.zeta12 R.A.primitive_zeta12
      (KPLiteralChamber.sectionTuple F R.A.zeta12 R.A.primitive_zeta12 _)) = _
  congr 2
  apply RestrictedProduct.ext
  intro p
  change KPLiteralChamber.sectionTuple F R.A.zeta12 R.A.primitive_zeta12
    (Function.update (fun _ => 1) w (diagonal y)) p =
      KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 p
        (Units.map (adeleEval F p) (KPRationalAdelicSplitting.localIdele F (Sum.inl w)
          (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (R.A.complex_place w)).symm.toMonoidHom y)))
  have he := eval_localIdele F (Sum.inl w) p
    (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (R.A.complex_place w)).symm.toMonoidHom y)
  have he' : Units.map (adeleEval F p)
      (KPRationalAdelicSplitting.localIdele F (Sum.inl w)
        (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (R.A.complex_place w)).symm.toMonoidHom y)) =
      Pi.mulSingle (M := fun v => (KPHilbert.Completion F v)ˣ) (Sum.inl w)
        (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (R.A.complex_place w)).symm.toMonoidHom y) p :=
    Units.ext (congrArg Units.val he)
  rw [he']
  cases p with
  | inr q =>
    simp only [Pi.mulSingle_eq_of_ne (Sum.inr_ne_inl), KPStandardLocalRootLifts.A_one]
    rfl
  | inl u =>
    by_cases hu : u = w
    · subst u
      simp only [Function.update_self, Pi.mulSingle_eq_same]
      change KPLocalCover.sectionMap F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w) _ =
        KPLocalCover.sectionMap F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w) _
      congr 1
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [KPCplxCharacterHaar.diagonal, KPStandardLocalRootLifts.A, KubotaRankTwo.d,
          Matrix.GeneralLinearGroup.map]
    · rw [Pi.mulSingle_eq_of_ne (Sum.inl_injective.ne hu), KPStandardLocalRootLifts.A_one]
      change KPLocalCover.sectionMap F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl u)
        (Matrix.GeneralLinearGroup.map
          (InfinitePlace.Completion.ringEquivComplexOfIsComplex (R.A.complex_place u)).symm.toRingHom
          (Function.update (fun _ : InfinitePlace F => (1 : ComplexGL2)) w
            (KPCplxCharacterHaar.diagonal y) u)) = 1
      rw [Function.update_of_ne hu, map_one]
      rfl

theorem archMatrixInsertion_local_weyl (w : InfinitePlace F) :
    archMatrixInsertion F R.A.zeta12 R.A.primitive_zeta12
      (Function.update (fun _ => 1) w weyl) =
    scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (localInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w)
        (KPRationalAdelicSplitting.WCoordinates F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w))) := by
  rw [← complexCompactLift_weyl R.A.zeta12 R.A.primitive_zeta12 w,
    ← KPLiteralScalarHCCompactAction.archMatrixInsertion_compact_single]
  apply KPLiteralScalarHCLocalCovariance.archMatrixInsertion_projective_congr
  intro u
  by_cases hu : u = w
  · subst u
    simp only [Function.update_self]
    apply (Matrix.ProjGenLinGroup.mk_eq_mk_iff).mpr
    refine ⟨Units.mk0 Complex.I Complex.I_ne_zero, ?_⟩
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [complexSU2Embedding, compactWeyl, weyl, Matrix.mul_apply]
  · simp [Function.update_of_ne hu]

theorem selected_weyl_jacquet_identity {N : TraceHaarTransport R} (C : JointDigitDescentSources R N)
    (v : R.A.UnitQuotient) (w : InfinitePlace F) :
    ∃ (κ : ℂˣ) (f : PrincipalSeries positiveParameter),
      selectedComplexWeyl R C v w = standardWeylJacquet κ f := by
  obtain ⟨f,hf⟩ := selected_residue_jacquet_image R C.sources C.realization v w
  let a := fourier R C.sources.dq (C.realization.theta v) 1
  have ha : a ≠ 0 := ThetaExpansion.first_root_forward_period_ne_zero R C v
  let κ : ℂˣ := (Units.mk0 a ha)⁻¹
  refine ⟨κ,f,?_⟩
  funext y
  have hi : archMatrixInsertion F R.A.zeta12 R.A.primitive_zeta12
      (Function.update (fun _ => 1) w (diagonal y * weyl)) =
      archMatrixInsertion F R.A.zeta12 R.A.primitive_zeta12
        (Function.update (fun _ => 1) w (diagonal y)) *
      archMatrixInsertion F R.A.zeta12 R.A.primitive_zeta12
        (Function.update (fun _ => 1) w weyl) := by
    rw [← map_mul]
    congr 1
    funext u
    by_cases hu : u = w <;> simp [hu]
  have h := hf (diagonal y * weyl)
  rw [hi, archMatrixInsertion_local_diagonal R w y, archMatrixInsertion_local_weyl R w] at h
  unfold selectedComplexWeyl ThetaExpansion.normalizedLocalWeylValue standardWeylJacquet
  rw [h]
  simp only [κ, a, Units.val_inv_eq_inv_val, Units.val_mk0, div_eq_mul_inv]
  exact mul_comm _ _

end DedekindZetaZeroFree.SheetRescaling

end
