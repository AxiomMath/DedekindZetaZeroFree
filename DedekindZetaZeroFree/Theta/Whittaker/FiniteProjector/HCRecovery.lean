module

public import DedekindZetaZeroFree.Theta.Periods.ResidualLieWordSpan
public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.FlatFiniteSum
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.ActualNativeWordIdentification
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.FiniteTranslationLieCommutation

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.FiniteWhittakerProjectors
open MomentSources NumberField
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeWordAction renaming actual_eq_word → actual_eq_word
open _root_.DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets renaming word_add → word_add
open _root_.DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets renaming word_smul → word_smul
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.RawFiniteCompact renaming smooth_translate → smooth_translate
open _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.FlatFiniteSum renaming smooth_add → smooth_add
open _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.FlatFiniteSum renaming smooth_smul → smooth_smul
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
local notation "ρ" => KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12
local notation "W" => AdelicRightLieWords.actualRightWord F R.A.zeta12 R.A.primitive_zeta12
local notation "FinG" => KPGlobalTorusFunctionData.finitePart F R.A.zeta12 R.A.primitive_zeta12

theorem actualWord_finite_translate (w : List (Fin (AdelicRightLieWords.groupDimension F)))
    (a : FinG) (f : Functions R) : W w (ρ a.val f) = ρ a.val (W w f) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    funext g
    simp only [AdelicRightLieWords.actualRightWord, ih]
    change deriv _ 0 = deriv _ 0
    congr 1
    funext t
    change W w f _ = W w f _
    rw [mul_assoc, (KPGlobalResidualConstruction.ActualScalarCasimirTransport.insertion_commutes_finitePart
      F R.A.zeta12 R.A.primitive_zeta12 _ a).eq, ← mul_assoc]

def finiteTranslateSpan {Q : AdmissibleFlatSources R} (T : Realization R Q) : Submodule ℂ (Functions R) :=
  Submodule.span ℂ {f | ∃ (v : R.A.UnitQuotient) (a : FinG), f = ρ a.val (T.theta v)}

theorem finiteTranslateSpan_words {Q : AdmissibleFlatSources R} (T : Realization R Q)
    {f : Functions R} (hf : f ∈ finiteTranslateSpan R T) :
    KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 f ∧
      ∀ (w : List (Fin (AdelicRightLieWords.groupDimension F)))
        (a : Group R), ρ a (W w f) ∈ hcHeckeSpan T := by
  have actual_eq_word (w : List (Fin (AdelicRightLieWords.groupDimension F)))
      (u : Functions R) :
      W w u = KPMsClearedTruncationL2.NativeStageJets.word F R.A.zeta12 R.A.primitive_zeta12
        (w.map (fun b =>
          KPSmoothAutomorphicEvaluation.AmbientApproximation.OrbitSmoothing.Reconstruction.LocalSobolev.Scalar.CoordinateSource.actualBasisReindex F
            (AdelicRightLieWords.lieEnumeration F b))) u := by
    have word_eq (w : List (Fin (AdelicRightLieWords.groupDimension F))) :
        W w u = KPContActualSphericalRightFieldIdentification.actualRightWord
          F R.A.zeta12 R.A.primitive_zeta12 w u := by
      induction w with
      | nil => rfl
      | cons b w ih =>
        simp only [AdelicRightLieWords.actualRightWord,
          KPContActualSphericalRightFieldIdentification.actualRightWord]
        rw [ih]
        rfl
    rw [word_eq]
    exact KPGlobalResidualConstruction.NativeWordAction.actual_eq_word
      F R.A.zeta12 R.A.primitive_zeta12 w u
  change f ∈ Submodule.span ℂ _ at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨v,a,rfl⟩ := hf
    refine ⟨smooth_translate F R.A.zeta12 R.A.primitive_zeta12 a _ (T.automorphic v).1, ?_⟩
    intro w b
    rw [actualWord_finite_translate, ← Module.End.mul_apply, ← map_mul]
    exact Submodule.subset_span ⟨v,b*a.val,w,rfl⟩
  | zero =>
    have hs := ((FlatFiniteSum.zero F R.A.zeta12 R.A.primitive_zeta12 ⊥).property.1 0).1
    refine ⟨hs, ?_⟩
    intro w a
    have hw : W w (0 : Functions R) = 0 := by
      rw [actual_eq_word]
      have hh := word_smul F R.A.zeta12 R.A.primitive_zeta12 (0 : ℂ) (0 : Functions R) hs.2.1
        (w.map (fun b => KPSmoothAutomorphicEvaluation.AmbientApproximation.OrbitSmoothing.Reconstruction.LocalSobolev.Scalar.CoordinateSource.actualBasisReindex F
          (AdelicRightLieWords.lieEnumeration F b)))
      simpa using hh
    rw [hw, map_zero]
    exact Submodule.zero_mem _
  | add f g hf hg ihf ihg =>
    refine ⟨smooth_add F R.A.zeta12 R.A.primitive_zeta12 f g ihf.1 ihg.1, ?_⟩
    intro w a
    have hw : W w (f+g) = W w f + W w g := by
      simp_rw [actual_eq_word]
      exact word_add F R.A.zeta12 R.A.primitive_zeta12 f g ihf.1.2.1 ihg.1.2.1 _
    rw [hw, map_add]
    exact Submodule.add_mem _ (ihf.2 w a) (ihg.2 w a)
  | smul c f hf ih =>
    refine ⟨smooth_smul F R.A.zeta12 R.A.primitive_zeta12 c f ih.1, ?_⟩
    intro w a
    have hw : W w (c • f) = c • W w f := by
      simp_rw [actual_eq_word]
      exact word_smul F R.A.zeta12 R.A.primitive_zeta12 c f ih.1.2.1 _
    rw [hw, map_smul]
    exact Submodule.smul_mem _ c (ih.2 w a)

theorem hcHeckeSpan_le_of_finite_recovery {Q Q' : AdmissibleFlatSources R}
    (T : Realization R Q) (T' : Realization R Q')
    (h : ∀ v, T.theta v ∈ finiteTranslateSpan R T') : hcHeckeSpan T ≤ hcHeckeSpan T' := by
  apply Submodule.span_le.mpr
  rintro f ⟨v,a,w,rfl⟩
  exact (finiteTranslateSpan_words R T' (h v)).2 w a

end DedekindZetaZeroFree.FiniteWhittakerProjectors

end
