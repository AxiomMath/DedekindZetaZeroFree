module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RightWordOperators
public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.TensorFiniteRecovery

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.RootDerivatives
open MomentSources NumberField
open _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.FlatFiniteSum renaming smooth_add → smooth_add
open _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.FlatFiniteSum renaming smooth_smul → smooth_smul
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.RawFiniteCompact renaming smooth_translate → smooth_translate
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
local notation "ρ" => KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12
local notation "W" => KPContActualSphericalRightFieldIdentification.actualRightWord F R.A.zeta12 R.A.primitive_zeta12
local notation "FinG" => KPGlobalTorusFunctionData.finitePart F R.A.zeta12 R.A.primitive_zeta12

private theorem actualRightWord_eq_adelic
    (w : List (Fin (KPContActualSphericalRightFieldIdentification.groupDimension F)))
    (f : Functions R) : W w f =
      AdelicRightLieWords.actualRightWord F R.A.zeta12 R.A.primitive_zeta12 w f := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    simp only [KPContActualSphericalRightFieldIdentification.actualRightWord, AdelicRightLieWords.actualRightWord]
    rw [ih]
    rfl

def wordRecovery {Q : AdmissibleFlatSources R} (T : Realization R Q) :
    Submodule ℂ (Functions R) where
  carrier := {f | KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 f ∧
    ∀ w a, ρ a (W w f) ∈ hcHeckeSpan T}
  zero_mem' := by
    have hz := ((FiniteWhittakerProjectors.FlatFiniteSum.zero F R.A.zeta12 R.A.primitive_zeta12 ⊥).property.1 0).1
    refine ⟨hz, ?_⟩
    intro w a
    have hw : W w (0 : Functions R) = 0 := by
      simpa using SharedSource.actualRightWord_smul (F := F) (ζ := R.A.zeta12)
        (hζ := R.A.primitive_zeta12) (0 : ℂ) (0 : Functions R) hz w
    rw [hw, map_zero]
    exact Submodule.zero_mem _
  add_mem' := by
    intro f g hf hg
    refine ⟨smooth_add F R.A.zeta12 R.A.primitive_zeta12 f g hf.1 hg.1, ?_⟩
    intro w a
    rw [SharedSource.actualRightWord_add f g hf.1 hg.1 w, map_add]
    exact Submodule.add_mem _ (hf.2 w a) (hg.2 w a)
  smul_mem' := by
    intro c f hf
    refine ⟨smooth_smul F R.A.zeta12 R.A.primitive_zeta12 c f hf.1, ?_⟩
    intro w a
    rw [SharedSource.actualRightWord_smul c f hf.1 w, map_smul]
    exact Submodule.smul_mem _ c (hf.2 w a)

theorem theta_mem_wordRecovery {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (v : R.A.UnitQuotient) : T.theta v ∈ wordRecovery R T := by
  refine ⟨(T.automorphic v).1, ?_⟩
  intro w a
  exact Submodule.subset_span ⟨v,a,w,by rw [actualRightWord_eq_adelic R]⟩

theorem actualWord_append
    (u w : List (Fin (KPContActualSphericalRightFieldIdentification.groupDimension F)))
    (f : Functions R) : W (u ++ w) f = W u (W w f) := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    simp only [List.cons_append, KPContActualSphericalRightFieldIdentification.actualRightWord, ih]

theorem wordRecovery_word {Q : AdmissibleFlatSources R} (T : Realization R Q)
    {f : Functions R} (hf : f ∈ wordRecovery R T)
    (w : List (Fin (KPContActualSphericalRightFieldIdentification.groupDimension F))) :
    W w f ∈ wordRecovery R T := by
  refine ⟨SharedSource.actualRightWord_smooth f hf.1 w, ?_⟩
  intro u a
  rw [← actualWord_append]
  exact hf.2 (u ++ w) a

theorem wordRecovery_finite {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (a : FinG) {f : Functions R} (hf : f ∈ wordRecovery R T) :
    ρ a.val f ∈ wordRecovery R T := by
  refine ⟨smooth_translate F R.A.zeta12 R.A.primitive_zeta12 a f hf.1, ?_⟩
  intro w b
  have hcomm : W w (ρ a.val f) = ρ a.val (W w f) := by
    simpa only [actualRightWord_eq_adelic R] using
      (_root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.actualWord_finite_translate R w a f)
  rw [hcomm, ← Module.End.mul_apply, ← map_mul]
  exact hf.2 w (b * a.val)

theorem hcHeckeSpan_le_of_word_recovery {Q Q' : AdmissibleFlatSources R}
    (T : Realization R Q) (T' : Realization R Q')
    (h : ∀ v, T.theta v ∈ wordRecovery R T') : hcHeckeSpan T ≤ hcHeckeSpan T' := by
  apply Submodule.span_le.mpr
  rintro f ⟨v,a,w,rfl⟩
  change ρ a (AdelicRightLieWords.actualRightWord F R.A.zeta12 R.A.primitive_zeta12
    w (T.theta v)) ∈ hcHeckeSpan T'
  rw [← actualRightWord_eq_adelic R]
  exact (h v).2 w a
end DedekindZetaZeroFree.RootDerivatives

end
