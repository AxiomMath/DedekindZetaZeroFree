module

public import DedekindZetaZeroFree.Adeles.Characters.ComplexTraceCharacter

@[expose] public section

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency true
namespace DedekindZetaZeroFree.KPActualReflectionData.StandardLocalSource
open NumberField KPReferenceChange.StandardComplexImage
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxActualImage
open KPInterface.ResidueConstruction.Raw
variable {F : Type} [Field F] [NumberField F]
variable (A : SArithmeticData F) (w : InfinitePlace F)

def complexRootAction : Representation ℂ (Multiplicative (KPHilbert.Completion F (Sum.inl w)))
    (Theta frequency) :=
  (KPReferenceChange.StandardCover.complexRho A w).comp
    (actualLocalRoot F A.zeta12 A.primitive_zeta12 (Sum.inl w)).toMonoidHom

def complexRawPsi : ContinuousAddChar (KPHilbert.Completion F (Sum.inl w)) :=
  actualLocalPsi F (PrincipalOfKP.standardCharacter F) (Sum.inl w)

theorem complexRawPsi_trace (x : KPHilbert.Completion F (Sum.inl w)) :
    (complexRawPsi w).toAddChar x = (archTraceCharacter w x : ℂ) := complexLocalPsi_trace w x

theorem complexRootAction_apply (x : KPHilbert.Completion F (Sum.inl w)) (h : Theta frequency) :
    complexRootAction A w (Multiplicative.ofAdd x) h =
      imageAction frequency (Matrix.ProjGenLinGroup.mk (upperUnipotent (coordinate A w x))) h := by
  change action A w (KPPGLLocalCover.N F A.zeta12 A.primitive_zeta12 (Sum.inl w) x) h = _
  rw [KPPGLLocalCover.N, ← standard_upper, action_splitMatrix]

theorem complex_whittakerLine : KPReflectionSpec.LocalWhittakerLine (V := Theta frequency)
    (complexRootAction A w) (complexRawPsi w).toAddChar.toMonoidHom := by
  have he : localWhittakerSpace _ (Theta frequency) (complexRootAction A w)
      (complexRawPsi w).toAddChar.toMonoidHom =
      KPCplxWhittakerUnique.whittakerSpace frequency (character (frequency : ℂ)) := by
    ext ell
    change (∀ t : Multiplicative (KPHilbert.Completion F (Sum.inl w)), ∀ h : Theta frequency,
      ell (complexRootAction A w t h) = (complexRawPsi w).toAddChar t.toAdd * ell h) ↔
      (∀ t : ℂ, ∀ h : Theta frequency,
        ell (imageAction frequency (Matrix.ProjGenLinGroup.mk (upperUnipotent t)) h) =
          (character (frequency : ℂ) t : ℂ) * ell h)
    constructor
    · intro hell t h
      have hx := hell (Multiplicative.ofAdd ((coordinate A w).symm t)) h
      change ell (complexRootAction A w (Multiplicative.ofAdd ((coordinate A w).symm t)) h) =
        (complexRawPsi w).toAddChar ((coordinate A w).symm t) * ell h at hx
      rw [complexRootAction_apply, complexRawPsi_trace, trace_character] at hx
      rw [(coordinate A w).apply_symm_apply t] at hx
      exact hx
    · intro hell t h
      change ell (complexRootAction A w (Multiplicative.ofAdd t.toAdd) h) =
        (complexRawPsi w).toAddChar t.toAdd * ell h
      rw [complexRootAction_apply, complexRawPsi_trace, trace_character]
      exact hell (coordinate A w t.toAdd) h
  unfold KPReflectionSpec.LocalWhittakerLine
  rw [he]
  apply (KPCplxWhittakerUnique.whittaker_dimension_one frequency (character (frequency : ℂ)) _ _).2
  · exact Circle.exp.continuous.comp (Complex.continuous_re.comp (continuous_const.mul continuous_id))
  · intro hone
    obtain ⟨x, hx⟩ := actualLocalPsi_nontrivial F (PrincipalOfKP.standardCharacter F)
      (PrincipalOfKP.standardCharacter_nontrivial F) (Sum.inl w)
    apply hx
    change (complexRawPsi w).toAddChar x = 1
    rw [complexRawPsi_trace, trace_character]
    exact congrArg (fun c : AddChar ℂ Circle => (c (coordinate A w x) : ℂ)) hone

end DedekindZetaZeroFree.KPActualReflectionData.StandardLocalSource

end
