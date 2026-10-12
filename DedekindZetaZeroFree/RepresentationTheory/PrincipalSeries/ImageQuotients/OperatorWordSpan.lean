module

public import DedekindZetaZeroFree.Eisenstein.Residues.ScalarSections.MixedOperatorWords
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.HarishChandra.TensorImageWords

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open NumberField KPGlobalTorusFiniteStages HCGeneration TensorActionSource MomentSources
open KPContActualSphericalRightFieldIdentification
open _root_.DedekindZetaZeroFree.FourierContinuation.HCGeneration renaming map_tensorSlot → map_tensorSlot
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
variable (H : ∀ q, LocalImageData R q)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6400000

def imageData (q : KPFinitePlace F) : LocalImageData R q where
  inducing := { C.canonical q with polarization := C.polarization q }
  haar := (H q).haar
  haar_add := (H q).haar_add
  haar_integer := (H q).haar_integer

def localImageQuotient (v : KPHilbert.Place F) :
    Plus R.A P C v →ₗ[ℂ] actualLocal R (imageData R P C H) v := by
  cases v with
  | inl w => exact KPLiteralTensor.harmonicQuotient
  | inr q => exact (KPRankOneShellRepair.actualCanonicalForwardMap F R.A.zeta12
      R.A.primitive_zeta12 q (imageData R P C H q).inducing
      (imageData R P C H q).inducing.polarization
      (imageData R P C H q).haar (imageData R P C H q).haar_integer).toLinearMap.rangeRestrict

theorem localImageQuotient_surjective (v : KPHilbert.Place F) :
    Function.Surjective (localImageQuotient R P C H v) := by
  cases v with
  | inl w => exact KPLiteralTensor.harmonicQuotient_surjective
  | inr q =>
    rintro ⟨f, x, rfl⟩
    exact ⟨x, rfl⟩

def stageImageQuotient (s : RestrictedTensorSimple.Level (bad R.A P C)) :
    RestrictedTensorSimple.Stage (Plus R.A P C) s.val →ₗ[ℂ]
    RestrictedTensorSimple.Stage (actualLocal R (imageData R P C H)) s.val :=
  PiTensorProduct.map (fun j => localImageQuotient R P C H j.val)

def stageImageGenerator (s : RestrictedTensorSimple.Level (bad R.A P C)) :
    StageGenerator R P C s →
    Module.End ℂ (RestrictedTensorSimple.Stage (actualLocal R (imageData R P C H)) s.val)
  | .compact w k => tensorSlot (V := fun j : s.val => actualLocal R (imageData R P C H) j.val) ⟨Sum.inl w,
      s.property (by simp [bad, KPGlobalResidualConstruction.ScalarAbsorption.fullBad])⟩
      (localOperation R (imageData R P C H) (Sum.inl w) [.inl k])
  | .lie i => tensorSlot (V := fun j : s.val => actualLocal R (imageData R P C H) j.val) ⟨Sum.inl (actualLieIndexEquiv (F := F) i).1,
      s.property (by simp [bad, KPGlobalResidualConstruction.ScalarAbsorption.fullBad])⟩
      (localOperation R (imageData R P C H) (Sum.inl (actualLieIndexEquiv (F := F) i).1)
        [.inr (actualLieIndexEquiv (F := F) i).2])
  | .finite q hq a => tensorSlot (V := fun j : s.val => actualLocal R (imageData R P C H) j.val) ⟨Sum.inr q, hq⟩
      (localOperation R (imageData R P C H) (Sum.inr q)
        (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a))

theorem stageImageQuotient_generator
    (s : RestrictedTensorSimple.Level (bad R.A P C)) (b : StageGenerator R P C s)
    (x : RestrictedTensorSimple.Stage (Plus R.A P C) s.val) :
    stageImageQuotient R P C H s (stageGenerator R P C s b x) =
    stageImageGenerator R P C H s b (stageImageQuotient R P C H s x) := by
  cases b with
  | compact w k =>
    let hw : Sum.inl w ∈ s.val := s.property (by simp [bad,
      KPGlobalResidualConstruction.ScalarAbsorption.fullBad])
    exact congrArg (fun L => L x) (map_tensorSlot
      (fun j : s.val => localImageQuotient R P C H j.val) ⟨Sum.inl w, hw⟩
      (harmonicSourceAction k)
      (localOperation R (imageData R P C H) (Sum.inl w) [.inl k])
      (fun f => harmonicPlusGenerator_intertwines (.inl k) f))
  | lie i =>
    exact congrArg (fun L => L x) (map_tensorSlot
      (fun j : s.val => localImageQuotient R P C H j.val)
      ⟨Sum.inl (actualLieIndexEquiv (F := F) i).1, _⟩ _ _
      (harmonicPlusDerivative_intertwines (actualLieIndexEquiv (F := F) i).2))
  | finite q hq a =>
    apply congrArg (fun L => L x) (map_tensorSlot
      (fun j : s.val => localImageQuotient R P C H j.val) ⟨Sum.inr q, hq⟩ _ _ ?_)
    intro f
    apply Subtype.ext
    exact KPRankOneShellRepair.actualCanonicalForwardLinear_intertwines F R.A.zeta12
      R.A.primitive_zeta12 q (imageData R P C H q).inducing
      (imageData R P C H q).inducing.polarization
      (imageData R P C H q).haar (imageData R P C H q).haar_integer _ f

def stageImageWord (s : RestrictedTensorSimple.Level (bad R.A P C)) :
    List (StageGenerator R P C s) →
    Module.End ℂ (RestrictedTensorSimple.Stage (actualLocal R (imageData R P C H)) s.val)
  | [] => LinearMap.id
  | b :: w => (stageImageGenerator R P C H s b).comp (stageImageWord s w)

def stageComplexIndex (s : RestrictedTensorSimple.Level (bad R.A P C))
    (w : InfinitePlace F) : ComplexGenerator → StageGenerator R P C s
  | .inl k => .compact w k
  | .inr b => .lie ((actualLieIndexEquiv (F := F)).symm (w, b))

theorem stageComplexIndex_word
    (s : RestrictedTensorSimple.Level (bad R.A P C))
    (w : InfinitePlace F) (hw : Sum.inl w ∈ s.val) (a : List ComplexGenerator) :
    stageImageWord R P C H s (a.map (stageComplexIndex R P C s w)) =
    tensorSlot (V := fun j : s.val => actualLocal R (imageData R P C H) j.val)
      ⟨Sum.inl w, hw⟩ (localOperation R (imageData R P C H) (Sum.inl w) a) := by
  induction a with
  | nil => exact (tensorSlot_id (V := fun j : s.val => actualLocal R (imageData R P C H) j.val) _).symm
  | cons b a ih =>
    have hb : stageImageGenerator R P C H s (stageComplexIndex R P C s w b) =
        tensorSlot (V := fun j : s.val => actualLocal R (imageData R P C H) j.val)
          ⟨Sum.inl w, hw⟩ (localOperation R (imageData R P C H) (Sum.inl w) [b]) := by
      cases b with
      | inl k => rfl
      | inr b =>
        let slot (wb : InfinitePlace F × Fin 6) :
            Module.End ℂ (RestrictedTensorSimple.Stage (actualLocal R (imageData R P C H)) s.val) :=
          tensorSlot (V := fun j : s.val => actualLocal R (imageData R P C H) j.val)
            ⟨Sum.inl wb.1, s.property (by simp [bad,
              KPGlobalResidualConstruction.ScalarAbsorption.fullBad])⟩
            (localOperation R (imageData R P C H) (Sum.inl wb.1) [.inr wb.2])
        change slot (actualLieIndexEquiv (F := F) ((actualLieIndexEquiv (F := F)).symm (w, b))) = slot (w, b)
        exact congrArg slot ((actualLieIndexEquiv (F := F)).apply_symm_apply (w, b))
    change (stageImageGenerator R P C H s (stageComplexIndex R P C s w b)).comp
      (stageImageWord R P C H s (a.map (stageComplexIndex R P C s w))) = _
    rw [hb, ih, ← tensorSlot_comp]
    rfl

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
