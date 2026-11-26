module

public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.Construction
public import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Tensor
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GeneralTowerNaturality

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Conjugation of finite-place Artin homomorphisms

This module identifies localized completions associated with conjugate extensions and proves conjugation invariance of the resulting finite-place Artin map.
-/

open scoped Classical IsMulCommutative NNReal NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The algebraic localizations belonging to conjugate extensions of a
finite place are identified by the induced equivalence of completions. -/
noncomputable def finitePlaceConjugateLocalizedCompletionAlgEquiv
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (g : L ≃ₐ[K] L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let wc := absoluteValueExtensionConjugate vK w g
    let Ew := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    let Ewc := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wc
    letI : Algebra vK.Completion Ew :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    letI : Algebra vK.Completion Ewc :=
      finitePlaceLocalArtinLocalizedAlgebra v wc
    Ewc ≃ₐ[vK.Completion] Ew := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let wc := absoluteValueExtensionConjugate vK w g
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  letI hwK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  letI : SMul K w.1.Completion := hwK.toSMul
  letI : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  letI hwcK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) wc.1
  letI : SMul K wc.1.Completion := hwcK.toSMul
  letI : Algebra vK.Completion wc.1.Completion :=
    AbsoluteValue.completionAlgebra vK wc.1 wc.2
  let Ew := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  let Ewc := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wc
  let eCompletion : wc.1.Completion ≃ₐ[vK.Completion]
      w.1.Completion :=
    { LocalClassFieldTheory.conjugateExtensionCompletionRingEquiv
        vK w g with
      commutes' :=
        LocalClassFieldTheory.conjugateExtensionCompletionRingEquiv_algebraMap
          vK w g }
  let e : Ewc ≃ₐ[vK.Completion] Ew :=
    (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
        vK hvK wc).trans
      (eCompletion.trans
        (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
          vK hvK w).symm)
  exact e

omit [IsAbelianGalois K L] in
/-- The conjugate-localization equivalence carries the canonical
embedding of `L` to the conjugate of that embedding. -/
theorem finitePlaceConjugateLocalizedCompletionAlgEquiv_toAlgebraicLocalization
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (g : L ≃ₐ[K] L) (x : L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let wc := absoluteValueExtensionConjugate vK w g
    let Ew := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    let Ewc := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wc
    letI : Algebra vK.Completion Ew :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    letI : Algebra vK.Completion Ewc :=
      finitePlaceLocalArtinLocalizedAlgebra v wc
    finitePlaceConjugateLocalizedCompletionAlgEquiv
        (K := K) (L := L) v w g
        (AbsoluteValue.toAlgebraicLocalization
          vK wc.1 wc.2 x) =
      AbsoluteValue.toAlgebraicLocalization
        vK w.1 w.2 (g x) := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let wc := absoluteValueExtensionConjugate vK w g
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let hwK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hwK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let hwcK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) wc.1
  let : SMul K wc.1.Completion := hwcK.toSMul
  let : Algebra vK.Completion wc.1.Completion :=
    AbsoluteValue.completionAlgebra vK wc.1 wc.2
  apply
    (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
      vK hvK w).injective
  change
    LocalClassFieldTheory.conjugateExtensionCompletionRingEquiv
        vK w g
        (AbsoluteValue.toCompletion wc.1 x) =
      AbsoluteValue.toCompletion w.1 (g x)
  exact
    LocalClassFieldTheory.conjugateExtensionCompletionRingEquiv_toCompletion
      vK w g x

omit [IsAbelianGalois K L] in
/-- The inverse conjugate-localization equivalence carries the
canonical embedding back along the inverse global automorphism. -/
theorem
    finitePlaceConjugateLocalizedCompletionAlgEquiv_symm_toAlgebraicLocalization
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (g : L ≃ₐ[K] L) (x : L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let wc := absoluteValueExtensionConjugate vK w g
    let Ew := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    let Ewc := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wc
    letI : Algebra vK.Completion Ew :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    letI : Algebra vK.Completion Ewc :=
      finitePlaceLocalArtinLocalizedAlgebra v wc
    (finitePlaceConjugateLocalizedCompletionAlgEquiv
        (K := K) (L := L) v w g).symm
        (AbsoluteValue.toAlgebraicLocalization
          vK w.1 w.2 x) =
      AbsoluteValue.toAlgebraicLocalization
        vK wc.1 wc.2 (g.symm x) := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let wc := absoluteValueExtensionConjugate vK w g
  let hwK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hwK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let hwcK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) wc.1
  let : SMul K wc.1.Completion := hwcK.toSMul
  let : Algebra vK.Completion wc.1.Completion :=
    AbsoluteValue.completionAlgebra vK wc.1 wc.2
  let e :=
    finitePlaceConjugateLocalizedCompletionAlgEquiv
      (K := K) (L := L) v w g
  apply e.injective
  rw [e.apply_symm_apply,
    finitePlaceConjugateLocalizedCompletionAlgEquiv_toAlgebraicLocalization,
    g.apply_symm_apply]

/-- The canonical embedding of `L` intertwines a decomposition-group element
with the local automorphism it corresponds to. -/
private theorem finitePlaceDecompositionEquiv_symm_toAlgebraicLocalization
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (tau :
      letI : Algebra (NumberField.HeightOneSpectrum.adicAbv K v).Completion
          (AlgebraicNumberTheory.Valuations.LocalizedCompletion
            (NumberField.HeightOneSpectrum.adicAbv K v) w) :=
        finitePlaceLocalArtinLocalizedAlgebra v w
      AlgebraicNumberTheory.Valuations.LocalizedCompletion
          (NumberField.HeightOneSpectrum.adicAbv K v) w ≃ₐ[
        (NumberField.HeightOneSpectrum.adicAbv K v).Completion]
        AlgebraicNumberTheory.Valuations.LocalizedCompletion
          (NumberField.HeightOneSpectrum.adicAbv K v) w)
    (y : L) :
    letI : Algebra (NumberField.HeightOneSpectrum.adicAbv K v).Completion
        (AlgebraicNumberTheory.Valuations.LocalizedCompletion
          (NumberField.HeightOneSpectrum.adicAbv K v) w) :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    AbsoluteValue.toAlgebraicLocalization
        (NumberField.HeightOneSpectrum.adicAbv K v) w.1 w.2
        ((((decompositionGroupEquivAlgebraicLocalizationAut
            (NumberField.HeightOneSpectrum.adicAbv K v)
            (RayClass.adicAbv_isNontrivial v) w :
              absoluteValueDecompositionGroup K w.1 ≃*
                (AlgebraicNumberTheory.Valuations.LocalizedCompletion
                    (NumberField.HeightOneSpectrum.adicAbv K v) w ≃ₐ[
                  (NumberField.HeightOneSpectrum.adicAbv K v).Completion]
                  AlgebraicNumberTheory.Valuations.LocalizedCompletion
                    (NumberField.HeightOneSpectrum.adicAbv K v) w)).symm tau :
            absoluteValueDecompositionGroup K w.1) : L ≃ₐ[K] L) y) =
      tau (AbsoluteValue.toAlgebraicLocalization
        (NumberField.HeightOneSpectrum.adicAbv K v) w.1 w.2 y) := by
  rw [← localizationRamificationGroups_decompositionGroupEquiv_toLocalization]
  exact DFunLike.congr_fun (MulEquiv.apply_symm_apply _ tau) _

/-- A global automorphism acting on the conjugate localization through `tauC`
acts on the original localization through the transported automorphism. -/
private theorem finitePlaceConjugate_toAlgebraicLocalization_of_action
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (g σ : L ≃ₐ[K] L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let wc := absoluteValueExtensionConjugate vK w g
    let Ew := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    let Ewc := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wc
    letI : Algebra vK.Completion Ew :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    letI : Algebra vK.Completion Ewc :=
      finitePlaceLocalArtinLocalizedAlgebra v wc
    ∀ (tauC : Ewc ≃ₐ[vK.Completion] Ewc),
      (∀ y : L, AbsoluteValue.toAlgebraicLocalization vK wc.1 wc.2 (σ y) =
        tauC (AbsoluteValue.toAlgebraicLocalization vK wc.1 wc.2 y)) →
      ∀ z : L, AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 (σ z) =
        AlgEquiv.autCongr
          (finitePlaceConjugateLocalizedCompletionAlgEquiv (K := K) (L := L) v w g)
          tauC (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 z) := by
  intro vK wc Ew Ewc
  letI : Algebra vK.Completion Ew := finitePlaceLocalArtinLocalizedAlgebra v w
  letI : Algebra vK.Completion Ewc := finitePlaceLocalArtinLocalizedAlgebra v wc
  intro tauC hσ z
  have hg := (inferInstance : IsMulCommutative (L ≃ₐ[K] L)).is_comm.comm g σ
  have hcomm : g (σ (g.symm z)) = σ z :=
    calc
      g (σ (g.symm z)) = (g * σ) (g.symm z) := rfl
      _ = (σ * g) (g.symm z) := DFunLike.congr_fun hg (g.symm z)
      _ = σ (g (g.symm z)) := rfl
      _ = σ z := by rw [g.apply_symm_apply]
  rw [← hcomm,
    ← finitePlaceConjugateLocalizedCompletionAlgEquiv_toAlgebraicLocalization,
    hσ, ← finitePlaceConjugateLocalizedCompletionAlgEquiv_symm_toAlgebraicLocalization]
  rfl

/-- Conjugation of a place intertwines the two localization
decomposition-group identifications on each local automorphism. -/
theorem finitePlaceDecompositionTransport_conjugate_apply
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (g : L ≃ₐ[K] L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let wc := absoluteValueExtensionConjugate vK w g
    let hvK : vK.IsNontrivial :=
      RayClass.adicAbv_isNontrivial v
    let Ew := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    let Ewc := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wc
    letI : Algebra vK.Completion Ew :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    letI : Algebra vK.Completion Ewc :=
      finitePlaceLocalArtinLocalizedAlgebra v wc
    let e :=
      finitePlaceConjugateLocalizedCompletionAlgEquiv
        (K := K) (L := L) v w g
    let eDw :
        absoluteValueDecompositionGroup K w.1 ≃*
          (Ew ≃ₐ[vK.Completion] Ew) :=
      decompositionGroupEquivAlgebraicLocalizationAut
        vK hvK w
    let eDwc :
        absoluteValueDecompositionGroup K wc.1 ≃*
          (Ewc ≃ₐ[vK.Completion] Ewc) :=
      decompositionGroupEquivAlgebraicLocalizationAut
        vK hvK wc
    ∀ tauC : Ewc ≃ₐ[vK.Completion] Ewc,
      (absoluteValueDecompositionGroup K wc.1).subtype
          (eDwc.symm tauC) =
        (absoluteValueDecompositionGroup K w.1).subtype
          (eDw.symm (AlgEquiv.autCongr e tauC)) := by
  intro vK wc hvK Ew Ewc e eDw eDwc tauC
  letI : Algebra vK.Completion Ew := finitePlaceLocalArtinLocalizedAlgebra v w
  letI : Algebra vK.Completion Ewc := finitePlaceLocalArtinLocalizedAlgebra v wc
  have hC (y : L) :
      AbsoluteValue.toAlgebraicLocalization vK wc.1 wc.2
          (((eDwc.symm tauC : absoluteValueDecompositionGroup K wc.1) :
            L ≃ₐ[K] L) y) =
        tauC (AbsoluteValue.toAlgebraicLocalization vK wc.1 wc.2 y) :=
    finitePlaceDecompositionEquiv_symm_toAlgebraicLocalization v wc tauC y
  have hW (tau : Ew ≃ₐ[vK.Completion] Ew) (y : L) :
      AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
          (((eDw.symm tau : absoluteValueDecompositionGroup K w.1) :
            L ≃ₐ[K] L) y) =
        tau (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 y) :=
    finitePlaceDecompositionEquiv_symm_toAlgebraicLocalization v w tau y
  apply AlgEquiv.ext
  intro z
  apply (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2).injective
  rw [Subgroup.coe_subtype, Subgroup.coe_subtype, hW]
  exact finitePlaceConjugate_toAlgebraicLocalization_of_action v w g
    ((eDwc.symm tauC : absoluteValueDecompositionGroup K wc.1) : L ≃ₐ[K] L)
    tauC hC z

/-- Conjugation of a place intertwines the two localization
decomposition-group identifications after inclusion in the global
Galois group. -/
theorem finitePlaceDecompositionTransport_conjugate
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (g : L ≃ₐ[K] L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let wc := absoluteValueExtensionConjugate vK w g
    let hvK : vK.IsNontrivial :=
      RayClass.adicAbv_isNontrivial v
    let Ew := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    let Ewc := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wc
    letI : Algebra vK.Completion Ew :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    letI : Algebra vK.Completion Ewc :=
      finitePlaceLocalArtinLocalizedAlgebra v wc
    let e :=
      finitePlaceConjugateLocalizedCompletionAlgEquiv
        (K := K) (L := L) v w g
    let eDw :
        absoluteValueDecompositionGroup K w.1 ≃*
          (Ew ≃ₐ[vK.Completion] Ew) :=
      decompositionGroupEquivAlgebraicLocalizationAut
        vK hvK w
    let eDwc :
        absoluteValueDecompositionGroup K wc.1 ≃*
          (Ewc ≃ₐ[vK.Completion] Ewc) :=
      decompositionGroupEquivAlgebraicLocalizationAut
        vK hvK wc
    (absoluteValueDecompositionGroup K wc.1).subtype.comp
        eDwc.symm.toMonoidHom =
      ((absoluteValueDecompositionGroup K w.1).subtype.comp
          eDw.symm.toMonoidHom).comp
        (AlgEquiv.autCongr e).toMonoidHom := by
  apply MonoidHom.ext
  intro tauC
  exact
    finitePlaceDecompositionTransport_conjugate_apply
      (K := K) (L := L) v w g tauC

/-- The localized local Artin map is the abelian local Artin map of the
localized completion, precomposed with the canonical completion input. -/
private theorem finitePlaceLocalArtinMonoidHom_eq_comp
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    letI : Algebra vK.Completion E :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    letI : FiniteDimensional vK.Completion E :=
      finitePlaceLocalArtinFiniteDimensional v w
    letI : IsAbelianGalois vK.Completion E :=
      finitePlaceLocalArtinIsAbelianGalois v w
        (inferInstance : FiniteDimensional K L)
    letI : ValuativeRel vK.Completion :=
      finitePlaceLocalArtinCompletionValuativeRel v
    letI : IsNonarchimedeanLocalField vK.Completion :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    finitePlaceLocalArtinMonoidHom (K := K) (L := L) v w =
      (LocalClassFieldTheory.abelianLocalArtinMonoidHom
        vK.Completion E).comp
          (finitePlaceLocalArtinInputMonoidHom v) := by
  intro vK E
  rfl

/-- Naturality of the abelian local Artin map under the conjugate
localization equivalence, in the instance form used by
`finitePlaceLocalArtinMonoidHom`. -/
private theorem finitePlaceConjugate_abelianLocalArtinMonoidHom_autCongr
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (g : L ≃ₐ[K] L) :
    letI : Algebra (NumberField.HeightOneSpectrum.adicAbv K v).Completion
        (AlgebraicNumberTheory.Valuations.LocalizedCompletion (NumberField.HeightOneSpectrum.adicAbv K v) w) :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    letI : Algebra (NumberField.HeightOneSpectrum.adicAbv K v).Completion
        (AlgebraicNumberTheory.Valuations.LocalizedCompletion (NumberField.HeightOneSpectrum.adicAbv K v)
          (absoluteValueExtensionConjugate (NumberField.HeightOneSpectrum.adicAbv K v) w g)) :=
      finitePlaceLocalArtinLocalizedAlgebra v
        (absoluteValueExtensionConjugate (NumberField.HeightOneSpectrum.adicAbv K v) w g)
    letI : FiniteDimensional (NumberField.HeightOneSpectrum.adicAbv K v).Completion
        (AlgebraicNumberTheory.Valuations.LocalizedCompletion (NumberField.HeightOneSpectrum.adicAbv K v) w) :=
      finitePlaceLocalArtinFiniteDimensional v w
    letI : FiniteDimensional (NumberField.HeightOneSpectrum.adicAbv K v).Completion
        (AlgebraicNumberTheory.Valuations.LocalizedCompletion (NumberField.HeightOneSpectrum.adicAbv K v)
          (absoluteValueExtensionConjugate (NumberField.HeightOneSpectrum.adicAbv K v) w g)) :=
      finitePlaceLocalArtinFiniteDimensional v
        (absoluteValueExtensionConjugate (NumberField.HeightOneSpectrum.adicAbv K v) w g)
    letI : IsAbelianGalois (NumberField.HeightOneSpectrum.adicAbv K v).Completion
        (AlgebraicNumberTheory.Valuations.LocalizedCompletion (NumberField.HeightOneSpectrum.adicAbv K v) w) :=
      finitePlaceLocalArtinIsAbelianGalois v w
        (inferInstance : FiniteDimensional K L)
    letI : IsAbelianGalois (NumberField.HeightOneSpectrum.adicAbv K v).Completion
        (AlgebraicNumberTheory.Valuations.LocalizedCompletion (NumberField.HeightOneSpectrum.adicAbv K v)
          (absoluteValueExtensionConjugate (NumberField.HeightOneSpectrum.adicAbv K v) w g)) :=
      finitePlaceLocalArtinIsAbelianGalois v
        (absoluteValueExtensionConjugate (NumberField.HeightOneSpectrum.adicAbv K v) w g)
        (inferInstance : FiniteDimensional K L)
    letI : ValuativeRel (NumberField.HeightOneSpectrum.adicAbv K v).Completion :=
      finitePlaceLocalArtinCompletionValuativeRel v
    letI : IsNonarchimedeanLocalField (NumberField.HeightOneSpectrum.adicAbv K v).Completion :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    (AlgEquiv.autCongr
        (finitePlaceConjugateLocalizedCompletionAlgEquiv
          (K := K) (L := L) v w g)).toMonoidHom.comp
        (LocalClassFieldTheory.abelianLocalArtinMonoidHom (NumberField.HeightOneSpectrum.adicAbv K v).Completion
          (AlgebraicNumberTheory.Valuations.LocalizedCompletion (NumberField.HeightOneSpectrum.adicAbv K v)
            (absoluteValueExtensionConjugate (NumberField.HeightOneSpectrum.adicAbv K v) w g))) =
      LocalClassFieldTheory.abelianLocalArtinMonoidHom (NumberField.HeightOneSpectrum.adicAbv K v).Completion
        (AlgebraicNumberTheory.Valuations.LocalizedCompletion (NumberField.HeightOneSpectrum.adicAbv K v) w) := by
  exact
    @LocalClassFieldTheory.abelianLocalArtinMonoidHom_autCongr
      (NumberField.HeightOneSpectrum.adicAbv K v).Completion
      (AlgebraicNumberTheory.Valuations.LocalizedCompletion (NumberField.HeightOneSpectrum.adicAbv K v)
        (absoluteValueExtensionConjugate (NumberField.HeightOneSpectrum.adicAbv K v) w g))
      (AlgebraicNumberTheory.Valuations.LocalizedCompletion (NumberField.HeightOneSpectrum.adicAbv K v) w) _ _ _
      (finitePlaceLocalArtinLocalizedAlgebra v
        (absoluteValueExtensionConjugate (NumberField.HeightOneSpectrum.adicAbv K v) w g))
      (finitePlaceLocalArtinLocalizedAlgebra v w)
      (finitePlaceLocalArtinCompletionValuativeRel v) _
      (finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v)
      (finitePlaceLocalArtinFiniteDimensional v
        (absoluteValueExtensionConjugate (NumberField.HeightOneSpectrum.adicAbv K v) w g))
      (finitePlaceLocalArtinFiniteDimensional v w)
      (finitePlaceLocalArtinIsAbelianGalois v
        (absoluteValueExtensionConjugate (NumberField.HeightOneSpectrum.adicAbv K v) w g)
        (inferInstance : FiniteDimensional K L))
      (finitePlaceLocalArtinIsAbelianGalois v w
        (inferInstance : FiniteDimensional K L))
      (finitePlaceConjugateLocalizedCompletionAlgEquiv
        (K := K) (L := L) v w g)

/-- Local Artin maps are natural under the localized-completion
equivalence induced by conjugating a finite-place extension. -/
theorem finitePlaceLocalArtinMonoidHom_conjugate
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (g : L ≃ₐ[K] L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let wc := absoluteValueExtensionConjugate vK w g
    let Ew := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    let Ewc := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wc
    letI : Algebra vK.Completion Ew :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    letI : Algebra vK.Completion Ewc :=
      finitePlaceLocalArtinLocalizedAlgebra v wc
    let e :=
      finitePlaceConjugateLocalizedCompletionAlgEquiv
        (K := K) (L := L) v w g
    (AlgEquiv.autCongr e).toMonoidHom.comp
        (finitePlaceLocalArtinMonoidHom
          (K := K) (L := L) v wc) =
      finitePlaceLocalArtinMonoidHom
        (K := K) (L := L) v w := by
  intro vK wc Ew Ewc e
  rw [finitePlaceLocalArtinMonoidHom_eq_comp v wc,
    finitePlaceLocalArtinMonoidHom_eq_comp v w, ← MonoidHom.comp_assoc]
  exact congrArg (fun f => f.comp (finitePlaceLocalArtinInputMonoidHom v))
    (finitePlaceConjugate_abelianLocalArtinMonoidHom_autCongr v w g)

/-- The decomposition-group inclusions at conjugate extensions differ by the
conjugate localization equivalence. -/
private theorem finitePlaceLocalToGlobalMonoidHom_conjugate
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (g : L ≃ₐ[K] L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let wc := absoluteValueExtensionConjugate vK w g
    let Ew := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    let Ewc := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wc
    letI : Algebra vK.Completion Ew :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    letI : Algebra vK.Completion Ewc :=
      finitePlaceLocalArtinLocalizedAlgebra v wc
    finitePlaceLocalToGlobalMonoidHom (K := K) (L := L) v wc =
      (finitePlaceLocalToGlobalMonoidHom (K := K) (L := L) v w).comp
        (AlgEquiv.autCongr
          (finitePlaceConjugateLocalizedCompletionAlgEquiv
            (K := K) (L := L) v w g)).toMonoidHom := by
  intro vK wc Ew Ewc
  apply MonoidHom.ext
  intro tauC
  exact
    finitePlaceDecompositionTransport_conjugate_apply
      (K := K) (L := L) v w g tauC

/-- Conjugating the chosen extension of a finite place does not change
its Artin homomorphism when the global extension is abelian. -/
theorem finitePlaceArtinMonoidHomOfExtension_conjugate
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (g : L ≃ₐ[K] L) :
    finitePlaceArtinMonoidHomOfExtension
        (K := K) (L := L) v
        (absoluteValueExtensionConjugate
          (NumberField.HeightOneSpectrum.adicAbv K v) w g) =
      finitePlaceArtinMonoidHomOfExtension
        (K := K) (L := L) v w := by
  rw [finitePlaceArtinMonoidHomOfExtension_factor,
    finitePlaceArtinMonoidHomOfExtension_factor,
    finitePlaceLocalToGlobalMonoidHom_conjugate v w g, MonoidHom.comp_assoc]
  exact congrArg (fun f => (finitePlaceLocalToGlobalMonoidHom
    (K := K) (L := L) v w).comp f)
    (finitePlaceLocalArtinMonoidHom_conjugate v w g)

/-- The finite-place Artin homomorphism is independent of the chosen
extension of the base place in an abelian extension. -/
theorem finitePlaceArtinMonoidHomOfExtension_eq
    (v : HeightOneSpectrum (𝓞 K))
    (w w' : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L) :
    finitePlaceArtinMonoidHomOfExtension
        (K := K) (L := L) v w =
      finitePlaceArtinMonoidHomOfExtension
        (K := K) (L := L) v w' := by
  let : NumberField L := NumberField.of_module_finite K L
  let W :=
    finitePlaceExtensionCentre
      (K := K) (L := L) v w
  let W' :=
    finitePlaceExtensionCentre
      (K := K) (L := L) v w'
  let : Finite (L ≃ₐ[K] L) :=
    IsGaloisGroup.finite (L ≃ₐ[K] L) K L
  let :
      IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing
      (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
  let : W.asIdeal.LiesOver v.asIdeal :=
    ⟨(finitePlaceExtensionCentreIdeal_under
      (K := K) (L := L) v w).symm⟩
  let : W'.asIdeal.LiesOver v.asIdeal :=
    ⟨(finitePlaceExtensionCentreIdeal_under
      (K := K) (L := L) v w').symm⟩
  obtain ⟨g, hg⟩ :=
    HilbertRamification.Dedekind.exists_smul_eq_of_isGaloisGroup
      v.asIdeal W.asIdeal W'.asIdeal (L ≃ₐ[K] L)
  have hplace :
      finitePlaceEquiv K L g W = W' := by
    apply HeightOneSpectrum.ext
    rw [finitePlaceEquiv_asIdeal]
    exact hg
  have hconjugate :
      absoluteValueExtensionConjugate
          (NumberField.HeightOneSpectrum.adicAbv K v)
          w g⁻¹ =
        w' := by
    apply
      finitePlaceExtensionCentre_injective
        (K := K) (L := L) v
    rw [finitePlaceExtensionCentre_conjugate]
    simpa only [inv_inv, W, W'] using hplace
  rw [← hconjugate]
  exact
    (finitePlaceArtinMonoidHomOfExtension_conjugate
      (K := K) (L := L) v w g⁻¹).symm

end Reciprocity
end GlobalClassFieldTheory

end
