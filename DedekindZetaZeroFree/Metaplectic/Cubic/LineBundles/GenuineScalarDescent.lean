module

public import DedekindZetaZeroFree.Metaplectic.Cubic.Quotients.HaarPushforwardsAndSupport

@[expose] public section

noncomputable section
open scoped Classical NumberField

namespace DedekindZetaZeroFree.KPContSectorScalarLineAlgebra

open KPContSectorCoveredQuotientVocabulary

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)

def GenuineCoveredScalars :
    Submodule ℂ (CoveredSpherical F ζ hζ U → ℂ) where
  carrier := {f | ∀ (ε : rootsOfUnity 3 F) (v : CoveredSpherical F ζ hζ U),
    f (z F ζ hζ U ε v) = (chi F ζ hζ ε : ℂ) * f v}
  zero_mem' := by intro ε v; simp
  add_mem' := by
    intro f g hf hg ε v
    simp only [Pi.add_apply, hf ε v, hg ε v]
    ring
  smul_mem' := by
    intro c f hf ε v
    simp only [Pi.smul_apply, smul_eq_mul, hf ε v]
    ring

def J : GenuineCoveredScalars F ζ hζ U ≃ₗ[ℂ]
    KPFiniteCuspAtlas.genuineScalars F ζ hζ U where
  toFun f := ⟨fun p => f.val (Quotient.mk (coveredRelation F ζ hζ U) p), by
    refine ⟨?_, ?_, ?_⟩
    · intro x c γ
      change f.val (Quotient.mk (coveredRelation F ζ hζ U)
          (γ • x, KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ * c)) =
        f.val (Quotient.mk (coveredRelation F ζ hζ U) (x, c))
      rw [← Quotient.sound (show coveredRelation F ζ hζ U (x, c)
        (γ • x, KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ * c) from
          ⟨γ, 1, by simp, by simp⟩)]
    · intro x c ε
      change f.val (Quotient.mk (coveredRelation F ζ hζ U)
          (x, KPCuspGenuineMonodromy.central F ζ hζ ε * c)) =
        (chi F ζ hζ ε : ℂ) * f.val (Quotient.mk (coveredRelation F ζ hζ U) (x, c))
      rw [← z_mk F ζ hζ U ε x c]
      exact f.property ε _
    · intro x c u
      change f.val (Quotient.mk (coveredRelation F ζ hζ U)
          (x, c * (u : FiniteCover F ζ hζ))) =
        f.val (Quotient.mk (coveredRelation F ζ hζ U) (x, c))
      rw [← Quotient.sound (show coveredRelation F ζ hζ U (x, c)
        (x, c * (u : FiniteCover F ζ hζ)) from ⟨1, u, by simp, by simp⟩)]⟩
  invFun g := ⟨Quotient.lift g.val (by
    intro a b hab
    obtain ⟨x, c⟩ := a
    obtain ⟨y, d⟩ := b
    obtain ⟨γ, u, hy, hd⟩ := hab
    subst hy
    subst hd
    rw [mul_assoc, g.property.1 x (c * (u : FiniteCover F ζ hζ)) γ,
      g.property.2.2 x c u]), by
    intro ε v
    refine Quotient.inductionOn v ?_
    intro p
    obtain ⟨x, c⟩ := p
    rw [z_mk]
    exact g.property.2.1 x c ε⟩
  left_inv := by
    intro f
    apply Subtype.ext
    funext v
    refine Quotient.inductionOn v ?_
    intro p
    rfl
  right_inv := by
    intro g
    apply Subtype.ext
    funext p
    rfl
  map_add' := by
    intro f g
    apply Subtype.ext
    funext p
    rfl
  map_smul' := by
    intro c f
    apply Subtype.ext
    funext p
    rfl

theorem J_apply (f : GenuineCoveredScalars F ζ hζ U)
    (x : SymmetricSpace F) (c : FiniteCover F ζ hζ) :
    (J F ζ hζ U f).val (x, c) =
      f.val (Quotient.mk (coveredRelation F ζ hζ U) (x, c)) := by
  rfl

variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

def S : GenuineCoveredScalars F ζ hζ U ≃ₗ[ℂ]
    (∀ i : Fin (H.atlas U).componentCount,
      KPCuspGenuineMonodromy.sections F ζ hζ U
        ((H.atlas U).representative i) ((H.atlas U).line i).rho) :=
  (J F ζ hζ U).trans (H.atlas U).scalar_realization

theorem S_apply (f : GenuineCoveredScalars F ζ hζ U)
    (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F) :
    (S F ζ hζ U R P H f i).val x =
      f.val (Quotient.mk (coveredRelation F ζ hζ U)
        (x, (H.atlas U).representative i)) := by
  rw [S, LinearEquiv.trans_apply,
    (H.atlas U).scalar_realization_formula (J F ζ hζ U f) i x,
    J_apply]

theorem group_lift_formula (f : GenuineCoveredScalars F ζ hζ U)
    (a : KPSmoothActualFlowData.GInfinity F) (c : FiniteCover F ζ hζ) :
    f.val (KPContSectorQuotientRelationsComparison.piTilde F ζ hζ U
      (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
          (c : ActualCover F ζ hζ)))) =
      (J F ζ hζ U f).val (KPMsFixedHaarDisintegration.archBasepoint F a, c) := by
  rw [KPContSectorQuotientRelationsComparison.piTilde_quotientMap, J_apply]

theorem S_equivariance (f : GenuineCoveredScalars F ζ hζ U)
    (i : Fin (H.atlas U).componentCount)
    (γ : KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))
    (x : SymmetricSpace F) :
    (S F ζ hζ U R P H f i).val ((γ : KPCuspArithmetic.PGL2 F) • x) =
      (chi F ζ hζ (((H.atlas U).line i).rho γ) : ℂ) *
        (S F ζ hζ U R P H f i).val x := by
  exact (S F ζ hζ U R P H f i).property.2 γ x

end DedekindZetaZeroFree.KPContSectorScalarLineAlgebra

namespace DedekindZetaZeroFree

open KPContSectorCoveredQuotientVocabulary KPContSectorScalarLineAlgebra

end DedekindZetaZeroFree

end
