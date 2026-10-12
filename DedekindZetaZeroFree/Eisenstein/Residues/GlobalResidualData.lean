module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.FiniteExceptionalRepresentationData
public import DedekindZetaZeroFree.Metaplectic.Torus.RationalCentralCharacter
public import DedekindZetaZeroFree.Algebra.TensorProduct.RestrictedTensorSimplicity
public import DedekindZetaZeroFree.Eisenstein.Continuation.SmoothMeromorphicFunctions
public import DedekindZetaZeroFree.Eisenstein.Induction.BorelBruhatTwoCells
public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.AdditivePeriodization
public import DedekindZetaZeroFree.Eisenstein.Induction.ExceptionalParameterExponents

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped NumberField Classical TensorProduct Topology NNReal BigOperators
open NumberField IsDedekindDomain MeasureTheory ValuativeRel

namespace DedekindZetaZeroFree.KPGlobalResidualConstruction

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev G := KPGlobalTorusFunctionData.G F ζ hζ

def complexCore : Submodule ℂ (KPCplxPrincipalSeriesCharts.PrincipalSeries
    KPCplxPrincipalSeriesCharts.negativeParameter) :=
  KPCplxActualImage.imageSubmodule (1 : ℂˣ) ⊓
    ⨆ ℓ : ℕ, KPCplxIntertwinerEigenvalues.harmonicKType
      KPCplxPrincipalSeriesCharts.negativeParameter ℓ

abbrev RationalFiber := KPGlobalTorusFunctionData.ScalarFunctions
  (KPGlobalCenterRationalCharacter.R F ζ hζ)
  (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ).toMonoidHom

structure RationalSplitting where
  lift : Matrix.ProjGenLinGroup (Fin 2) F →* G F ζ hζ
  on_matrix : ∀ g : KubotaRankTwo.GL2 F,
    lift (Matrix.ProjGenLinGroup.mk g) =
      KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.rationalHom F ζ hζ g)

abbrev ArchCoordinates := InfinitePlace F → Fin 3 → ℂ

def archBase : ArchCoordinates F := fun _ i => if i = 1 then 1 else 0

def archDomain : Set (ArchCoordinates F) := {x | ∀ w, x w 1 ≠ 0}

def archChart (x : ArchCoordinates F) : G F ζ hζ := by
  let tuple : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ :=
    ⟨fun v => match v with
      | Sum.inr _ => 1
      | Sum.inl w =>
        let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F ζ hζ w)
        KPStandardLocalRootLifts.N F ζ hζ (Sum.inl w) (e.symm (x w 0)) *
        KPStandardLocalRootLifts.A F ζ hζ (Sum.inl w)
          (if h : x w 1 = 0 then 1 else Units.mk0 (e.symm (x w 1))
            (by exact fun h0 => h (by simpa using congrArg e h0))) *
        KPStandardLocalRootLifts.LowerN F ζ hζ (Sum.inl w) (e.symm (x w 2)), by
      apply Filter.Eventually.of_forall
      intro v
      cases v with
      | inl w => exact Subgroup.mem_top _
      | inr q => exact Subgroup.one_mem _⟩
  exact KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
    (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ tuple)

abbrev Jet := Σ n : ℕ, Fin n → ArchCoordinates F

def complexCompactLift (w : InfinitePlace F)
    (k : KPCplxCharacterHaar.ComplexSU2) : G F ζ hζ :=
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (KPHilbert.infinite_isComplex F ζ hζ w)
  KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
    (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inl w)
      (KPLocalCover.sectionMap F ζ hζ (Sum.inl w)
        (Matrix.GeneralLinearGroup.map e.symm.toRingHom
          (KPCplxCharacterHaar.complexSU2Embedding k))))

end DedekindZetaZeroFree.KPGlobalResidualConstruction

end

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped NumberField Classical TensorProduct Topology NNReal BigOperators
open NumberField IsDedekindDomain MeasureTheory ValuativeRel

namespace DedekindZetaZeroFree.KPGlobalResidualConstruction

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev B := KPGlobalTorusFunctionData.borel F ζ hζ
abbrev A := KPGlobalTorusFunctionData.Adeles F
abbrev Y := A F ⧸ AdeleRing.principalSubgroup (𝓞 F) F
abbrev Places := KPHilbert.Place F

abbrev smoothRationalFiber : Submodule ℂ (RationalFiber F ζ hζ) := by
  letI : AddCommGroup (RationalFiber F ζ hζ) := inferInstance
  exact KPGlobalTorusFunctionData.SmoothUnion
    (KPGlobalCenterRationalCharacter.R F ζ hζ)
    (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ).toMonoidHom
    (KPGlobalTorusFunctionData.torusArchChart F ζ hζ)
    (KPGlobalTorusFunctionData.torusArchDomain F)
    (fun U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ =>
      (KPGlobalTorusFunctionData.globalLevel F ζ hζ U).comap
        (KPGlobalTorusFunctionData.torus F ζ hζ).subtype)

def upperConstantTerm (dq : Measure (Y F)) (f : G F ζ hζ → ℂ) (g : G F ζ hζ) : ℂ :=
  ∫ q, f (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) * g) ∂dq

end DedekindZetaZeroFree.KPGlobalResidualConstruction

end
end
