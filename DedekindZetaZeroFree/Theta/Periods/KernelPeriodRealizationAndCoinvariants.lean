module

public import DedekindZetaZeroFree.Metaplectic.Cubic.Wild.ResidualScalarSubmodules
public import DedekindZetaZeroFree.Theta.Periods.PartialPeriodSourcesAndRootCoinvariants
public import DedekindZetaZeroFree.Theta.Whittaker.Borel.RootFiberContinuity

@[expose] public section

section

noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
open scoped NumberField
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPWildKernelUpperBound

open KPLocalExceptionalConstruction KPWildPartialPeriodFactorization

def quotientHaar (F : Type) [Field F] [NumberField F] :
    Measure (KPCompactFourier.AdditiveQuotient F) :=
  Measure.addHaarMeasure (⟨⟨Set.univ, isCompact_univ⟩, by simp⟩ :
    TopologicalSpace.PositiveCompacts (KPCompactFourier.AdditiveQuotient F))

instance quotientHaar_isAddHaarMeasure (F : Type) [Field F] [NumberField F] :
    (quotientHaar F).IsAddHaarMeasure := by
  unfold quotientHaar
  infer_instance

instance quotientHaar_isProbabilityMeasure (F : Type) [Field F] [NumberField F] :
    IsProbabilityMeasure (quotientHaar F) :=
  ⟨by exact Measure.addHaarMeasure_self⟩

end DedekindZetaZeroFree.KPWildKernelUpperBound

end

end

section

noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
open scoped NumberField
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPWildKernelUpperBound

open KPLocalExceptionalConstruction KPWildPartialPeriodFactorization

def borelRootFiber (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (θ : KPGlobalTorusFunctionData.G F ζ hζ → ℂ)
    (b : KPGlobalTorusFunctionData.borel F ζ hζ)
    (x : KPCompactFourier.AdditiveQuotient F) : ℂ :=
  θ (KPGlobalTorusFunctionData.N F ζ hζ (KPCompactFourier.representative F x) * b.val)

structure SourceKernelPeriodRealization
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (V : Type*) [AddCommGroup V] [Module ℂ V] where
  period : V →ₗ[ℂ] ℂ
  kernelFunction : period.ker →ₗ[ℂ] (KPGlobalTorusFunctionData.G F ζ hζ → ℂ)
  faithful : Function.Injective kernelFunction
  continuous : ∀ e, Continuous (kernelFunction e)
  rational_invariant : ∀ e (γ : KPRationalAdelicSplitting.RationalPGL2 F) g,
    kernelFunction e (KPRationalAdelicSplitting.rationalPGLHom F ζ hζ γ * g) =
      kernelFunction e g
  fiber_continuous : ∀ e b,
    Continuous (borelRootFiber F ζ hζ (kernelFunction e) b)
  fourier_zero : ∀ e b (χ : AddChar (KPCompactFourier.AdditiveQuotient F) Circle),
    Continuous χ →
    (∫ x, borelRootFiber F ζ hζ (kernelFunction e) b x * (χ x : ℂ)
      ∂quotientHaar F) = 0

end DedekindZetaZeroFree.KPWildKernelUpperBound

end
end

section

namespace DedekindZetaZeroFree.KPWildKernelSource

theorem invariant_linearMap_zero_of_coinvariants_subsingleton
    {H U E : Type*} [Monoid H]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ H U)
    (hcoinvariants : Subsingleton (Representation.Coinvariants ρ))
    (L : U →ₗ[ℂ] E) (hL : ∀ a, L.comp (ρ a) = L) :
    L = 0 := by
  have hker : Representation.Coinvariants.ker ρ = ⊤ :=
    Submodule.Quotient.subsingleton_iff.1 hcoinvariants
  have hle : Representation.Coinvariants.ker ρ ≤ LinearMap.ker L := by
    rw [Representation.Coinvariants.ker]
    apply Submodule.span_le.2
    rintro _ ⟨⟨a, x⟩, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, sub_eq_zero]
    simpa using LinearMap.congr_fun (hL a) x
  have htop : LinearMap.ker L = ⊤ := le_top.antisymm (hker ▸ hle)
  ext u
  have : u ∈ LinearMap.ker L := htop ▸ Submodule.mem_top
  simpa using this

end DedekindZetaZeroFree.KPWildKernelSource

end
