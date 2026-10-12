module

public import DedekindZetaZeroFree.Eisenstein.Sections.LiteralSeries
public import DedekindZetaZeroFree.Metaplectic.Torus.BorelTwistCompatibility

@[expose] public section

section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField
namespace DedekindZetaZeroFree.KPLiteralTensor
open KPLiteralRaw
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev harmonicPlus : Submodule ℂ (KPCplxPrincipalSeriesCharts.PrincipalSeries
    KPCplxPrincipalSeriesCharts.positiveParameter) :=
  ⨆ ℓ : ℕ, KPCplxIntertwinerEigenvalues.harmonicKType
    KPCplxPrincipalSeriesCharts.positiveParameter ℓ

end DedekindZetaZeroFree.KPLiteralTensor

end

end

section

noncomputable section

open scoped NumberField Classical TensorProduct

open NumberField MeasureTheory

set_option maxHeartbeats 8000000

set_option synthInstance.maxHeartbeats 200000

set_option backward.isDefEq.respectTransparency false

namespace DedekindZetaZeroFree.ScalarRationalProductTransport

open KPGlobalTorusBorelTwistCompatibility

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

variable (C : ModelData F ζ hζ) (s : ℂ)

def scalar (P : Polarization F ζ hζ) :
    Induced F ζ hζ P →ₗ[ℂ] (G F ζ hζ → ℂ) :=
  (KPGlobalTorusFunctionData.BorelFunctions F ζ hζ P).subtype.comp
    (scalarSection F ζ hζ P)

theorem scalar_injective (P : Polarization F ζ hζ) :
    Function.Injective (scalar F ζ hζ P) := by
  intro f h he
  apply Subtype.ext
  apply Subtype.ext
  funext g
  apply Subtype.ext
  apply Subtype.ext
  funext t
  rw [scalar_transitivity, scalar_transitivity]
  exact congrArg ((KPGlobalTorusFunctionData.deltaHalf F ζ hζ t)⁻¹ * ·)
    (congrFun he (t.val * g))

end DedekindZetaZeroFree.ScalarRationalProductTransport

end

end

section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField MeasureTheory
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.ScalarRationalProductTransport
open KPGlobalTorusBorelTwistCompatibility
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : ModelData F ζ hζ) (s : ℂ)

local instance (P : Polarization F ζ hζ) : TopologicalSpace (Induced F ζ hζ P) :=
  inducedTopology F ζ hζ P

private def inducedEquiv :
    Induced F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) ≃ₗ[ℂ]
      Induced F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) where
  toLinearMap := (borelP F ζ hζ C s).toLinearMap
  invFun := borelQ F ζ hζ C s
  left_inv := borelQ_borelP F ζ hζ C s
  right_inv := borelP_borelQ F ζ hζ C s

private theorem scalar_intertwines (P : Polarization F ζ hζ)
    (a : G F ζ hζ) (f : Induced F ζ hζ P) :
    scalar F ζ hζ P (inducedRightAction F ζ hζ P a f) =
      KPLiteralRaw.rightAction F ζ hζ a (scalar F ζ hζ P f) := by
  funext g
  rfl

private def orbitSpan {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (ρ : Representation ℂ (G F ζ hζ) V) (K : Subgroup (G F ζ hζ)) (v : V) :
    Submodule ℂ V := Submodule.span ℂ (Set.range fun k : K => ρ k.val v)

set_option maxHeartbeats 400000

private theorem mapOrbitSpan {V W : Type*} [AddCommMonoid V] [Module ℂ V]
    [AddCommMonoid W] [Module ℂ W]
    (ρ : Representation ℂ (G F ζ hζ) V) (σ : Representation ℂ (G F ζ hζ) W)
    (L : V →ₗ[ℂ] W) (hL : ∀ a v, L (ρ a v) = σ a (L v))
    (K : Subgroup (G F ζ hζ)) (v : V) :
    (orbitSpan F ζ hζ ρ K v).map L = orbitSpan F ζ hζ σ K (L v) := by
  change (Submodule.span ℂ (Set.range fun k : K => ρ k.val v)).map L = _
  rw [Submodule.map_span, ← Set.range_comp]
  apply congrArg (Submodule.span ℂ)
  apply congrArg Set.range
  funext k
  exact hL k.val v

private theorem scalar_orbitSpan (P : Polarization F ζ hζ)
    (K : Subgroup (G F ζ hζ)) (f : Induced F ζ hζ P) :
    (orbitSpan F ζ hζ (inducedRightAction F ζ hζ P) K f).map (scalar F ζ hζ P) =
      orbitSpan F ζ hζ (KPLiteralRaw.rightAction F ζ hζ) K (scalar F ζ hζ P f) := by
  exact mapOrbitSpan F ζ hζ (inducedRightAction F ζ hζ P)
    (KPLiteralRaw.rightAction F ζ hζ) (scalar F ζ hζ P)
    (scalar_intertwines F ζ hζ P) K f

private def scalarOrbitEquiv (P : Polarization F ζ hζ)
    (K : Subgroup (G F ζ hζ)) (f : Induced F ζ hζ P) :
    orbitSpan F ζ hζ (inducedRightAction F ζ hζ P) K f ≃ₗ[ℂ]
      orbitSpan F ζ hζ (KPLiteralRaw.rightAction F ζ hζ) K (scalar F ζ hζ P f) :=
  (Submodule.equivMapOfInjective (scalar F ζ hζ P) (scalar_injective F ζ hζ P) _).trans
    (LinearEquiv.ofEq _ _ (scalar_orbitSpan F ζ hζ P K f))

private theorem induced_orbitSpan (K : Subgroup (G F ζ hζ))
    (f : Induced F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s)) :
    (orbitSpan F ζ hζ (inducedRightAction F ζ hζ _) K f).map
      (inducedEquiv F ζ hζ C s).toLinearMap =
      orbitSpan F ζ hζ (inducedRightAction F ζ hζ _) K (borelP F ζ hζ C s f) := by
  exact mapOrbitSpan F ζ hζ (inducedRightAction F ζ hζ _)
    (inducedRightAction F ζ hζ _) (inducedEquiv F ζ hζ C s).toLinearMap
    (borelP_intertwines F ζ hζ C s) K f

private def inducedOrbitEquiv (K : Subgroup (G F ζ hζ))
    (f : Induced F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s)) :
    orbitSpan F ζ hζ (inducedRightAction F ζ hζ _) K f ≃ₗ[ℂ]
      orbitSpan F ζ hζ (inducedRightAction F ζ hζ _) K (borelP F ζ hζ C s f) :=
  (inducedEquiv F ζ hζ C s).ofSubmodules _ _ (induced_orbitSpan F ζ hζ C s K f)

private def scalarTransportOrbitEquiv (K : Subgroup (G F ζ hζ))
    (f : Induced F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s)) :
    orbitSpan F ζ hζ (KPLiteralRaw.rightAction F ζ hζ) K (scalar F ζ hζ _ f) ≃ₗ[ℂ]
      orbitSpan F ζ hζ (KPLiteralRaw.rightAction F ζ hζ) K
        (scalar F ζ hζ _ (borelP F ζ hζ C s f)) :=
  (scalarOrbitEquiv F ζ hζ _ K f).symm.trans
    ((inducedOrbitEquiv F ζ hζ C s K f).trans
      (scalarOrbitEquiv F ζ hζ _ K (borelP F ζ hζ C s f)))

private theorem kFinite_iff_orbitSpan (K : Subgroup (G F ζ hζ)) (φ : G F ζ hζ → ℂ) :
    KPLiteralRaw.KFinite F ζ hζ K φ ↔
      Module.Finite ℂ (orbitSpan F ζ hζ (KPLiteralRaw.rightAction F ζ hζ) K φ) := by
  constructor
  · rintro ⟨S, hS, hφ, hstable⟩
    let := hS
    have hle : orbitSpan F ζ hζ (KPLiteralRaw.rightAction F ζ hζ) K φ ≤ S := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, rfl⟩
      exact hstable k φ hφ
    exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  · intro hfin
    refine ⟨orbitSpan F ζ hζ (KPLiteralRaw.rightAction F ζ hζ) K φ, hfin, ?_, ?_⟩
    · have hmem := Submodule.subset_span (Set.mem_range_self (1 : K))
        (R := ℂ) (s := Set.range fun k : K => KPLiteralRaw.rightAction F ζ hζ k.val φ)
      simpa [orbitSpan] using hmem
    · intro k v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨j, rfl⟩ := hv
        have hmul : KPLiteralRaw.rightAction F ζ hζ k.val
            (KPLiteralRaw.rightAction F ζ hζ j.val φ) =
            KPLiteralRaw.rightAction F ζ hζ (k * j).val φ := by
          funext g
          change φ ((g * k.val) * j.val) = φ (g * (k.val * j.val))
          rw [mul_assoc]
        rw [hmul]
        exact Submodule.subset_span (Set.mem_range_self (k * j))
      | zero => simpa only [map_zero] using Submodule.zero_mem _
      | add v w _ _ hv hw => simpa only [map_add] using Submodule.add_mem _ hv hw
      | smul c v _ hv => simpa only [map_smul] using Submodule.smul_mem _ c hv

 theorem scalar_borelP_kFinite_iff (K : Subgroup (G F ζ hζ))
    (f : Induced F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s)) :
    KPLiteralRaw.KFinite F ζ hζ K (scalar F ζ hζ _ f) ↔
      KPLiteralRaw.KFinite F ζ hζ K (scalar F ζ hζ _ (borelP F ζ hζ C s f)) := by
  exact (kFinite_iff_orbitSpan F ζ hζ K _).trans
    ((Module.Finite.equiv_iff (scalarTransportOrbitEquiv F ζ hζ C s K f)).trans
      (kFinite_iff_orbitSpan F ζ hζ K _).symm)

end DedekindZetaZeroFree.ScalarRationalProductTransport

end
end

section
noncomputable section
namespace DedekindZetaZeroFree.KPLiteralTensor
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev RationalInduced := KPGlobalTorusBorelTwistCompatibility.Induced F ζ hζ
  (KPGlobalTorusBorelTwistCompatibility.rationalModel F ζ hζ)

end DedekindZetaZeroFree.KPLiteralTensor
end
end
