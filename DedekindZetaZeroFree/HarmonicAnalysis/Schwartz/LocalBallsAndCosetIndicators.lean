module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.TraceCharacters.LocalTraceCharacter
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CompletionBallMass
public import Mathlib.Topology.LocallyConstant.Algebra

@[expose] public section

noncomputable section

open scoped NumberField Classical WithZero
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree

variable (F : Type) [Field F] [NumberField F]

def finiteCompletionBall (v : HeightOneSpectrum (𝓞 F)) (n : ℤ) :
    AddSubgroup (v.adicCompletion F) where
  carrier := {x | Valued.v x ≤ WithZero.exp (-n)}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    exact (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).map_add_le hx hy
  neg_mem' := by
    intro x hx
    change Valued.v (-x) ≤ WithZero.exp (-n)
    change Valued.v x ≤ WithZero.exp (-n) at hx
    simpa only [Valuation.map_neg] using hx

@[simp] theorem mem_finiteCompletionBall (v : HeightOneSpectrum (𝓞 F))
    (n : ℤ) (x : v.adicCompletion F) :
    x ∈ finiteCompletionBall F v n ↔ Valued.v x ≤ WithZero.exp (-n) :=
  Iff.rfl

def localFiniteAnnihilator (v : HeightOneSpectrum (𝓞 F))
    (U : AddSubgroup (v.adicCompletion F)) : AddSubgroup (v.adicCompletion F) where
  carrier := {y | ∀ u ∈ U, localFiniteCharacter F v (u * y) = 1}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy u hu
    rw [mul_add, AddChar.map_add_eq_mul, hx u hu, hy u hu, one_mul]
  neg_mem' := by
    intro x hx u hu
    rw [mul_neg, AddChar.map_neg_eq_inv, hx u hu, inv_one]

@[simp] theorem mem_localFiniteAnnihilator (v : HeightOneSpectrum (𝓞 F))
    (U : AddSubgroup (v.adicCompletion F)) (y : v.adicCompletion F) :
    y ∈ localFiniteAnnihilator F v U ↔
      ∀ u ∈ U, localFiniteCharacter F v (u * y) = 1 :=
  Iff.rfl

def localSchwartz (v : HeightOneSpectrum (𝓞 F)) :
    Submodule ℂ (v.adicCompletion F → ℂ) where
  carrier := {f | IsLocallyConstant f ∧ HasCompactSupport f}
  zero_mem' := ⟨IsLocallyConstant.zero, HasCompactSupport.zero⟩
  add_mem' := by
    intro f g hf hg
    exact ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' := by
    intro c f hf
    exact ⟨hf.1.comp (fun z => c • z), hf.2.smul_left (f := fun _ => c)⟩

@[simp] theorem mem_localSchwartz (v : HeightOneSpectrum (𝓞 F))
    (f : v.adicCompletion F → ℂ) :
    f ∈ localSchwartz F v ↔ IsLocallyConstant f ∧ HasCompactSupport f :=
  Iff.rfl

def localCosetIndicator (v : HeightOneSpectrum (𝓞 F))
    (b : v.adicCompletion F) (U : AddSubgroup (v.adicCompletion F)) :
    v.adicCompletion F → ℂ :=
  {x | x - b ∈ U}.indicator (fun _ => (1 : ℂ))

@[simp] theorem localCosetIndicator_apply (v : HeightOneSpectrum (𝓞 F))
    (b : v.adicCompletion F) (U : AddSubgroup (v.adicCompletion F))
    (x : v.adicCompletion F) :
    localCosetIndicator F v b U x = if x - b ∈ U then 1 else 0 := by
  simp [localCosetIndicator, Set.indicator]

end DedekindZetaZeroFree

end
