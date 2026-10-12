module

public import ClassFieldTheory.Definitions.HilbertSymbols.GlobalHilbertPairingFamily
public import ClassFieldTheory.Definitions.HilbertSymbols.PowerClass
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Finite-place factors of a global Hilbert pairing family
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory.GlobalHilbertPairingFamily

universe u

/-- Evaluate a local pairing on two nonzero elements of the number field and
transport the resulting root of unity back to the number field. -/
def finiteFactor
    (F : Type u) [Field F] [NumberField F]
    {n : ℕ+} (B : GlobalHilbertPairingFamily F n)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (v : HeightOneSpectrum (𝓞 F)) (a b : Fˣ) :
    rootsOfUnity (n : ℕ) F := by
  letI : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let e : rootsOfUnity (n : ℕ) F ≃* rootsOfUnity (n : ℕ) (v.adicCompletion F) :=
    rootsOfUnityEquivOfPrimitiveRoots
      (algebraMap F (v.adicCompletion F)).injective hmu
  exact e.symm
    (B v
      (powerClass (v.adicCompletion F) n
        (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a))
      (powerClass (v.adicCompletion F) n
        (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom b)))

end ClassFieldTheory.GlobalHilbertPairingFamily

end
