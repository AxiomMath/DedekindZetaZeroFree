module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.RootsOfUnityAndPowerClasses

@[expose] public section

namespace DedekindZetaZeroFree
namespace NormalizedSymbolTransport

set_option autoImplicit false

variable {C M N : Type*} [CommGroup C] [CommGroup M] [CommGroup N]

def inverseTransport (e : M ≃* N) (B : C →* C →* N) : C →* C →* M where
  toFun a := e.symm.toMonoidHom.comp (invMonoidHom.comp (B a))
  map_one' := by
    ext b
    change e.symm (((B 1) b)⁻¹) = 1
    rw [map_one, MonoidHom.one_apply, inv_one, map_one]
  map_mul' := by
    intro a c
    ext b
    change e.symm (((B (a * c)) b)⁻¹) =
      e.symm ((B a b)⁻¹) * e.symm ((B c b)⁻¹)
    rw [map_mul, MonoidHom.mul_apply, mul_inv, map_mul]

theorem inverseTransport_apply (e : M ≃* N) (B : C →* C →* N) (a b : C) :
    inverseTransport e B a b = e.symm ((B a b)⁻¹) := rfl

theorem map_inverseTransport (e : M ≃* N) (B : C →* C →* N) (a b : C) :
    e (inverseTransport e B a b) = (B a b)⁻¹ := by
  simp [inverseTransport_apply]

theorem inverseTransport_skew (e : M ≃* N) (B : C →* C →* N)
    (hskew : ∀ a b : C, B a b = (B b a)⁻¹) (a b : C) :
    inverseTransport e B a b = (inverseTransport e B b a)⁻¹ := by
  simp [inverseTransport_apply, hskew a b]

theorem inverseTransport_left_nondegenerate (e : M ≃* N) (B : C →* C →* N)
    (h : ∀ a : C, (∀ b : C, B a b = 1) → a = 1) :
    ∀ a : C, (∀ b : C, inverseTransport e B a b = 1) → a = 1 := by
  intro a ha
  apply h a
  intro b
  have hb := congrArg e (ha b)
  simpa only [map_inverseTransport, map_one, inv_eq_one] using hb

end NormalizedSymbolTransport

namespace SArithmeticData

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

variable {F : Type} [Field F] [NumberField F]

def finiteSymbolInverseTransport (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (hn : IsLocalRootOrder n)
    (B : PowerQuotient (v.adicCompletion F)ˣ n →*
      PowerQuotient (v.adicCompletion F)ˣ n →* rootsOfUnity n (v.adicCompletion F)) :
    PowerQuotient (v.adicCompletion F)ˣ n →*
      PowerQuotient (v.adicCompletion F)ˣ n →* rootsOfUnity n F :=
  NormalizedSymbolTransport.inverseTransport (A.finiteRootsEquiv v n hn) B

theorem finiteSymbolInverseTransport_local_value (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (hn : IsLocalRootOrder n)
    (B : PowerQuotient (v.adicCompletion F)ˣ n →*
      PowerQuotient (v.adicCompletion F)ˣ n →* rootsOfUnity n (v.adicCompletion F))
    (a b : PowerQuotient (v.adicCompletion F)ˣ n) :
    ((A.finiteRootsEquiv v n hn (A.finiteSymbolInverseTransport v n hn B a b) :
      rootsOfUnity n (v.adicCompletion F)) : (v.adicCompletion F)ˣ) =
        ((B a b : rootsOfUnity n (v.adicCompletion F)) : (v.adicCompletion F)ˣ)⁻¹ := by
  exact congrArg Subtype.val
    (NormalizedSymbolTransport.map_inverseTransport (A.finiteRootsEquiv v n hn) B a b)

theorem finiteSymbolInverseTransport_exponentCompatibility (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (m n k : ℕ)
    (hm : IsLocalRootOrder m) (hn : IsLocalRootOrder n)
    (Bm : PowerQuotient (v.adicCompletion F)ˣ m →*
      PowerQuotient (v.adicCompletion F)ˣ m →* rootsOfUnity m (v.adicCompletion F))
    (Bn : PowerQuotient (v.adicCompletion F)ˣ n →*
      PowerQuotient (v.adicCompletion F)ˣ n →* rootsOfUnity n (v.adicCompletion F))
    (a b : (v.adicCompletion F)ˣ)
    (hcompat :
      (Bm (QuotientGroup.mk' (powMonoidHom (α := (v.adicCompletion F)ˣ) m).range a)
          (QuotientGroup.mk' (powMonoidHom (α := (v.adicCompletion F)ˣ) m).range b) :
        (v.adicCompletion F)ˣ) =
      (Bn (QuotientGroup.mk' (powMonoidHom (α := (v.adicCompletion F)ˣ) n).range a)
          (QuotientGroup.mk' (powMonoidHom (α := (v.adicCompletion F)ˣ) n).range b) :
        (v.adicCompletion F)ˣ) ^ k) :
    (A.finiteRootsEquiv v m hm
      (A.finiteSymbolInverseTransport v m hm Bm
        (QuotientGroup.mk' (powMonoidHom (α := (v.adicCompletion F)ˣ) m).range a)
        (QuotientGroup.mk' (powMonoidHom (α := (v.adicCompletion F)ˣ) m).range b)) :
      (v.adicCompletion F)ˣ) =
    (A.finiteRootsEquiv v n hn
      (A.finiteSymbolInverseTransport v n hn Bn
        (QuotientGroup.mk' (powMonoidHom (α := (v.adicCompletion F)ˣ) n).range a)
        (QuotientGroup.mk' (powMonoidHom (α := (v.adicCompletion F)ˣ) n).range b)) :
      (v.adicCompletion F)ˣ) ^ k := by
  rw [A.finiteSymbolInverseTransport_local_value,
    A.finiteSymbolInverseTransport_local_value, hcompat, inv_pow]

end
end SArithmeticData
end DedekindZetaZeroFree
