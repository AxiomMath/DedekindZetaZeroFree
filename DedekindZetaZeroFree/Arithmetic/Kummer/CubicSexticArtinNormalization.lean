module

public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Hilbert.SexticHilbertNormalization

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain ClassFieldTheory

namespace DedekindZetaZeroFree
namespace KPHilbert
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

variable (F : Type) [Field F] [NumberField F]

abbrev CFTSource (v : HeightOneSpectrum (𝓞 F)) := (HeightOneSpectrum.adicAbv F v).Completion

variable (v : HeightOneSpectrum (𝓞 F))

local instance : ValuativeRel (CFTSource F v) :=
  GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinCompletionValuativeRel v
local instance : IsNonarchimedeanLocalField (CFTSource F v) :=
  GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
local instance : CharZero (CFTSource F v) :=
  charZero_of_injective_algebraMap (algebraMap F (CFTSource F v)).injective

def cftSourceUnit (a : (v.adicCompletion F)ˣ) : (CFTSource F v)ˣ :=
  (Units.mapEquiv (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv.toMulEquiv).symm a

def cftSourceRoots (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) F).Nonempty) :
    (primitiveRoots (n : ℕ) (CFTSource F v)).Nonempty := by
  obtain ⟨z, hz⟩ := hmu
  exact ⟨algebraMap F (CFTSource F v) z, (mem_primitiveRoots n.pos).2
    (((mem_primitiveRoots n.pos).1 hz).map_of_injective
      (algebraMap F (CFTSource F v)).injective)⟩

def cftSourceCoefficients (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) F).Nonempty) :
    rootsOfUnity (n : ℕ) (CFTSource F v) ≃* rootsOfUnity (n : ℕ) (v.adicCompletion F) :=
  rootsOfUnityEquivOfRingEquiv (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv n
    (cftSourceRoots F v n hmu)

theorem B3_localSameCFT (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (a b : (v.adicCompletion F)ˣ) :
    finiteRootsThree F ζ hζ v (B3 F ζ hζ (Sum.inr v) a b) =
      finitePlaceAdicHilbertPairingFamily F 3 (rootsThree F ζ hζ) v
        (powerClass _ 3 b) (powerClass _ 3 a) := by
  rw [B3_canonical]
  change (finiteRootsThree F ζ hζ v)
    (NormalizedSymbolTransport.inverseTransport (finiteRootsThree F ζ hζ v)
      (finitePlaceAdicHilbertPairingFamily F 3 (rootsThree F ζ hζ) v) _ _) = _
  erw [NormalizedSymbolTransport.map_inverseTransport]
  have hs := (finitePlaceAdicHilbertPairingFamily_isLocallyHilbert
    F 3 (rootsThree F ζ hζ) v).2.1
  rw [hs]
  simp
  rfl

theorem finiteFamily_source (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (a b : (v.adicCompletion F)ˣ) :
    (cftSourceCoefficients F v n hmu).symm
      (finitePlaceAdicHilbertPairingFamily F n hmu v (powerClass _ n a) (powerClass _ n b)) =
    localHilbertPairing (CFTSource F v) n (Nat.cast_ne_zero.mpr n.ne_zero)
      (cftSourceRoots F v n hmu)
      (powerClass _ n (cftSourceUnit F v a)) (powerClass _ n (cftSourceUnit F v b)) := by
  unfold finitePlaceAdicHilbertPairingFamily
  rw [hilbertPairingOfRingEquiv_apply,
    powerClassGroupEquivOfRingEquiv_symm_powerClass,
    powerClassGroupEquivOfRingEquiv_symm_powerClass]
  exact (cftSourceCoefficients F v n hmu).symm_apply_apply _

end
end KPHilbert
end DedekindZetaZeroFree
