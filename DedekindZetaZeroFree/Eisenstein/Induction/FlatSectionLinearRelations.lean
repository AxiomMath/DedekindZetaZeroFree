module

public import DedekindZetaZeroFree.Eisenstein.Induction.CompactAndFlatSections
public import DedekindZetaZeroFree.Eisenstein.Residues.MetaplecticRealizations

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField
namespace DedekindZetaZeroFree.KPLiteralTensorEquivariance.FiniteClearedCovariance
open KPLiteralRaw
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem flat_finite_combination_of_zero
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (f : Flat F ζ hζ K) (n : ℕ) (d : Fin n → ℂ)
    (v : Fin n → Flat F ζ hζ K)
    (hzero : ∀ g, f.val 0 g = ∑ i, d i * (v i).val 0 g) :
    ∀ z g, f.val z g = ∑ i, d i * (v i).val z g := by
  intro z g
  simp_rw [← KPLiteralChamber.compactExtension_eq_flat F ζ hζ K hK,
    KPLiteralChamber.compactExtension]
  simp_rw [mul_left_comm (d _)]
  rw [← Finset.mul_sum, hzero]

end DedekindZetaZeroFree.KPLiteralTensorEquivariance.FiniteClearedCovariance

end
