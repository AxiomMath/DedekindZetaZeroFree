module

public import DedekindZetaZeroFree.Theta.Digits.SphericalValueBounds

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.OrbitFrequencies.IntegralFrequency
open NumberField
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]

 def rowUnit (A : SArithmeticData F) (r : ProbeOrbitNormSum.Nonzero A) : Fˣ :=
  Units.mk0 (r.val : F) (by intro h; exact r.property (Subtype.ext h))

 theorem unitEquiv_coe (A : SArithmeticData F) (u : A.U) :
    ((A.unitEquiv u : A.R) : F) = (u.val : F) := rfl

def orbitFrequency (A : SArithmeticData F) : ProbeOrbitNormSum.Orbit A → ThetaReflectionData.Frequency A :=
  Quotient.lift (fun r => QuotientGroup.mk (rowUnit A r)) (by
    intro r s hrs
    obtain ⟨γ, hγ⟩ := MulAction.orbitRel_apply.mp hrs
    apply Quotient.sound
    change QuotientGroup.leftRel (ThetaReflectionData.rationalGamma A) _ _
    rw [QuotientGroup.leftRel_apply]
    have he : rowUnit A r = γ.val.val * rowUnit A s := by
      apply Units.ext
      have hh := congrArg (fun t : ProbeOrbitNormSum.Nonzero A => (t.val : F)) hγ
      change ((A.unitEquiv γ.val : A.R) : F) * (s.val : F) = (r.val : F) at hh
      rw [unitEquiv_coe] at hh
      exact hh.symm
    rw [he]
    have hmem : γ.val.val ∈ ThetaReflectionData.rationalGamma A := by
      obtain ⟨u, hu⟩ := γ.property
      refine ⟨u.val, u.property, ?_⟩
      exact congrArg Subtype.val hu
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (ThetaReflectionData.rationalGamma A).inv_mem hmem)

@[simp] theorem orbitFrequency_mk (A : SArithmeticData F) (r : ProbeOrbitNormSum.Nonzero A) :
    orbitFrequency A (ProbeOrbitNormSum.orbitMk A r) = QuotientGroup.mk (rowUnit A r) := rfl

end DedekindZetaZeroFree.OrbitFrequencies.IntegralFrequency
end

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.OrbitFrequencies
open MomentSources NumberField MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open scoped NumberField Classical
namespace IntegralFrequency
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

abbrev Support (m : ThetaReflectionData.Row R.A) :=
  {ξ : ThetaReflectionData.Frequency R.A // ((ThetaReflectionData.rowUnit R.A m ^ 2 * Quotient.out ξ : Fˣ) : F) ∈ R.A.R}

def cleared (m : ThetaReflectionData.Row R.A) (ξ : Support R m) : ProbeOrbitNormSum.Nonzero R.A :=
  ⟨⟨((ThetaReflectionData.rowUnit R.A m ^ 2 * Quotient.out ξ.val : Fˣ) : F), ξ.property⟩,
    by
      intro hz
      exact (ThetaReflectionData.rowUnit R.A m ^ 2 * Quotient.out ξ.val).ne_zero
        (congrArg (fun a : R.A.R => (a : F)) hz)⟩

def orbit (m : ThetaReflectionData.Row R.A) (ξ : Support R m) : ProbeOrbitNormSum.Orbit R.A :=
  ProbeOrbitNormSum.orbitMk R.A (cleared R m ξ)

lemma orbit_frequency (m : ThetaReflectionData.Row R.A) (ξ : Support R m) :
    orbitFrequency R.A (orbit R m ξ) =
      (QuotientGroup.mk (ThetaReflectionData.rowUnit R.A m ^ 2) : ThetaReflectionData.Frequency R.A) * ξ.val := by
  rw [orbit, orbitFrequency_mk]
  change QuotientGroup.mk (Units.mk0 _ _) = _
  have he : (Units.mk0 ((cleared R m ξ).val : F) (by
      intro h; exact (cleared R m ξ).property (Subtype.ext h))) =
      ThetaReflectionData.rowUnit R.A m ^ 2 * Quotient.out ξ.val := Units.ext rfl
  rw [he, QuotientGroup.mk_mul]
  exact congrArg (fun z : ThetaReflectionData.Frequency R.A =>
    (QuotientGroup.mk (ThetaReflectionData.rowUnit R.A m ^ 2) : ThetaReflectionData.Frequency R.A) * z)
    (Quotient.out_eq ξ.val)

lemma orbit_injective (m : ThetaReflectionData.Row R.A) : Function.Injective (orbit R m) := by
  letI : (ThetaReflectionData.rationalGamma R.A).Normal := inferInstance
  intro ξ ζ h
  apply Subtype.ext
  have he := congrArg (orbitFrequency R.A) h
  rw [orbit_frequency, orbit_frequency] at he
  exact mul_left_cancel he

lemma orbit_norm (m : ThetaReflectionData.Row R.A) (ξ : Support R m) :
    ProbeOrbitNormSum.orbitNorm R.A (orbit R m ξ) =
      (q R.A (ThetaReflectionData.rowUnit R.A m)).val ^ 2 * ThetaReflectionData.frequencyNorm R.A ξ.val := by
  rw [orbit, ProbeOrbitNormSum.orbitNorm_eq_snorm R.A (cleared R m ξ)
    (ThetaReflectionData.rowUnit R.A m ^ 2 * Quotient.out ξ.val) rfl,
    map_mul, map_pow, NormSheetsCoordinates.norm_mul]
  have hp : R.A.norm (R.A.diagonal (ThetaReflectionData.rowUnit R.A m) ^ 2) =
      R.A.norm (R.A.diagonal (ThetaReflectionData.rowUnit R.A m)) ^ 2 := by
    rw [pow_two, NormSheetsCoordinates.norm_mul, pow_two]
  rw [hp]
  have he := ThetaReflectionData.frequencyNorm_mk R.A (Quotient.out ξ.val)
  have ho : (QuotientGroup.mk (Quotient.out ξ.val) : ThetaReflectionData.Frequency R.A) = ξ.val := Quotient.out_eq ξ.val
  rw [ho] at he
  rw [← he]
  rfl

end IntegralFrequency
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

def frequencyMajorant (m : ThetaReflectionData.Row R.A) (ξ : ThetaReflectionData.Frequency R.A) : ℝ :=
  if ((ThetaReflectionData.rowUnit R.A m ^ 2 * Quotient.out ξ : Fˣ) : F) ∈ R.A.R
  then (ThetaReflectionData.frequencyNorm R.A ξ) ^ (-2 : ℤ) else 0

lemma frequencyMajorant_summable (m : ThetaReflectionData.Row R.A) : Summable (frequencyMajorant R m) := by
  let C := (q R.A (ThetaReflectionData.rowUnit R.A m)).val ^ 4
  have hs := (ProbeOrbitNormSum.orbit_norm_rpow_summable R.A 2 (by norm_num)).mul_left C
  have ht : Summable (fun ξ : IntegralFrequency.Support R m =>
      (ThetaReflectionData.frequencyNorm R.A ξ.val) ^ (-2 : ℤ)) := by
    have he := hs.comp_injective (IntegralFrequency.orbit_injective R m)
    apply he.congr
    intro ξ
    change C * (ProbeOrbitNormSum.orbitNorm R.A (IntegralFrequency.orbit R m ξ)) ^ (-2 : ℝ) = _
    rw [IntegralFrequency.orbit_norm]
    rw [show (-2 : ℝ) = -(2 : ℝ) from rfl,
      Real.rpow_neg (mul_nonneg (sq_nonneg _) (ThetaReflectionData.frequencyNorm_pos R.A ξ.val).le), Real.rpow_two]
    simp only [C, mul_pow, mul_inv_rev, zpow_neg, zpow_ofNat]
    have hn := (q R.A (ThetaReflectionData.rowUnit R.A m)).property
    field_simp
  exact (summable_subtype_iff_indicator (s := {ξ : ThetaReflectionData.Frequency R.A |
    ((ThetaReflectionData.rowUnit R.A m ^ 2 * Quotient.out ξ : Fˣ) : F) ∈ R.A.R})).mp ht

end DedekindZetaZeroFree.OrbitFrequencies
end
