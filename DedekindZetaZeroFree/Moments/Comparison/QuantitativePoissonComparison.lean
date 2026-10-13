module

public import DedekindZetaZeroFree.Moments.Principal.Contour.Comparison
public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.Summability
public import DedekindZetaZeroFree.Moments.Probes.Poisson.NonprincipalSumBound

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.Compare

noncomputable section

open DedekindZetaZeroFree NumberField
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem c₀_ne_zero : Spectral.c₀ D ≠ 0 :=
  (Principal.principal_comparison D).1

theorem Iscale_sub_main_le :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 2 ≤ Z →
      ‖D.Iscale Z - Spectral.c₀ D * Spectral.f D Z‖ ≤ C * Z ^ (717 / 2000 : ℝ) := by
  obtain ⟨-, hJ, ⟨Cw, hCw, hw⟩, ⟨Cz, hCz, hz⟩, -, -⟩ := Principal.principal_comparison D
  obtain ⟨Cr, hCr, hr⟩ := Rows.nonprincipalSum_bound D
  obtain ⟨Co, hCo, ho⟩ := OmittedProbeBound.omittedSum_bound D
  have hrep : ∀ u : D.Row, u ∈ PoissonIdentity.repRows D := fun u => by
    rw [PoissonIdentity.repRows_eq_univ D]
    exact Set.mem_univ u
  have hset : ∀ k : ℕ, (PoissonKernel.dyadRows D ((2 : ℝ) ^ k) ∩ PoissonIdentity.repRows D) \
      PoissonKernel.principalRows D = Rows.nonprincipalDyad D k := by
    intro k
    ext u
    simp [Rows.nonprincipalDyad, PoissonKernel.principalRows, hrep u] <;> tauto
  have hprin : PoissonKernel.principalRows D ∩ PoissonIdentity.repRows D =
      PoissonKernel.principalRows D := by
    ext u; simp [hrep u]
  have hid : ∀ Z : ℝ, 2 ≤ Z → D.Iscale Z = PoissonKernel.Jpr D Z + Rows.nonprincipalSum D Z +
      PoissonFrequencyDecomposition.omittedSum D Z := by
    intro Z hZ
    have hZ0 : (0 : ℝ) < Z := by linarith
    have h2 : Rows.nonprincipalSum D Z = ∑' k : ℕ,
        PoissonKernel.J D ((PoissonKernel.dyadRows D ((2 : ℝ) ^ k) ∩ PoissonIdentity.repRows D) \
          PoissonKernel.principalRows D) 4 4 2 Z := by
      unfold Rows.nonprincipalSum Rows.dyadIntegral
      exact tsum_congr (fun k => by rw [hset k])
    rw [PoissonIdentity.Iscale_eq_principal_add_nonprincipal D Z hZ0,
      (PoissonIdentity.nonprincipal_eq_sum_dyads D Z hZ0).2, hprin, h2]
    try rfl
  have hexp1 : ∀ Z : ℝ, 2 ≤ Z → Z ^ (Scales.mainExponent - 37749867 / 1000000000) ≤ Z ^ (717 / 2000 : ℝ) := by
    intro Z hZ
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    norm_num [Scales.mainExponent]
  have hexp2 : ∀ Z : ℝ, 2 ≤ Z → Z ^ (Scales.mainExponent - 384999 / 10000000) ≤ Z ^ (717 / 2000 : ℝ) := by
    intro Z hZ
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    norm_num [Scales.mainExponent]
  refine ⟨Cw + Cz + Cr + Co, by positivity, fun Z hZ => ?_⟩
  have h1 : D.Iscale Z - Spectral.c₀ D * Spectral.f D Z =
      PrincipalWShift.Rw D Z + PrincipalZShift.Rz D Z + Rows.nonprincipalSum D Z +
        PoissonFrequencyDecomposition.omittedSum D Z := by
    rw [hid Z hZ, hJ Z hZ]; ring
  rw [h1]
  have hp : 0 ≤ Z ^ (717 / 2000 : ℝ) := Real.rpow_nonneg (by linarith) _
  have a1 := (hw Z hZ).trans (mul_le_mul_of_nonneg_left (hexp1 Z hZ) hCw.le)
  have a2 := (hz Z hZ).trans (mul_le_mul_of_nonneg_left (hexp2 Z hZ) hCz.le)
  have a3 := hr Z hZ
  have a4 := ho Z hZ
  calc _ ≤ ‖PrincipalWShift.Rw D Z‖ + ‖PrincipalZShift.Rz D Z‖ + ‖Rows.nonprincipalSum D Z‖ +
        ‖PoissonFrequencyDecomposition.omittedSum D Z‖ :=
        (norm_add_le _ _).trans (add_le_add norm_add₃_le le_rfl)
    _ ≤ _ := by nlinarith [a1, a2, a3, a4]

end

end DedekindZetaZeroFree.Quantitative.Compare
