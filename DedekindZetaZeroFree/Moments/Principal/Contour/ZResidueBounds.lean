module

public import DedekindZetaZeroFree.Moments.Principal.Contour.WShift
public import DedekindZetaZeroFree.Moments.Principal.Contour.ResidueIntegrability

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.PrincipalZShiftAux

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.PoissonKernel DedekindZetaZeroFree.Quantitative.PrincipalWShift
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def zResidue (u : D.Row) (ξ : ℂ) (Z : ℝ) : ℂ :=
  Filter.limUnder (nhdsWithin (1 / 6 : ℂ) {1 / 6}ᶜ)
    (fun z : ℂ => (z - 1 / 6) * wResidue D u ξ z Z)

theorem cvi_sub_aux (σ : ℝ) (f g : ℂ → ℂ)
    (hf : MeasureTheory.Integrable (fun t : ℝ => f ((σ : ℂ) + (t : ℂ) * Complex.I)))
    (hg : MeasureTheory.Integrable (fun t : ℝ => g ((σ : ℂ) + (t : ℂ) * Complex.I))) :
    comparisonVerticalIntegral σ f - comparisonVerticalIntegral σ g =
      comparisonVerticalIntegral σ (fun z => f z - g z) := by
  unfold comparisonVerticalIntegral
  rw [← mul_sub, ← MeasureTheory.integral_sub hf hg]

theorem principalRows_eq_single :
    principalRows D = {ActualRowCount.principalRow D} := by
  ext r
  simp only [principalRows, Set.mem_setOf_eq, Set.mem_singleton_iff]
  exact ⟨fun h => ActualRowCount.eq_principalRow D h,
    fun h => by rw [h]; exact ActualRowCount.principalRow_u D⟩

theorem Jwres_sub_Rz (Z : ℝ) (hZ : 2 ≤ Z) :
    Jwres D Z -
        ∑ᶠ u ∈ principalRows D, comparisonVerticalIntegral Scales.rightLine (fun ξ =>
          comparisonVerticalIntegral (1 / 20) (fun z => wResidue D u ξ z Z)) =
      ∑ᶠ u ∈ principalRows D, comparisonVerticalIntegral Scales.rightLine (fun ξ => zResidue D u ξ Z) := by
  classical
  have hset := principalRows_eq_single D
  have hu : (ActualRowCount.principalRow D).u = (1 : ↥D.recipe.A.R) :=
    ActualRowCount.principalRow_u D
  obtain ⟨_, _, hw⟩ := PrincipalResidueIntegrability.residue_integrability_w D
    (ActualRowCount.principalRow D) hu
  obtain ⟨_, _, hz⟩ := PrincipalResidueIntegrability.residue_integrability_z D
    (ActualRowCount.principalRow D) hu
  have hWi := (hw Z hZ).2.2.1
  have hZi := (hz Z hZ).2.2.1
  have hpt : ∀ t : ℝ,
      comparisonVerticalIntegral (1 / 6 + Scales.contourOffset) (fun z =>
          wResidue D (ActualRowCount.principalRow D) ((Scales.rightLine : ℂ) + (t : ℂ) * Complex.I) z Z) -
        comparisonVerticalIntegral (1 / 20) (fun z =>
          wResidue D (ActualRowCount.principalRow D) ((Scales.rightLine : ℂ) + (t : ℂ) * Complex.I) z Z) =
      zResidue D (ActualRowCount.principalRow D) ((Scales.rightLine : ℂ) + (t : ℂ) * Complex.I) Z :=
    fun t => PrincipalContourDeformation.wResidue_z_shift_across D _ hu Z hZ t
  unfold Jwres
  simp only [hset, finsum_mem_singleton]
  have hsub := PrincipalZShiftAux.cvi_sub_aux Scales.rightLine
    (fun ξ => comparisonVerticalIntegral (1 / 6 + Scales.contourOffset) (fun z =>
      wResidue D (ActualRowCount.principalRow D) ξ z Z))
    (fun ξ => comparisonVerticalIntegral (1 / 20) (fun z =>
      wResidue D (ActualRowCount.principalRow D) ξ z Z)) hWi hZi
  rw [hsub]
  unfold comparisonVerticalIntegral
  congr 1
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  exact hpt t

theorem zResidue_sum_eq (Z : ℝ) (hZ : 2 ≤ Z) :
    ∑ᶠ u ∈ principalRows D, comparisonVerticalIntegral Scales.rightLine (fun ξ => zResidue D u ξ Z) =
      Spectral.c₀ D * Spectral.f D Z := by
  have hset : principalRows D = {ActualRowCount.principalRow D} := by
    ext r
    simp only [principalRows, Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact ⟨fun h => ActualRowCount.eq_principalRow D h,
      fun h => by rw [h]; exact ActualRowCount.principalRow_u D⟩
  rw [hset, finsum_mem_singleton]
  exact PrincipalContourDeformation.zResidue_xi_shift (D := D) (u := ActualRowCount.principalRow D)
    (hu := ActualRowCount.principalRow_u D) (Z := Z) (hZ := hZ)

theorem Rz_integral_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 2 ≤ Z →
      ‖∑ᶠ u ∈ principalRows D, comparisonVerticalIntegral Scales.rightLine (fun ξ =>
          comparisonVerticalIntegral (1 / 20) (fun z => wResidue D u ξ z Z))‖ ≤
        C * Z ^ (Scales.mainExponent - 384999 / 10000000) := by
  classical
  have hset := principalRows_eq_single D
  have hu : (ActualRowCount.principalRow D).u = (1 : ↥D.recipe.A.R) :=
    ActualRowCount.principalRow_u D
  obtain ⟨C, hC, h⟩ := PrincipalResidueIntegrability.residue_integrability_z D
    (ActualRowCount.principalRow D) hu
  have hE : Scales.kernelExponent Scales.rightLine 1 (1 / 20) = Scales.mainExponent - 384999 / 10000000 := by
    unfold Scales.kernelExponent Scales.rightLine Scales.contourOffset Scales.xExponent Scales.smoothingExponent Scales.yExponent Scales.mainExponent
    norm_num
  refine ⟨C, hC, fun Z hZ => ?_⟩
  have hb := (h Z hZ).2.2.2
  rw [hset, finsum_mem_singleton, ← hE]
  exact hb

end

end DedekindZetaZeroFree.Quantitative.PrincipalZShiftAux
