module

public import DedekindZetaZeroFree.Adeles.Quotients.CuspShells.LevelTransport
public import DedekindZetaZeroFree.Adeles.Quotients.CuspShells.AngularTestCoefficient

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology NNReal ENNReal BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.KPMsNativeOffsetMass
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem fullShell_cutoff_and_cofinal_independent
    (S : NativeRecipe F ζ hζ R P)
    (V W : KPMsActualAngularSource.Level F ζ hζ) (Y Z : ℝ)
    (hV : OffsetAdmissible F ζ hζ R P S V Y)
    (hW : OffsetAdmissible F ζ hζ R P S W Z) :
    fullShell F ζ hζ R P S V Y = fullShell F ζ hζ R P S W Z := by
  have hmono (U : KPMsActualAngularSource.Level F ζ hζ) (A B : ℝ)
      (hA : OffsetAdmissible F ζ hζ R P S U A) (hAB : A ≤ B) :
      OffsetAdmissible F ζ hζ R P S U B := by
    intro j
    have hcut : A / (cuspOffset F ζ hζ R P S U j).val ≤
        B / (cuspOffset F ζ hζ R P S U j).val :=
      div_le_div_of_nonneg_right hAB (cuspOffset F ζ hζ R P S U j).property.le
    refine ⟨lt_of_lt_of_le (hA j).1 hcut, (hA j).2.trans ?_⟩
    unfold KPMsFixedHaarDisintegration.logHeight
    exact div_le_div_of_nonneg_right (Real.log_le_log (hA j).1 hcut) (by positivity)
  have hsame (U : KPMsActualAngularSource.Level F ζ hζ) (A B : ℝ)
      (hA : OffsetAdmissible F ζ hζ R P S U A)
      (hB : OffsetAdmissible F ζ hζ R P S U B) :
      fullShell F ζ hζ R P S U A = fullShell F ζ hζ R P S U B := by
    apply Measure.ext_of_lintegral
    intro φ hφ
    obtain ⟨a, ha⟩ := fullShell_test_coefficient F ζ hζ R P S U φ hφ
    exact (ha A hA).trans (ha B hB).symm
  have hVT := hmono V Y (max Y Z) hV (le_max_left Y Z)
  have hWT := hmono W Z (max Y Z) hW (le_max_right Y Z)
  exact (hsame V Y (max Y Z) hV hVT).trans
    ((fullShell_cofinal_independent F ζ hζ R P S V W (max Y Z) hVT hWT).trans
      (hsame W (max Y Z) Z hWT hW))

end DedekindZetaZeroFree.KPMsNativeOffsetMass

end
