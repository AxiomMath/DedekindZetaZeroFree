module

public import DedekindZetaZeroFree.Eisenstein.Induction.FlatSections.SmoothFlowDifferences

@[expose] public section

noncomputable section
open scoped Classical Topology Matrix.Norms.Operator
namespace DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension
open KPGlobalResidualConstruction KPCplxPrincipalSeriesCharts KPCplxCharacterHaar
set_option backward.isDefEq.respectTransparency false

def sourceFlow (X : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) : ComplexGL2 :=
  KPSmoothActualFlowData.matrixExponential ((t:ℂ) • X)

theorem sourceFlow_zero (X : Matrix (Fin 2) (Fin 2) ℂ) : sourceFlow X 0=1 := by
  apply Units.ext
  simp [sourceFlow,KPSmoothActualFlowData.matrixExponential]

theorem sourceFlow_add (X : Matrix (Fin 2) (Fin 2) ℂ) (r t : ℝ) :
    sourceFlow X (r+t)=sourceFlow X r*sourceFlow X t := by
  apply Units.ext
  change NormedSpace.exp (((r+t:ℝ):ℂ) • X)=NormedSpace.exp ((r:ℂ) • X)*NormedSpace.exp ((t:ℂ) • X)
  rw [Complex.ofReal_add,add_smul]
  exact NormedSpace.exp_add_of_commute (((Commute.refl X).smul_left (r:ℂ)).smul_right (t:ℂ))

theorem sourceTranslate_add (s : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) (r t : ℝ) (v : PrincipalSeries s) :
    KPCplxPrincipalSeriesCharts.rightTranslate s (sourceFlow X r)
      (KPCplxPrincipalSeriesCharts.rightTranslate s (sourceFlow X t) v)=
    KPCplxPrincipalSeriesCharts.rightTranslate s (sourceFlow X (r+t)) v := by
  apply Subtype.ext
  funext g
  simp only [KPCplxPrincipalSeriesCharts.rightTranslate,sourceFlow_add,mul_assoc]

theorem sourceDerivative_neg (s : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) (v : PrincipalSeries s) :
    NativeComplexHCOperators.derivative s (-X) v = -NativeComplexHCOperators.derivative s X v := by
  apply Subtype.ext
  funext g
  have hd := NativeComplexHCOperators.hasDerivAt_flow s X v g
  rw [←neg_zero] at hd
  have h := hd.scomp 0 (show HasDerivAt (fun t : ℝ=> -t) (-1) 0 from (hasDerivAt_id (0:ℝ)).neg)
  have he : (fun t : ℝ=>v (g*KPSmoothActualFlowData.matrixExponential (((-t):ℂ) • X)))=
      fun t : ℝ=>v (g*KPSmoothActualFlowData.matrixExponential ((t:ℂ) • (-X))) := by
    funext t
    simp only [Complex.ofReal_neg,neg_smul,smul_neg]
  simp only [Function.comp_def,Complex.ofReal_neg] at h
  rw [he] at h
  have H := (NativeComplexHCOperators.hasDerivAt_flow s (-X) v g).unique h
  simpa using H

theorem sourceFlow_neg (X : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) :
    sourceFlow (-X) t=sourceFlow X (-t) := by
  simp only [sourceFlow,Complex.ofReal_neg,neg_smul,smul_neg]

theorem sourceTranslate_inverse (s : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) (v : PrincipalSeries s) :
    KPCplxPrincipalSeriesCharts.rightTranslate s (sourceFlow (-X) t)
      (KPCplxPrincipalSeriesCharts.rightTranslate s (sourceFlow X t) v)=v := by
  rw [sourceFlow_neg,sourceTranslate_add,neg_add_cancel,sourceFlow_zero]
  apply Subtype.ext
  funext g
  simp only [KPCplxPrincipalSeriesCharts.rightTranslate,mul_one]
end DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension

end
