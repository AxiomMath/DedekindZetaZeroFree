module

public import DedekindZetaZeroFree.Eisenstein.Induction.FlatSections.TranslationFlow
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.LieDerivatives.UpperRootFlows

@[expose] public section

noncomputable section
open scoped Classical Topology Matrix Matrix.Norms.Operator
namespace DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension
open KPGlobalResidualConstruction KPCplxPrincipalSeriesCharts KPCplxCharacterHaar KPSmoothActualFlowData
open _root_.DedekindZetaZeroFree.RootDerivatives renaming exp_upper → RootDerivatives.exp_upper
set_option backward.isDefEq.respectTransparency false

def lowerGL (z : ℂ) : ComplexGL2 :=
  Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection (i:=1) (j:=0) (by decide) z)

theorem lowerGL_val (z : ℂ) : (lowerGL z : Matrix (Fin 2) (Fin 2) ℂ)=!![1,0;z,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerGL,Matrix.SpecialLinearGroup.toGL,Matrix.SpecialLinearGroup.transvection_coe,Matrix.transvection]

theorem exp_lower (z : ℂ) : NormedSpace.exp (!![0,0;z,0] : Matrix (Fin 2) (Fin 2) ℂ)=!![1,0;z,1] := by
  have he : (!![0,0;z,0] : Matrix (Fin 2) (Fin 2) ℂ)=(!![0,z;0,0])ᵀ := by ext i j;fin_cases i <;> fin_cases j <;> rfl
  rw [he,Matrix.exp_transpose,RootDerivatives.exp_upper]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem sourceFlow_lower_real (t : ℝ) : sourceFlow (basisMatrix 4) t=lowerGL (t:ℂ) := by
  apply Units.ext
  change NormedSpace.exp ((t:ℂ) • basisMatrix 4)=_
  have hm : (t:ℂ) • basisMatrix 4=(!![0,0;(t:ℂ),0] : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [basisMatrix,sl2Matrix,Matrix.smul_apply,smul_eq_mul]
  rw [hm,exp_lower,lowerGL_val]

theorem sourceFlow_lower_imag (t : ℝ) : sourceFlow (basisMatrix 5) t=lowerGL (Complex.I*(t:ℂ)) := by
  apply Units.ext
  change NormedSpace.exp ((t:ℂ) • basisMatrix 5)=_
  have hm : (t:ℂ) • basisMatrix 5=(!![0,0;Complex.I*(t:ℂ),0] : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [basisMatrix,sl2Matrix,Matrix.smul_apply,smul_eq_mul,mul_comm]
  rw [hm,exp_lower,lowerGL_val]

theorem lowerGL_flow_factor (z : ℂ) :
    lowerGL z=sourceFlow (basisMatrix 4) z.re*sourceFlow (basisMatrix 5) z.im := by
  rw [sourceFlow_lower_real,sourceFlow_lower_imag]
  apply Units.ext
  change (lowerGL z : Matrix (Fin 2) (Fin 2) ℂ)= (lowerGL (z.re:ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * (lowerGL (Complex.I*(z.im:ℂ)) : Matrix (Fin 2) (Fin 2) ℂ)
  simp only [lowerGL_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two]
  exact (Complex.re_add_im z).symm.trans (by ring)
end DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension

end
