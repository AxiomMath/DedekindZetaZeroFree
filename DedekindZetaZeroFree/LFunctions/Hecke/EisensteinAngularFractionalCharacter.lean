module

public import DedekindZetaZeroFree.Arithmetic.Ideals.EisensteinIntegers.PrimaryGenerators
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Topology.Algebra.Group.Units

@[expose] public section

namespace DedekindZetaZeroFree.Eisenstein

theorem angular_mem_circle (z : ℂˣ) :
    z.val / (‖z.val‖ : ℂ) ∈ Metric.sphere (0 : ℂ) 1 := by
  rw [Metric.mem_sphere, dist_zero_right, norm_div,
    Complex.norm_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.mpr z.ne_zero)]

theorem angular_unit_mul (z w : ℂˣ) :
    (z * w).val / (‖(z * w).val‖ : ℂ) =
      (z.val / (‖z.val‖ : ℂ)) * (w.val / (‖w.val‖ : ℂ)) := by
  simp only [Units.val_mul, norm_mul, Complex.ofReal_mul]
  exact (div_mul_div_comm _ _ _ _).symm

noncomputable def archimedeanAngular : ℂˣ →* Circle where
  toFun z := ⟨z.val / (‖z.val‖ : ℂ), angular_mem_circle z⟩
  map_one' := Circle.ext (by simp)
  map_mul' z w := Circle.ext (angular_unit_mul z w)

@[simp] theorem archimedeanAngular_apply (z : ℂˣ) :
    (archimedeanAngular z : ℂ) = z.val / (‖z.val‖ : ℂ) := rfl

theorem continuous_archimedeanAngular : Continuous archimedeanAngular := by
  apply Continuous.subtype_mk
  exact Units.continuous_val.div (Complex.continuous_ofReal.comp Units.continuous_val.norm)
    (fun z => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr z.ne_zero))

end DedekindZetaZeroFree.Eisenstein
