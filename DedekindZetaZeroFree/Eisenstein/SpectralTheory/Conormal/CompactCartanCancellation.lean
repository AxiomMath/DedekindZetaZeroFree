module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.BoundaryFlux.AngularConormalDescent
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspGeometry.ConormalFirstJet

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
open scoped Classical NumberField Topology ENNReal NNReal BigOperators Matrix.Norms.Operator
open MeasureTheory
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.IntrinsicFrameSpectral renaming smooth_intrinsic_scalar → smooth_intrinsic_scalar
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes renaming intrinsic_level → intrinsic_level
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes renaming normalRadial_finite_right → normalRadial_finite_right
namespace DedekindZetaZeroFree.KPMsGreenFlux.FramedConormal.NativeShellStokes
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

noncomputable local instance : NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) ℂ) :=
  NormedAlgebra.restrictScalars ℚ ℝ _

set_option maxHeartbeats 1000000
open KPSmoothActualFlowData
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.ConormalFirstJet renaming lift → lift
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.ConormalFirstJet renaming rightDerivative_eq_fderiv → rightDerivative_eq_fderiv
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.ConormalFirstJet renaming exponential_direction_hasDerivAt → exponential_direction_hasDerivAt

 def directionJet (a : LieCoordinates F) (f : Cover F ζ hζ → ℂ) (g : Cover F ζ hζ) : ℂ :=
  ∑ w : NumberField.InfinitePlace F, ∑ i : Fin 6, (a (w,i) : ℂ) * rightDerivative F ζ hζ w i f g

private theorem direction_sum (a : LieCoordinates F) :
    a = ∑ w : NumberField.InfinitePlace F, ∑ i : Fin 6, a (w,i) • Pi.single (w,i) 1 := by
  funext b
  rcases b with ⟨w,i⟩
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, Prod.mk.injEq, ite_and]

private theorem direction_hasDerivAt_zero (f : Cover F ζ hζ → ℂ) (hf : Smooth F ζ hζ f)
    (g : Cover F ζ hζ) (a : LieCoordinates F) :
    HasDerivAt (fun t : ℝ => f (g * archimedeanInsertion F ζ hζ (exponential F (t • a))))
      (directionJet a f g) 0 := by
  have hj : fderiv ℝ (lift f g) 0 a = directionJet a f g := by
    conv_lhs => rw [direction_sum a]
    simp only [map_sum, map_smul, rightDerivative_eq_fderiv f hf, Complex.real_smul, directionJet]
  simpa only [lift, hj] using exponential_direction_hasDerivAt f hf g a

 theorem direction_hasDerivAt (f : Cover F ζ hζ → ℂ) (hf : Smooth F ζ hζ f)
    (g : Cover F ζ hζ) (a : LieCoordinates F) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (g * archimedeanInsertion F ζ hζ (exponential F (s • a))))
      (directionJet a f (g * archimedeanInsertion F ζ hζ (exponential F (t • a)))) t := by
  let y := g * archimedeanInsertion F ζ hζ (exponential F (t • a))
  have hd : HasDerivAt (fun s : ℝ => f (y * archimedeanInsertion F ζ hζ (exponential F (s • a))))
      (directionJet a f y) (t-t) := by
    rw [sub_self]
    exact direction_hasDerivAt_zero f hf y a
  convert hd.comp_sub_const t t using 1
  funext s
  dsimp [y]
  have he (s t : ℝ) : exponential F ((s+t) • a) = exponential F (s • a) * exponential F (t • a) :=
    PGLComplex.productExponential_add_ray _ a s t
  rw [mul_assoc, ← (archimedean_insertion_properties F ζ hζ).2.1, ← he, add_sub_cancel]

 def compactCoefficients : Fin 3 → Fin 6 → ℝ
  | 0 => ![0,1,0,0,0,0]
  | 1 => ![0,0,1,0,-1,0]
  | 2 => ![0,0,0,1,0,1]

 def compactDirection (w : NumberField.InfinitePlace F) (j : Fin 3) : LieCoordinates F :=
  fun b => if b.1 = w then compactCoefficients j b.2 else 0

private theorem compact_direction_matrix_skew (j : Fin 3) :
    star (sl2Matrix (compactCoefficients j)) = -sl2Matrix (compactCoefficients j) := by
  fin_cases j <;> ext i k <;> fin_cases i <;> fin_cases k <;>
    simp [compactCoefficients, sl2Matrix]

open _root_.DedekindZetaZeroFree.KPMsGreenFlux.NormalCoefficient renaming matrix_path_components → matrix_path_components

private theorem compact_exp_components (M : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) (i j : Fin 2) :
    HasDerivAt (fun u : ℝ => (NormedSpace.exp ((u : ℂ) • M)) i j)
      ((NormedSpace.exp ((t : ℂ) • M) * M) i j) t := by
  letI : NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) ℂ) := NormedAlgebra.restrictScalars ℚ ℝ _
  have hd : HasDerivAt (fun u : ℝ => (NormedSpace.exp ((t : ℂ) • M) * NormedSpace.exp ((u : ℂ) • M)) i j)
      ((NormedSpace.exp ((t : ℂ) • M) * M) i j) (t-t) := by
    simpa only [sub_self] using matrix_path_components (NormedSpace.exp ((t : ℂ) • M)) M i j
  have hd' := hd.comp_sub_const t t
  convert hd' using 1
  funext u
  have he : (u : ℂ) • M = (t : ℂ) • M + ((u-t : ℝ) : ℂ) • M := by
    rw [← add_smul]
    congr 1
    push_cast
    ring
  rw [he, NormedSpace.exp_add_of_commute ((Commute.refl M).smul_left (t : ℂ) |>.smul_right ((u-t : ℝ) : ℂ))]

private theorem exp_trace_zero_det (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : M 0 0 + M 1 1 = 0) (t : ℝ) :
    (NormedSpace.exp ((t : ℂ) • M)).det = 1 := by
  let m := fun u : ℝ => NormedSpace.exp ((u : ℂ) • M)
  have hd (u : ℝ) : HasDerivAt (fun u => (m u).det) 0 u := by
    convert ((compact_exp_components M u 0 0).mul (compact_exp_components M u 1 1)).sub
      ((compact_exp_components M u 0 1).mul (compact_exp_components M u 1 0)) using 1
    · funext u; simp [m, Matrix.det_fin_two]
    · simp only [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination -((m u 0 0 * m u 1 1 - m u 0 1 * m u 1 0)) * hM
  have hc := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt) (fun u => (hd u).deriv) t 0
  simpa [m] using hc

 theorem compact_direction_exp_specialUnitary (j : Fin 3) (t : ℝ) :
    (matrixExponential ((t : ℂ) • sl2Matrix (compactCoefficients j))).val ∈
      Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  letI : NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) ℂ) := NormedAlgebra.restrictScalars ℚ ℝ _
  apply Matrix.mem_specialUnitaryGroup_iff.mpr
  constructor
  · apply Matrix.mem_unitaryGroup_iff.mpr
    exact Unitary.mem_iff.mp (NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
      (𝔸 := Matrix (Fin 2) (Fin 2) ℂ) (x := (t : ℂ) • sl2Matrix (compactCoefficients j)) (by
        rw [skewAdjoint.mem_iff]
        simp [compact_direction_matrix_skew])) |>.2
  · exact exp_trace_zero_det _ (by simp [sl2Matrix]) t

 def compactDirectionCurve (w : NumberField.InfinitePlace F) (j : Fin 3) (t : ℝ) : K F := fun v =>
  if v = w then
    ⟨Matrix.ProjGenLinGroup.mk (matrixExponential ((t : ℂ) • sl2Matrix (compactCoefficients j))), by
      let s : KPCplxCharacterHaar.ComplexSU2 := ⟨_, compact_direction_exp_specialUnitary j t⟩
      refine ⟨s, ?_⟩
      change Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding s) = _
      apply congrArg Matrix.ProjGenLinGroup.mk
      apply Units.ext
      rfl⟩
  else 1

private theorem compact_direction_curve_coe (w : NumberField.InfinitePlace F) (j : Fin 3) (t : ℝ) :
    (fun v => (compactDirectionCurve (F := F) w j t v).val) =
      exponential F (t • compactDirection w j) := by
  ext v
  by_cases hv : v = w
  · subst v
    simp [compactDirectionCurve, exponential, compactDirection, sl2Matrix,
      Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, Complex.ofReal_mul]
    congr 2
    ext i k
    fin_cases i <;> fin_cases k <;> simp <;> ring
  · simp only [compactDirectionCurve, hv, if_false, Subgroup.coe_one, exponential,
      compactDirection, Pi.smul_apply, smul_eq_mul, mul_zero, sl2Matrix]
    simp only [Complex.ofReal_zero, mul_zero, add_zero, neg_zero]
    have hz : (!![0, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by ext i k; fin_cases i <;> fin_cases k <;> rfl
    rw [hz]
    have he : matrixExponential (0 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
      apply Units.ext
      exact NormedSpace.exp_zero
    rw [he, map_one]

 theorem compact_direction_curve_insertion (w : NumberField.InfinitePlace F) (j : Fin 3) (t : ℝ) :
    compactInsertion F ζ hζ (compactDirectionCurve w j t) =
      archimedeanInsertion F ζ hζ (exponential F (t • compactDirection w j)) := by
  rw [← compact_direction_curve_coe]
  rfl

end DedekindZetaZeroFree.KPMsGreenFlux.FramedConormal.NativeShellStokes

end
