module

public import DedekindZetaZeroFree.HarmonicAnalysis.Schwartz.LatticeDecay
public import DedekindZetaZeroFree.Theta.Profiles.FractionalIdealShapeLattice

@[expose] public section

noncomputable section

open Module MeasureTheory Set
open scoped FourierTransform RealInnerProductSpace

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι]

theorem continuous_intPeriodization_coordinateSchwartz (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (b : Basis ι ℤ L)
    (f : SchwartzMap E ℂ) :
    Continuous (intPeriodization
      (fun x => f ((b.ofZLatticeBasis ℝ L).equivFun.symm x))) := by
  classical
  have hF : Summable (coordinateSchwartzTranslate L b f) := by
    apply ContinuousMap.summable_of_locally_summable_norm
    intro K
    exact schwartzLatticeDecay_coordinates L b f K
  have hcont : Continuous (fun x : ι → ℝ =>
      (∑' n, coordinateSchwartzTranslate L b f n) x) :=
    (∑' n, coordinateSchwartzTranslate L b f n).continuous
  have heval (x : ι → ℝ) :
      (∑' n, coordinateSchwartzTranslate L b f n) x =
        intPeriodization
          (fun x => f ((b.ofZLatticeBasis ℝ L).equivFun.symm x)) x := by
    rw [← ContinuousMap.tsum_apply hF x]
    rfl
  rw [show intPeriodization
        (fun x => f ((b.ofZLatticeBasis ℝ L).equivFun.symm x)) =
      fun x => (∑' n, coordinateSchwartzTranslate L b f n) x from
    funext fun x => (heval x).symm]
  exact hcont

def schwartzTorusPeriodization (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (b : Basis ι ℤ L)
    (f : SchwartzMap E ℂ) : C(UnitAddTorus ι, ℂ) :=
  torusPeriodization
    (fun x => f ((b.ofZLatticeBasis ℝ L).equivFun.symm x))
    (continuous_intPeriodization_coordinateSchwartz L b f)

@[simp] theorem schwartzTorusPeriodization_apply_quotient (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (b : Basis ι ℤ L)
    (f : SchwartzMap E ℂ) (x : ι → ℝ) :
    schwartzTorusPeriodization L b f (torusQuotientMap x) =
      ∑' k : ι → ℤ,
        f ((b.ofZLatticeBasis ℝ L).equivFun.symm
          (x + fun i => (k i : ℝ))) := by
  exact torusPeriodization_apply_quotient _ _ x

noncomputable def coordinateFourierSchwartz (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (b : Basis ι ℤ L)
    (f : SchwartzMap E ℂ) (n : ι → ℤ) (x : ι → ℝ) : ℂ :=
  coordinateFourierCharacter n x *
    f ((b.ofZLatticeBasis ℝ L).equivFun.symm x)

noncomputable def coordinateFourierSchwartzTranslate
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (f : SchwartzMap E ℂ) (n k : ι → ℤ)
    (x : ι → ℝ) : ℂ :=
  coordinateFourierCharacter n x *
    f ((b.ofZLatticeBasis ℝ L).equivFun.symm
      (x + fun i => (k i : ℝ)))

noncomputable def ambientFourierSchwartz (f : SchwartzMap E ℂ)
    (w y : E) : ℂ :=
  𝐞 (-(inner ℝ y w)) • f y

private theorem continuous_coordinateFourierCharacter (n : ι → ℤ) :
    Continuous (coordinateFourierCharacter n) := by
  unfold coordinateFourierCharacter
  exact (UnitAddTorus.mFourier (-n)).continuous.comp
    (continuous_pi fun i =>
      continuous_quotient_mk'.comp (continuous_apply i))

private theorem coordinateFourierCharacter_add_intPi
    (n k : ι → ℤ) (x : ι → ℝ) :
    coordinateFourierCharacter n ((fun i => (k i : ℝ)) + x) =
      coordinateFourierCharacter n x := by
  unfold coordinateFourierCharacter
  congr 1
  rw [add_comm]
  exact torusQuotientMap_add_intPi x k

private theorem continuous_coordinateFourierSchwartz
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (f : SchwartzMap E ℂ) (n : ι → ℤ) :
    Continuous (coordinateFourierSchwartz L b f n) := by
  unfold coordinateFourierSchwartz
  exact (continuous_coordinateFourierCharacter n).mul
    (f.continuous.comp (LinearEquiv.toContinuousLinearEquiv
      (b.ofZLatticeBasis ℝ L).equivFun.symm).continuous)

private theorem continuous_coordinateFourierSchwartzTranslate
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (f : SchwartzMap E ℂ) (n k : ι → ℤ) :
    Continuous (coordinateFourierSchwartzTranslate L b f n k) := by
  unfold coordinateFourierSchwartzTranslate
  refine (continuous_coordinateFourierCharacter n).mul ?_
  exact f.continuous.comp
    ((LinearEquiv.toContinuousLinearEquiv
      (b.ofZLatticeBasis ℝ L).equivFun.symm).continuous.comp
        (continuous_id.add continuous_const))

private theorem coordinateFourierSchwartz_add_intPi
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (f : SchwartzMap E ℂ) (n k : ι → ℤ) (x : ι → ℝ) :
    coordinateFourierSchwartz L b f n ((fun i => (k i : ℝ)) + x) =
      coordinateFourierSchwartzTranslate L b f n k x := by
  rw [coordinateFourierSchwartz, coordinateFourierSchwartzTranslate,
    coordinateFourierCharacter_add_intPi]
  congr 1
  rw [add_comm]

private theorem coordinateFourierSchwartz_eq_ambient [DecidableEq ι]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (f : SchwartzMap E ℂ) (n : ι → ℤ) (x : ι → ℝ) :
    coordinateFourierSchwartz L b f n x =
      ambientFourierSchwartz f (dualLatticePoint L b n)
        ((b.ofZLatticeBasis ℝ L).equivFun.symm x) := by
  rw [coordinateFourierSchwartz, ambientFourierSchwartz,
    coordinateFourierCharacter, mFourier_neg_torusQuotientMap,
    real_inner_comm,
    inner_dualLatticePoint_ofZLatticeBasis_equivFun_symm]
  simp only [Circle.smul_def, Real.fourierChar_apply]
  push_cast
  ring_nf

private theorem integrable_coordinateFourierSchwartz
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (f : SchwartzMap E ℂ) (n : ι → ℤ) :
    Integrable (coordinateFourierSchwartz L b f n) := by
  have hbase : Integrable (fun x : ι → ℝ =>
      f ((b.ofZLatticeBasis ℝ L).equivFun.symm x)) :=
    integrable_comp_ofZLatticeBasis_equivFun_symm L b f.integrable
  refine hbase.congr'
    (continuous_coordinateFourierSchwartz L b f n).aestronglyMeasurable ?_
  filter_upwards with x
  rw [coordinateFourierSchwartz, norm_mul, norm_coordinateFourierCharacter,
    one_mul]

private theorem summable_integral_norm_coordinateFourierSchwartzTranslate
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (f : SchwartzMap E ℂ) (n : ι → ℤ) :
    Summable (fun k : ι → ℤ =>
      ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Ioc 0 1},
        ‖coordinateFourierSchwartzTranslate L b f n k x‖) := by
  classical
  let S : Set (ι → ℝ) := {x | ∀ i, x i ∈ Ioc 0 1}
  let K : TopologicalSpace.Compacts (ι → ℝ) :=
    ⟨Icc (0 : ι → ℝ) 1, isCompact_Icc⟩
  have hSK : S ⊆ K := fun x hx =>
    ⟨fun i => (hx i).1.le, fun i => (hx i).2⟩
  have hS : MeasurableSet S := measurableSet_pi_Ioc
  have hKsum := schwartzLatticeDecay_coordinates L b f K
  have hmeasure : volume S < (⊤ : ENNReal) :=
    lt_of_le_of_lt (measure_mono hSK) K.2.measure_lt_top
  have hbound (k : ι → ℤ) :
      ∫ x in S, ‖coordinateFourierSchwartzTranslate L b f n k x‖ ≤
        volume.real S *
          ‖(coordinateSchwartzTranslate L b f k).restrict K‖ := by
    have hInt : IntegrableOn
        (fun x => ‖coordinateFourierSchwartzTranslate L b f n k x‖) S :=
      ((continuous_coordinateFourierSchwartzTranslate L b f n k).norm.integrableOn_Icc).mono_set hSK
    have hConst : IntegrableOn (fun _ : ι → ℝ =>
        ‖(coordinateSchwartzTranslate L b f k).restrict K‖) S :=
      integrableOn_const (ne_of_lt hmeasure)
    calc
      ∫ x in S, ‖coordinateFourierSchwartzTranslate L b f n k x‖ ≤
          ∫ _x in S,
            ‖(coordinateSchwartzTranslate L b f k).restrict K‖ := by
        apply integral_mono_ae hInt hConst
        filter_upwards [ae_restrict_mem hS] with x hx
        rw [coordinateFourierSchwartzTranslate, norm_mul,
          norm_coordinateFourierCharacter, one_mul]
        exact ContinuousMap.norm_coe_le_norm
          ((coordinateSchwartzTranslate L b f k).restrict K) ⟨x, hSK hx⟩
      _ = volume.real S *
          ‖(coordinateSchwartzTranslate L b f k).restrict K‖ := by simp
  apply Summable.of_nonneg_of_le
      (fun _ => integral_nonneg fun _ => norm_nonneg _) hbound
  exact hKsum.mul_left (volume.real S)

private theorem integral_tsum_coordinateFourierSchwartzTranslate
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (f : SchwartzMap E ℂ) (n : ι → ℤ) :
    ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Ioc 0 1},
        ∑' k : ι → ℤ, coordinateFourierSchwartzTranslate L b f n k x =
      ∑' k : ι → ℤ,
        ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Ioc 0 1},
          coordinateFourierSchwartzTranslate L b f n k x := by
  classical
  symm
  apply integral_tsum_of_summable_integral_norm
  · intro k
    let S : Set (ι → ℝ) := {x | ∀ i, x i ∈ Ioc 0 1}
    let K : Set (ι → ℝ) := Icc 0 1
    have hSK : S ⊆ K := fun x hx =>
      ⟨fun i => (hx i).1.le, fun i => (hx i).2⟩
    exact ((continuous_coordinateFourierSchwartzTranslate L b f n k).integrableOn_Icc).mono_set hSK
  · exact summable_integral_norm_coordinateFourierSchwartzTranslate L b f n

private theorem integral_ambientFourierSchwartz (f : SchwartzMap E ℂ)
    (w : E) :
    (∫ y : E, ambientFourierSchwartz f w y) =
      (FourierTransform.fourier f) w := by
  rw [show (FourierTransform.fourier f) w = 𝓕 (f : E → ℂ) w from rfl,
    Real.fourier_eq]
  rfl

private theorem toNNReal_inv_smul (c : ℝ) (hc : 0 < c) (z : ℂ) :
    (Real.toNNReal c)⁻¹ • z = (c : ℂ)⁻¹ * z := by
  rw [NNReal.smul_def, Complex.real_smul]
  congr 1
  rw [NNReal.coe_inv, Real.coe_toNNReal _ (le_of_lt hc), Complex.ofReal_inv]

private theorem integral_coordinateFourierSchwartz [DecidableEq ι]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (f : SchwartzMap E ℂ) (n : ι → ℤ) :
    (∫ x : ι → ℝ, coordinateFourierSchwartz L b f n x) =
      (ZLattice.covolume L : ℂ)⁻¹ *
        (FourierTransform.fourier f) (dualLatticePoint L b n) := by
  have hfun : (fun x : ι → ℝ => coordinateFourierSchwartz L b f n x) =
      fun x => ambientFourierSchwartz f (dualLatticePoint L b n)
        ((b.ofZLatticeBasis ℝ L).equivFun.symm x) := by
    funext x
    exact coordinateFourierSchwartz_eq_ambient L b f n x
  rw [hfun, integral_comp_ofZLatticeBasis_equivFun_symm L b
      (fun y => ambientFourierSchwartz f (dualLatticePoint L b n) y),
    integral_ambientFourierSchwartz f (dualLatticePoint L b n)]
  exact toNNReal_inv_smul (ZLattice.covolume L volume) (ZLattice.covolume_pos L volume) _

theorem mFourierCoeff_schwartzTorusPeriodization (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] [DecidableEq ι]
    (b : Basis ι ℤ L) (f : SchwartzMap E ℂ) (n : ι → ℤ) :
    UnitAddTorus.mFourierCoeff (schwartzTorusPeriodization L b f) n =
      (ZLattice.covolume L : ℂ)⁻¹ *
        (FourierTransform.fourier f) (dualLatticePoint L b n) := by
  classical
  rw [UnitAddTorus.mFourierCoeff_eq_integral _ n 0]
  simp only [Pi.zero_apply, zero_add]
  have hpoint (x : ι → ℝ) :
      UnitAddTorus.mFourier (-n) (fun i => (x i : UnitAddCircle)) •
          schwartzTorusPeriodization L b f (fun i => (x i : UnitAddCircle)) =
        ∑' k : ι → ℤ, coordinateFourierSchwartzTranslate L b f n k x := by
    rw [schwartzTorusPeriodization, show (fun i => (x i : UnitAddCircle)) = torusQuotientMap x from rfl,
      torusPeriodization_apply_quotient]
    unfold intPeriodization coordinateFourierSchwartzTranslate
      coordinateFourierCharacter
    rw [smul_eq_mul, tsum_mul_left]
  simp_rw [hpoint]
  rw [integral_tsum_coordinateFourierSchwartzTranslate L b f n,
    ← integral_coordinateFourierSchwartz L b f n,
    integral_eq_tsum_integral_pi_Ioc (coordinateFourierSchwartz L b f n)
      (integrable_coordinateFourierSchwartz L b f n)]
  apply tsum_congr
  intro k
  apply setIntegral_congr_fun measurableSet_pi_Ioc
  intro x hx
  exact (coordinateFourierSchwartz_add_intPi L b f n k x).symm

end DedekindZetaZeroFree.AbelianQuotient.Theta

end
