module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Mathlib.Analysis.Fourier.AddCircleMulti

@[expose] public section

noncomputable section
open scoped Classical FourierTransform
open Module
namespace DedekindZetaZeroFree.PoissonArch

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem innerₗ_nondegenerate : (innerₗ V).Nondegenerate := by
  constructor
  · intro x hx
    exact inner_self_eq_zero.mp (hx x)
  · intro x hx
    exact inner_self_eq_zero.mp (hx x)

def dualLattice {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (L : Submodule ℤ V) : Submodule ℤ V :=
  LinearMap.BilinForm.dualSubmodule (innerₗ V) L

variable {V}

theorem dualLattice_span [FiniteDimensional ℝ V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type*} [Finite ι] (b : Basis ι ℤ L) :
    dualLattice L = Submodule.span ℤ (Set.range
      (LinearMap.BilinForm.dualBasis (innerₗ V) (innerₗ_nondegenerate V)
        (b.ofZLatticeBasis ℝ L))) := by
  classical
  unfold dualLattice
  conv_lhs => rw [← b.ofZLatticeBasis_span ℝ]
  exact LinearMap.BilinForm.dualSubmodule_span_of_basis _ (innerₗ_nondegenerate V) _

instance dualLattice_discreteTopology [FiniteDimensional ℝ V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] :
    DiscreteTopology (dualLattice L) := by
  letI := ZLattice.module_free ℝ L
  letI := ZLattice.module_finite ℝ L
  rw [dualLattice_span L (Module.Free.chooseBasis ℤ L)]
  infer_instance

instance dualLattice_isZLattice [FiniteDimensional ℝ V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] :
    IsZLattice ℝ (dualLattice L) := by
  letI := ZLattice.module_free ℝ L
  letI := ZLattice.module_finite ℝ L
  constructor
  rw [dualLattice_span L (Module.Free.chooseBasis ℤ L)]
  exact ZSpan.span_top _

variable [FiniteDimensional ℝ V]
variable (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
variable {ι : Type*} [Fintype ι] (b : Basis ι ℤ L)

theorem dualLattice_eq_span_dualBasis :
    dualLattice L = Submodule.span ℤ (Set.range
      (LinearMap.BilinForm.dualBasis (innerₗ V) (innerₗ_nondegenerate V) (b.ofZLatticeBasis ℝ L))) := by
  exact dualLattice_span L b

def dualVector_b : (ι → ℤ) ≃+ dualLattice L :=
  AddEquiv.ofBijective
    ({ toFun := fun n => ⟨∑ i, (n i : ℝ) •
          LinearMap.BilinForm.dualBasis (innerₗ V) (innerₗ_nondegenerate V) (b.ofZLatticeBasis ℝ L) i,
          by
            rw [dualLattice_eq_span_dualBasis L b]
            apply Submodule.sum_mem
            intro i _
            rw [Int.cast_smul_eq_zsmul]
            exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)⟩
       map_zero' := by
         apply Subtype.ext
         simp
       map_add' := by
         intro n m
         apply Subtype.ext
         simp [add_smul, Finset.sum_add_distrib] } : (ι → ℤ) →+ dualLattice L)
    (by
      constructor
      · intro n m h
        have heq := congrArg Subtype.val h
        funext i
        apply Int.cast_injective (α := ℝ)
        have hi := congrArg (fun x : V =>
          (LinearMap.BilinForm.dualBasis (innerₗ V) (innerₗ_nondegenerate V)
            (b.ofZLatticeBasis ℝ L)).repr x i) heq
        simpa [Finsupp.single_apply] using hi
      · intro x
        have hx := x.property
        simp only [dualLattice_eq_span_dualBasis L b] at hx
        obtain ⟨n, hn⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hx
        refine ⟨n, Subtype.ext ?_⟩
        change (∑ i, (n i : ℝ) •
          LinearMap.BilinForm.dualBasis (innerₗ V) (innerₗ_nondegenerate V)
            (b.ofZLatticeBasis ℝ L) i) = (x : V)
        simpa only [Int.cast_smul_eq_zsmul] using hn)

theorem dualVector_b_coe (n : ι → ℤ) :
    (dualVector_b L b n : V) = ∑ i, (n i : ℝ) •
      LinearMap.BilinForm.dualBasis (innerₗ V) (innerₗ_nondegenerate V) (b.ofZLatticeBasis ℝ L) i := by
  rfl

theorem dualVector_b_inner_basis (n : ι → ℤ) (j : ι) :
    inner ℝ (dualVector_b L b n : V) (b j : V) = (n j : ℝ) := by
  rw [dualVector_b_coe, ← b.ofZLatticeBasis_apply ℝ L j]
  change (innerₗ V) (∑ i, (n i : ℝ) •
    LinearMap.BilinForm.dualBasis (innerₗ V) (innerₗ_nondegenerate V)
      (b.ofZLatticeBasis ℝ L) i) ((b.ofZLatticeBasis ℝ L) j) = _
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.BilinForm.apply_dualBasis_left]
  simp

theorem dualVector_b_fourierChar (x : V) (n : ι → ℤ) :
    (𝐞 (-inner ℝ x (dualVector_b L b n : V)) : ℂ) =
      UnitAddTorus.mFourier (-n)
        (fun i => ((b.ofZLatticeBasis ℝ L).repr x i : UnitAddCircle)) := by
  have hi : inner ℝ x (dualVector_b L b n : V) =
      ∑ i, (b.ofZLatticeBasis ℝ L).repr x i * (n i : ℝ) := by
    conv_lhs => rw [← (b.ofZLatticeBasis ℝ L).sum_repr x]
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_smul_left, Basis.ofZLatticeBasis_apply, real_inner_comm,
      dualVector_b_inner_basis]
  rw [hi, Real.fourierChar_apply]
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.neg_apply,
    fourier_coe_apply, Complex.ofReal_one, div_one]
  rw [← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_neg, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_intCast, Int.cast_neg, Complex.ofReal_ofNat]
  simp only [← Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

end DedekindZetaZeroFree.PoissonArch

end
