module

public import DedekindZetaZeroFree.HarmonicAnalysis.Schwartz.Lattices.UniformPeriodisation

@[expose] public section

noncomputable section
open scoped SchwartzMap
open Module

namespace DedekindZetaZeroFree.PoissonArch

def torusPeriodisation
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    {L : Submodule ℤ V} [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ L) (f : 𝓢(V, ℂ)) :
    C(UnitAddTorus ι, ℂ) where
  toFun t := periodisation L f
    ((b.ofZLatticeBasis ℝ L).equivFun.symm
      (fun i => ((AddCircle.equivIco (1 : ℝ) (0 : ℝ)) (t i) : ℝ)))
  continuous_toFun := by
    classical
    let B := b.ofZLatticeBasis ℝ L
    have hquot : Topology.IsQuotientMap
        (fun x : ι → ℝ => (fun i => (x i : UnitAddCircle))) :=
      (IsOpenQuotientMap.piMap
        (fun _ : ι => (QuotientAddGroup.isOpenQuotientMap_mk :
          IsOpenQuotientMap (fun x : ℝ => (x : UnitAddCircle))))).isQuotientMap
    apply hquot.continuous_iff.mpr
    have hperiod (x : ι → ℝ) :
        periodisation L f (B.equivFun.symm
          (fun i => ((AddCircle.equivIco (1 : ℝ) (0 : ℝ)) (x i : UnitAddCircle) : ℝ))) =
        periodisation L f (B.equivFun.symm x) := by
      let v : L := ∑ i, (-⌊x i⌋) • b i
      have heq : B.equivFun.symm
          (fun i => ((AddCircle.equivIco (1 : ℝ) (0 : ℝ)) (x i : UnitAddCircle) : ℝ)) =
          B.equivFun.symm x + (v : V) := by
        simp only [AddCircle.coe_equivIco_mk_apply, div_one, mul_one,
          Basis.equivFun_symm_apply, Int.fract]
        simp only [v, Submodule.coe_sum, Submodule.coe_smul_of_tower,
          Int.cast_neg, zsmul_eq_mul]
        simp only [B, Basis.ofZLatticeBasis_apply, sub_smul, Finset.sum_sub_distrib]
        rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        simp [neg_smul, Int.cast_smul_eq_zsmul]
      rw [heq, periodisation_add_lattice]
    have hfun : (fun x : ι → ℝ => periodisation L f
        (B.equivFun.symm
          (fun i => ((AddCircle.equivIco (1 : ℝ) (0 : ℝ)) (x i : UnitAddCircle) : ℝ)))) =
        (fun x => periodisation L f (B.equivFun.symm x)) := funext hperiod
    change Continuous (fun x : ι → ℝ => periodisation L f
      (B.equivFun.symm
        (fun i => ((AddCircle.equivIco (1 : ℝ) (0 : ℝ)) (x i : UnitAddCircle) : ℝ))))
    rw [hfun]
    exact (continuous_periodisation L f).comp
      B.equivFun.toContinuousLinearEquiv.symm.continuous

theorem torusPeriodisation_coe
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    {L : Submodule ℤ V} [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ L) (f : 𝓢(V, ℂ))
    (x : ι → ℝ) :
    torusPeriodisation b f (fun i => (x i : UnitAddCircle)) =
      periodisation L f ((b.ofZLatticeBasis ℝ L).equivFun.symm x) := by
  classical
  let B := b.ofZLatticeBasis ℝ L
  let v : L := ∑ i, (-⌊x i⌋) • b i
  change periodisation L f (B.equivFun.symm
    (fun i => ((AddCircle.equivIco (1 : ℝ) (0 : ℝ)) (x i : UnitAddCircle) : ℝ))) = _
  have heq : B.equivFun.symm
      (fun i => ((AddCircle.equivIco (1 : ℝ) (0 : ℝ)) (x i : UnitAddCircle) : ℝ)) =
      B.equivFun.symm x + (v : V) := by
    simp only [AddCircle.coe_equivIco_mk_apply, div_one, mul_one,
      Basis.equivFun_symm_apply, Int.fract]
    simp only [v, Submodule.coe_sum, Submodule.coe_smul_of_tower,
      Int.cast_neg, zsmul_eq_mul]
    simp only [B, Basis.ofZLatticeBasis_apply, sub_smul, Finset.sum_sub_distrib]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp [neg_smul, Int.cast_smul_eq_zsmul]
  rw [heq, periodisation_add_lattice]

end DedekindZetaZeroFree.PoissonArch

end
