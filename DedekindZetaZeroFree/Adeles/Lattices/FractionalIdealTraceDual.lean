module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.Archimedean.TraceNormalization

@[expose] public section

noncomputable section
open scoped Classical nonZeroDivisors
open NumberField

namespace DedekindZetaZeroFree
namespace PoissonArch

variable (F : Type) [Field F] [NumberField F]

abbrev NonzeroFractionalIdeal := (FractionalIdeal (RingOfIntegers F)⁰ F)ˣ

def minkowskiEmbedding : F →+ Space F :=
  (NumberField.mixedEmbedding.euclidean.toMixed F).symm.toAddMonoidHom.comp
    (NumberField.mixedEmbedding F).toAddMonoidHom

def idealLattice (I : NonzeroFractionalIdeal F) : Submodule ℤ (Space F) :=
  ZLattice.comap ℝ (NumberField.mixedEmbedding.idealLattice F I)
    (NumberField.mixedEmbedding.euclidean.toMixed F).toLinearMap

instance idealLattice_discrete (I : NonzeroFractionalIdeal F) :
    DiscreteTopology (idealLattice F I) := by
  unfold idealLattice
  infer_instance

instance idealLattice_isZLattice (I : NonzeroFractionalIdeal F) :
    IsZLattice ℝ (idealLattice F I) := by
  unfold idealLattice
  infer_instance

theorem mem_idealLattice (I : NonzeroFractionalIdeal F) (y : Space F) :
    y ∈ idealLattice F I ↔
      ∃ x : F, x ∈ (I : FractionalIdeal (RingOfIntegers F)⁰ F) ∧
        minkowskiEmbedding F x = y := by
  change NumberField.mixedEmbedding.euclidean.toMixed F y ∈
    NumberField.mixedEmbedding.idealLattice F I ↔ _
  rw [NumberField.mixedEmbedding.mem_idealLattice]
  refine exists_congr fun x => and_congr_right fun _ => ?_
  exact ((NumberField.mixedEmbedding.euclidean.toMixed F).symm_apply_eq).symm

def codifferentIdeal : NonzeroFractionalIdeal F :=
  Units.mk0 (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (RingOfIntegers F)⁰ F))
    (FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero)

theorem codifferentIdeal_eq_inv_different :
    (codifferentIdeal F : FractionalIdeal (RingOfIntegers F)⁰ F) =
      (differentIdeal ℤ (RingOfIntegers F) :
        FractionalIdeal (RingOfIntegers F)⁰ F)⁻¹ := by
  rw [coeIdeal_differentIdeal ℤ ℚ F]
  simp [codifferentIdeal]

def idealTraceDual (I : NonzeroFractionalIdeal F) : Set (Space F) :=
  {y | ∀ x : F, x ∈ (I : FractionalIdeal (RingOfIntegers F)⁰ F) →
    tracePairing F (minkowskiEmbedding F x) y ∈ Set.range (fun n : ℤ => (n : ℝ))}

private theorem trace_embedding (x z : F) :
    tracePairing F (minkowskiEmbedding F x) (minkowskiEmbedding F z) =
      (Algebra.trace ℚ F (x * z) : ℝ) := by
  have ht := trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := x * z)
  rw [← Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) (fun φ => φ (x*z))
    (fun σ => σ (x*z)) (fun φ => rfl)] at ht
  rw [← Fintype.sum_equiv (mixedEmbedding.indexEquiv F)
    (fun i => mixedEmbedding.indexEquiv F i (x*z)) (fun φ => φ (x*z))
    (fun i => rfl)] at ht
  have ht' := congrArg Complex.re ht
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two,
    mixedEmbedding.indexEquiv_apply_isReal, mixedEmbedding.indexEquiv_apply_isComplex_fst,
    mixedEmbedding.indexEquiv_apply_isComplex_snd, map_mul, ComplexEmbedding.conjugate_coe_eq,
    map_sum, Complex.add_re, Complex.conj_re, Complex.ratCast_re] at ht'
  have hr (w : {w : InfinitePlace F // w.IsReal}) (a : F) :
      (w.val.embedding a).re = InfinitePlace.embedding_of_isReal w.prop a ∧
      (w.val.embedding a).im = 0 := by
    constructor
    · exact (congrArg Complex.re (InfinitePlace.embedding_of_isReal_apply w.prop a)).symm
    · simpa only [Complex.ofReal_im] using
        (congrArg Complex.im (InfinitePlace.embedding_of_isReal_apply w.prop a)).symm
  simpa [tracePairing, minkowskiEmbedding, AddMonoidHom.comp_apply,
    mixedEmbedding, (hr _ _).1, (hr _ _).2,
    Finset.sum_add_distrib, ← two_mul, Finset.mul_sum] using ht'.symm
private theorem trace_dual_rational (I : NonzeroFractionalIdeal F) (y : Space F)
    (hy : y ∈ idealTraceDual F I) : ∃ z : F, minkowskiEmbedding F z = y := by
  let b := basisOfFractionalIdeal F I
  have hb (i : Module.Free.ChooseBasisIndex ℤ I) : b i ∈ (I : FractionalIdeal (RingOfIntegers F)⁰ F) := by
    apply (mem_span_basisOfFractionalIdeal (K := F)).mp
    exact Submodule.subset_span ⟨i, rfl⟩
  choose n hn using fun i => hy (b i) (hb i)
  let z : F := ∑ i, (n i : ℚ) • b.traceDual i
  refine ⟨z, (traceAdapter F).injective ?_⟩
  let B := (mixedEmbedding.fractionalIdealLatticeBasis F I).map
    (mixedEmbedding.euclidean.toMixed F).symm.toLinearEquiv
  apply InnerProductSpace.ext_inner_left_basis B
  intro i
  simp only [B, Module.Basis.map_apply, mixedEmbedding.fractionalIdealLatticeBasis_apply]
  change inner ℝ (minkowskiEmbedding F (b i)) (traceAdapter F (minkowskiEmbedding F z)) =
    inner ℝ (minkowskiEmbedding F (b i)) (traceAdapter F y)
  rw [← tracePairing_eq_inner, ← tracePairing_eq_inner, trace_embedding]
  rw [← hn i]
  dsimp [z]
  simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul,
    b.trace_mul_traceDual, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Rat.cast_intCast]
private theorem trace_integral_iff (q : ℚ) :
    (q : ℝ) ∈ Set.range (fun n : ℤ => (n : ℝ)) ↔
      q ∈ (algebraMap ℤ ℚ).range := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    change (n : ℚ) = q
    change (n : ℝ) = (q : ℝ) at hn
    exact_mod_cast hn
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    change (n : ℚ) = q at hn
    change (n : ℝ) = (q : ℝ)
    exact_mod_cast hn

theorem idealTraceDual_eq (I : NonzeroFractionalIdeal F) :
    idealTraceDual F I = (idealLattice F (codifferentIdeal F * I⁻¹) : Set (Space F)) := by
  have hc : ((codifferentIdeal F * I⁻¹ : NonzeroFractionalIdeal F) :
      FractionalIdeal (RingOfIntegers F)⁰ F) = FractionalIdeal.dual ℤ ℚ I := by
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, codifferentIdeal, Units.val_mk0]
    exact (FractionalIdeal.dual_eq_mul_inv ℤ ℚ (I : FractionalIdeal (RingOfIntegers F)⁰ F)).symm
  ext y
  rw [SetLike.mem_coe, mem_idealLattice]
  simp only [hc]
  constructor
  · intro hy
    obtain ⟨z, rfl⟩ := trace_dual_rational F I y hy
    refine ⟨z, ?_, rfl⟩
    rw [FractionalIdeal.mem_dual (Units.ne_zero I)]
    intro x hx
    rw [Algebra.traceForm_apply, mul_comm, ← trace_integral_iff]
    rw [← trace_embedding]
    exact hy x hx
  · rintro ⟨z, hz, rfl⟩
    rw [FractionalIdeal.mem_dual (Units.ne_zero I)] at hz
    intro x hx
    rw [trace_embedding, trace_integral_iff, mul_comm]
    exact hz x hx

end PoissonArch
end DedekindZetaZeroFree

end
