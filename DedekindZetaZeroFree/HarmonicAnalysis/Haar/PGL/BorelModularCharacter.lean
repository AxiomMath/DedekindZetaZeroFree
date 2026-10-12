module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.RankOne.NormalizedInduction

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneInduction

namespace OrdinaryModularProof
open MeasureTheory TopologicalSpace
open scoped Matrix NNReal ENNReal Matrix.Norms.Operator
variable (F : Type) [Field F] [NumberField F]
 (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))

set_option maxHeartbeats 1200000
 instance fieldSC : SecondCountableTopology (LocalField F w) := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : SeparableSpace (LocalField F w) :=
    SeparableSpace.of_denseRange _ (w.denseRange_algebraMap F)
  infer_instance

private theorem diag_nz (A : GL2 F w) (hA : A 1 0 = 0) : A 0 0 ≠ 0 ∧ A 1 1 ≠ 0 := by
  have hd := Matrix.GeneralLinearGroup.det_ne_zero A
  rw [Matrix.det_fin_two, hA, mul_zero, sub_zero] at hd
  exact mul_ne_zero_iff.mp hd

private theorem representative_upper (A : GL2 F w)
    (hA : Matrix.ProjGenLinGroup.mk A ∈ upperBorel F w) : A 1 0 = 0 := by
  obtain ⟨B, hB, hu⟩ := hA
  obtain ⟨t, rfl⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hB
  simpa [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar, Matrix.mul_diagonal, hu] using hu

def rootCoord (b : upperBorel F w) : LocalField F w :=
  let A := Classical.choose b.property
  A 0 1 / A 0 0

private theorem rootCoord_eq (b : upperBorel F w) (A : GL2 F w)
    (hA : Matrix.ProjGenLinGroup.mk A = b.val) :
    rootCoord F w b = A 0 1 / A 0 0 := by
  obtain ⟨u, heq⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp
    (hA.trans (Classical.choose_spec b.property).1.symm)
  unfold rootCoord
  rw [← heq]
  have hs (i j : Fin 2) : (A * Matrix.GeneralLinearGroup.scalar (Fin 2) u) i j =
      A i j * (u : LocalField F w) := by
    simp [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.mul_diagonal]
  dsimp only
  rw [hs, hs]
  exact mul_div_mul_right _ _ u.ne_zero

def affineMatrix (p : (LocalField F w)ˣ × LocalField F w) : GL2 F w :=
  diagonalMatrix F w p.1 * upperRootMatrix F w p.2

theorem affineMatrix_entries (p : (LocalField F w)ˣ × LocalField F w) :
    (affineMatrix F w p : Matrix (Fin 2) (Fin 2) (LocalField F w)) =
      !![(p.1 : LocalField F w), (p.1 : LocalField F w) * p.2; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [affineMatrix, diagonalMatrix, upperRootMatrix,
      Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply, Fin.sum_univ_two]

def affine (p : (LocalField F w)ˣ × LocalField F w) : upperBorel F w :=
  ⟨Matrix.ProjGenLinGroup.mk (affineMatrix F w p),
    ⟨affineMatrix F w p, rfl, by rw [affineMatrix_entries]; simp⟩⟩

theorem affine_ratio (p : (LocalField F w)ˣ × LocalField F w) :
    borelRatio F w (affine F w p) = p.1 := by
  apply Units.ext
  rw [borelRatio_eq F w _ (affineMatrix F w p) rfl]
  · rw [affineMatrix_entries]; simp
  · rw [affineMatrix_entries]; simp

theorem affine_root (p : (LocalField F w)ˣ × LocalField F w) :
    rootCoord F w (affine F w p) = p.2 := by
  rw [rootCoord_eq F w _ (affineMatrix F w p) rfl, affineMatrix_entries]
  simp [p.1.ne_zero]

theorem affine_inverse (b : upperBorel F w) :
    affine F w (borelRatio F w b, rootCoord F w b) = b := by
  obtain ⟨A, hA, h10⟩ := b.property
  have h00 := (diag_nz F w A h10).1
  have h11 := (diag_nz F w A h10).2
  apply Subtype.ext
  change Matrix.ProjGenLinGroup.mk _ = b.val
  rw [← hA]
  apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
  refine ⟨Units.mk0 (A 1 1) h11, ?_⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
    affineMatrix_entries, borelRatio_eq F w b A hA h10, rootCoord_eq F w b A hA]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_diagonal, h10, h11, h00]

theorem coords_continuous :
    Continuous (fun b : upperBorel F w => (borelRatio F w b, rootCoord F w b)) := by
  let S : Set (PGL2 F w) := upperBorel F w
  let p : GL2 F w → PGL2 F w := Matrix.ProjGenLinGroup.mk
  let f := S.restrictPreimage p
  have hq : Topology.IsQuotientMap f :=
    (QuotientGroup.isOpenQuotientMap_mk.restrictPreimage S).isQuotientMap
  apply hq.continuous_iff.mpr
  have hu (A : p ⁻¹' S) : (A.val : GL2 F w) 1 0 = 0 :=
    representative_upper F w A.val A.property
  have hn (A : p ⁻¹' S) := diag_nz F w A.val (hu A)
  have hentry (i j : Fin 2) : Continuous (fun A : p ⁻¹' S => (A.val : GL2 F w) i j) :=
    (continuous_apply_apply i j).comp ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (LocalField F w))).comp continuous_subtype_val)
  have hy : Continuous (fun A : p ⁻¹' S => borelRatio F w (f A)) := by
    apply Units.continuous_iff.mpr
    constructor
    · have he : (fun A : p ⁻¹' S => (borelRatio F w (f A) : LocalField F w)) =
          fun A => (A.val : GL2 F w) 0 0 / (A.val : GL2 F w) 1 1 := by
        funext A
        exact borelRatio_eq F w (f A) A.val rfl (hu A)
      change Continuous (fun A : p ⁻¹' S => (borelRatio F w (f A) : LocalField F w))
      rw [he]
      exact (hentry 0 0).div (hentry 1 1) (fun A => (hn A).2)
    · have he : (fun A : p ⁻¹' S => ((borelRatio F w (f A))⁻¹ : LocalField F w)) =
          fun A => (A.val : GL2 F w) 1 1 / (A.val : GL2 F w) 0 0 := by
        funext A
        change (borelRatio F w (f A) : LocalField F w)⁻¹ = _
        rw [borelRatio_eq F w (f A) A.val rfl (hu A), inv_div]
      change Continuous (fun A : p ⁻¹' S => (borelRatio F w (f A) : LocalField F w)⁻¹)
      rw [he]
      exact (hentry 1 1).div (hentry 0 0) (fun A => (hn A).1)
  have hx : Continuous (fun A : p ⁻¹' S => rootCoord F w (f A)) := by
    have he : (fun A : p ⁻¹' S => rootCoord F w (f A)) =
        fun A => (A.val : GL2 F w) 0 1 / (A.val : GL2 F w) 0 0 := by
      funext A
      exact rootCoord_eq F w (f A) A.val rfl
    rw [he]
    exact (hentry 0 1).div (hentry 0 0) (fun A => (hn A).1)
  exact hy.prodMk hx

theorem affine_continuous : Continuous (affine F w) := by
  have hmat : Continuous (affineMatrix F w) := by
    apply Units.continuous_iff.mpr
    constructor
    · have he : (fun p => (affineMatrix F w p : Matrix (Fin 2) (Fin 2) (LocalField F w))) =
          fun p => !![(p.1 : LocalField F w), (p.1 : LocalField F w) * p.2; 0, 1] := by
        funext p; exact affineMatrix_entries F w p
      change Continuous (fun p => (affineMatrix F w p : Matrix (Fin 2) (Fin 2) (LocalField F w)))
      rw [he]
      fun_prop
    · have he : (fun p => Units.val ((affineMatrix F w p)⁻¹)) =
          fun p => !![Units.val (p.1⁻¹), -p.2; 0, 1] := by
        funext p
        have hh : (affineMatrix F w p)⁻¹ = affineMatrix F w (p.1⁻¹, -(p.1 : LocalField F w) * p.2) := by
          apply inv_eq_of_mul_eq_one_left
          apply Units.ext
          rw [Matrix.GeneralLinearGroup.coe_mul, affineMatrix_entries, affineMatrix_entries]
          ext i j
          fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, p.1.ne_zero]
        rw [hh, affineMatrix_entries]
        simp [p.1.ne_zero]
      rw [he]
      fun_prop
  exact (QuotientGroup.continuous_mk.comp hmat).subtype_mk _

def affineHomeomorph : (LocalField F w)ˣ × LocalField F w ≃ₜ upperBorel F w where
  toFun := affine F w
  invFun b := (borelRatio F w b, rootCoord F w b)
  left_inv p := by simp only [affine_ratio, affine_root]
  right_inv := affine_inverse F w
  continuous_toFun := affine_continuous F w
  continuous_invFun := coords_continuous F w

instance unitsLC : LocallyCompactSpace (LocalField F w)ˣ :=
  (Units.isOpenEmbedding_val (R := LocalField F w)).locallyCompactSpace

instance unitsSC : SecondCountableTopology (LocalField F w)ˣ :=
  (Units.isOpenEmbedding_val (R := LocalField F w)).isEmbedding.secondCountableTopology

instance borelLC : LocallyCompactSpace (upperBorel F w) :=
  (affineHomeomorph F w).symm.isOpenEmbedding.locallyCompactSpace

instance borelSC : SecondCountableTopology (upperBorel F w) :=
  (affineHomeomorph F w).symm.isEmbedding.secondCountableTopology

instance borelT2 : T2Space (upperBorel F w) :=
  (affineHomeomorph F w).symm.isEmbedding.t2Space

end OrdinaryModularProof

end DedekindZetaZeroFree.KPRankOneInduction

end
