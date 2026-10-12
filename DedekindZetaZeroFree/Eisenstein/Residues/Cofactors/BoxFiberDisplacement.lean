module

public import DedekindZetaZeroFree.Eisenstein.Continuation.Cofactors.HeightAndTailBounds

@[expose] public section

noncomputable section
open _root_.DedekindZetaZeroFree.RestrictedTensorSimple renaming inclusion_insert → inclusion_insert
open scoped Classical NumberField TensorProduct BigOperators
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource.CofactorChamber
open KPLocalPrincipalSeries KPGlobalTorusFiniteStages KPLocalExceptionalConstruction
open KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem source_extend (E : Finset (KPFinitePlace F)) (hE : C.exceptional ⊆ E)
    (φ : ∀ q : E, compactPicture (C.canonical q.val).borel (C.polarization q.val)
      (C.canonical q.val).iwasawa .plus)
    (t : RestrictedTensorSimple.Level (bad R.A P C))
    (hst : cofactorSourceLevel R P C E hE ≤ t) :
    cofactorSourceCore R P C E hE φ =
      RestrictedTensorSimple.stageInclusion (Plus R.A P C) (plusReference R.A P C)
        (bad R.A P C) t (PiTensorProduct.tprod ℂ (cofactorExtendedTuple R P C E hE φ t)) := by
  let s := cofactorSourceLevel R P C E hE
  let y := cofactorExtendedTuple R P C E hE φ t
  have ht := RestrictedTensorSimple.insert_pure (Plus R.A P C) (plusReference R.A P C)
    s.val t.val hst (cofactorSourceTuple R P C E hE φ)
  have hh := congrArg (RestrictedTensorSimple.stageInclusion (Plus R.A P C)
    (plusReference R.A P C) (bad R.A P C) t) ht
  change RestrictedTensorSimple.stageInclusion _ _ _ s _ = _
  calc
    _ = RestrictedTensorSimple.stageInclusion (Plus R.A P C) (plusReference R.A P C)
        (bad R.A P C) t (RestrictedTensorSimple.insert (Plus R.A P C)
          (plusReference R.A P C) s.val t.val hst
          (PiTensorProduct.tprod ℂ (cofactorSourceTuple R P C E hE φ))) := by
      exact (LinearMap.congr_fun (inclusion_insert (Plus R.A P C) (plusReference R.A P C) (bad R.A P C) s t hst) _).symm
    _ = _ := by
      refine hh.trans ?_
      congr 1
      apply congrArg (PiTensorProduct.tprod ℂ)
      funext j
      by_cases hj : j.val ∈ s.val
      · simp only [y, cofactorExtendedTuple, show (cofactorSourceLevel R P C E hE).val = s.val from rfl, dite_eq_left hj]
      · simp only [y, cofactorExtendedTuple, show (cofactorSourceLevel R P C E hE).val = s.val from rfl, dite_eq_right hj]

theorem box_fiber_stage (E Q : Finset (KPFinitePlace F)) (hE : C.exceptional ⊆ E)
    (hEQ : E ⊆ Q)
    (φ : ∀ q : E, compactPicture (C.canonical q.val).borel (C.polarization q.val)
      (C.canonical q.val).iwasawa .plus)
    (x : KPGlobalTorusFunctionData.Adeles F) (hx : x ∈ TraceBox.adelicBox F Q)
    (z : ℂ) (t : KPGlobalTorusFunctionData.E F ζ hζ) :
    let v := cofactorSourceLevel R P C Q (hE.trans hEQ)
    let y := cofactorExtendedTuple R P C E hE φ v
    (coreFlatFiber R P C (cofactorSourceCore R P C E hE φ) z
      (chamberRaw F ζ hζ x)).val.val t =
      Complex.exp (z * (ThetaExpansion.iwasawaLogHeight R
        (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
          (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ (chamberRaw F ζ hζ x))) : ℂ)) *
      (comparison R.A P C (RestrictedTensorSimple.stageInclusion
        (Fiber R.A P C) (reference R.A P C) (bad R.A P C) v
        (PiTensorProduct.tprod ℂ (fun j => localValue R.A P C j.val
          (chamberRaw F ζ hζ x j.val) (y j))))).val.val t := by
  let v := cofactorSourceLevel R P C Q (hE.trans hEQ)
  have huv : cofactorSourceLevel R P C E hE ≤ v := by
    intro j hj
    cases j with
    | inl w => simp [v, cofactorSourceLevel]
    | inr q => exact Finset.inr_mem_disjSum.mpr (hEQ (Finset.inr_mem_disjSum.mp hj))
  dsimp only
  rw [source_extend R P C E hE φ v huv]
  exact coreFlatFiber_stage R P C v _ _ (chamber_raw_tail R P C Q (hE.trans hEQ) x hx) z t

theorem box_fiber_parameter (E Q : Finset (KPFinitePlace F)) (hE : C.exceptional ⊆ E)
    (hEQ : E ⊆ Q)
    (φ : ∀ q : E, compactPicture (C.canonical q.val).borel (C.polarization q.val)
      (C.canonical q.val).iwasawa .plus)
    (x : KPGlobalTorusFunctionData.Adeles F) (hx : x ∈ TraceBox.adelicBox F Q)
    (z : ℂ) (t : KPGlobalTorusFunctionData.E F ζ hζ) :
    let v := cofactorSourceLevel R P C Q (hE.trans hEQ)
    let y := cofactorExtendedTuple R P C E hE φ v
    (coreFlatFiber R P C (cofactorSourceCore R P C E hE φ) z
      (chamberRaw F ζ hζ x)).val.val t =
      (comparison R.A P C (RestrictedTensorSimple.stageInclusion
        (Fiber R.A P C) (reference R.A P C) (bad R.A P C) v
        (PiTensorProduct.tprod ℂ (fun j =>
          Complex.exp (z * (FaithfulSource.RepairedInducing.localLog R P C
            (chamberRaw F ζ hζ x) j.val : ℂ)) •
          localValue R.A P C j.val (chamberRaw F ζ hζ x j.val) (y j))))).val.val t := by
  let v := cofactorSourceLevel R P C Q (hE.trans hEQ)
  let y := cofactorExtendedTuple R P C E hE φ v
  dsimp only
  rw [box_fiber_stage R P C E Q hE hEQ φ x hx z t,
    chamber_height_stage R P C Q (hE.trans hEQ) x hx]
  rw [(PiTensorProduct.tprod ℂ).map_smul_univ]
  simp only [map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  have hp : (∏ j : v.val, Complex.exp (z *
      (FaithfulSource.RepairedInducing.localLog R P C (chamberRaw F ζ hζ x) j.val : ℂ))) =
      Complex.exp (z * ((∑ j : v.val,
        FaithfulSource.RepairedInducing.localLog R P C (chamberRaw F ζ hζ x) j.val : ℝ) : ℂ)) := by
    rw [← Complex.exp_sum]
    apply congrArg Complex.exp
    rw [Complex.ofReal_sum, Finset.mul_sum]
  rw [hp]

end DedekindZetaZeroFree.FourierContinuation.LiteralSource.CofactorChamber

end
