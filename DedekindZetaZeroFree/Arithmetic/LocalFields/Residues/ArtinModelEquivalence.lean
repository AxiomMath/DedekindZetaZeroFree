module

public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Sextic.CharacterOrder
public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Hilbert.SexticHilbertNormalization

@[expose] public section

open scoped NumberField Classical ValuativeRel
open NumberField IsDedekindDomain
noncomputable section
namespace DedekindZetaZeroFree.LocalFiniteSumCompatibility
open LocalFiniteSums
variable {F : Type} [Field F] [NumberField F] {A : SArithmeticData F}
local instance cftResidueValuativeRel (p : ExteriorPrime A) : ValuativeRel (LocalField p) := ClassFieldTheory.finitePlaceCompletionValuativeRel F p.val

def integerRingEquiv (p : ExteriorPrime A) : LocalIntegers p ≃+* (ValuativeRel.valuation (LocalField p)).integer := by
  letI : (Valued.v : Valuation (LocalField p) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  have he := (Valuation.isEquiv_iff_valuationSubring _ _).mp (ValuativeRel.isEquiv (Valued.v : Valuation (LocalField p) (WithZero (Multiplicative ℤ))) (ValuativeRel.valuation (LocalField p)))
  exact RingEquiv.restrict (RingEquiv.refl _) _ _ (fun x => by change x ∈ (Valued.v : Valuation (LocalField p) (WithZero (Multiplicative ℤ))).valuationSubring ↔ x ∈ (ValuativeRel.valuation (LocalField p)).valuationSubring; rw [he])

local instance cftResidueLocalField (p : ExteriorPrime A) : IsNonarchimedeanLocalField (LocalField p) := ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F p.val

def cftResidueEquiv (p : ExteriorPrime A) : (A.R ⧸ A.extendIdeal (primeIdeal p)) ≃+* IsLocalRing.ResidueField (ValuativeRel.valuation (LocalField p)).integer :=
  (A.exteriorLocalResidueEquiv (primeIdeal p) p.val rfl).trans (IsLocalRing.ResidueField.mapEquiv (integerRingEquiv p))

theorem cftResidueEquiv_mk (p : ExteriorPrime A) (x : A.R) :
    cftResidueEquiv p (Ideal.Quotient.mk _ x) = IsLocalRing.residue _ (integerRingEquiv p (integerMap p x)) := by
  unfold cftResidueEquiv
  rw [RingEquiv.trans_apply, A.exteriorLocalResidueEquiv_apply (primeIdeal p) p.val rfl x,
    IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  rfl

theorem rootReduction (p : ExteriorPrime A)
    (hn : ValuativeRel.valuation (LocalField p) (6 : LocalField p) = 1)
    (hmu : (primitiveRoots 6 (LocalField p)).Nonempty) (z : KummerTheory.nthRootsSubgroup (LocalField p) 6)
    (w : (ValuativeRel.valuation (LocalField p)).integer)
    (hw : (w : LocalField p) = (z.val : LocalField p)) :
    (((LocalClassFieldTheory.Kummer.localNthRootsReductionEquiv (LocalField p) 6
      hn hmu z).val) : _) =
      IsLocalRing.residue _ w := by
  change IsLocalRing.residue _ (LocalClassFieldTheory.Kummer.nthRootIntegerUnit (LocalField p) 6 z).val = _
  congr 1
  apply Subtype.ext
  have h := congrArg Units.val (LocalClassFieldTheory.Kummer.integerUnitsToFieldUnits_nthRootIntegerUnit (LocalField p) 6 z)
  exact h.trans hw.symm

end DedekindZetaZeroFree.LocalFiniteSumCompatibility

end
