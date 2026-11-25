/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicIntegralModel
public import WeilConjectures.SixFunctors.NearbyCycles.ExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeIntegralRational
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.SmoothPadicAlgCl
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.Constructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.OpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicSubfieldFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushResidueFinal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionConstructible
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorResidue
public import WeilConjectures.TraceFormula.Specialization.NormalizePrecoherent

/-!

# Generic vanishing along a divisor for `ℚ̄_ℓ`-coefficients, from finite coefficients

Let `X` be normal, `Z = V(h)` a principal divisor with complement `j : X ∖ Z ⟶ X` and `ζ` a
generic point of `Z`. For every bounded constructible `ℚ̄_ℓ`-complex `N` on `X ∖ Z`, the
restriction `Le^* Ψ_X(j_! N)` vanishes over a neighbourhood of `ζ`
(`ProEtale.CondensedRing.exists_isZero_upperStar_nearbyCycles_lowerShriek_padicAlgCl`), granted
the same statement for bounded constructible complexes with coefficients in the residue field
`𝔽_E` of a finite subextension `E ⊆ ℚ̄_ℓ`
(`ProEtale.CondensedRing.exists_isZero_upperStar_nearbyCycles_lowerShriek_residueField`).

## Proof

Write `G_Λ(K) = Lι^* Le^* Ψ_X^Λ(j_! K)`, where `ι` is the inclusion of the inverse image of an open
`U ∋ ζ` of `Z`. All functors in `G_Λ` commute with a change of coefficients, the pushforward
`Rj_*` of the deformation on bounded below complexes
(`NearbyCyclesModel.isZero_upperStar_upperStar_nearbyCycles_lowerShriek_extendScalars`).

* `N ≅ ℚ̄_ℓ ⊗ᴸ_E (E ⊗ᴸ_{𝒪_E} N₀)` for a bounded constructible `𝒪_E`-complex `N₀`
  (`ProEtale.exists_padicAlgCl_iso_integralModel`), so it suffices that `G_{𝒪_E}(N₀) = 0`.
* The first derived reduction of `G_{𝒪_E}(N₀)` is `G_{𝔽_E}(𝔽_E ⊗ᴸ N₀)`, which vanishes for a
  suitable `U` by the finite-coefficient statement, `𝔽_E ⊗ᴸ N₀` being bounded constructible
  (`ProEtale.boundedConstructible_derivedExtendScalars_residueField`).
* `G_{𝒪_E}(N₀)` is derived complete: `j_! N₀` is bounded constructible, hence derived complete
  (`ProEtale.derivedCompleteIntegers_of_boundedConstructible`), and derived completeness is
  preserved by `Rj_*`, by the pullbacks along morphisms of quasi-compact quasi-separated schemes
  and by the restriction to an open subscheme. By derived Nakayama
  (`ProEtale.isZero_of_derivedCompleteIntegers_of_isZero_derivedReduction`), `G_{𝒪_E}(N₀) = 0`.

-/

@[expose] public section

universe u

open CategoryTheory Limits Topology TopologicalSpace

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

section Instances

variable {k : Type u} [Field k] (X : Over (Spec (.of k)))
  (I : X.left.IdealSheafData) (k' : Type u) [Field k'] [Algebra k k']

instance [QuasiCompact X.hom] : CompactSpace (deformationModel X I k').total :=
  QuasiCompact.compactSpace_of_compactSpace (deformationTotalToTrait X I k')

instance [IsSeparated X.hom] : QuasiSeparatedSpace (deformationModel X I k').total :=
  quasiSeparatedSpace_of_quasiSeparated (deformationTotalToTrait X I k')

instance : QuasiCompact (deformationModel X I k').j := by
  rw [deformationModel_j, deformationGenericToTotal]
  infer_instance

instance : QuasiSeparated (deformationModel X I k').j := by
  rw [deformationModel_j, deformationGenericToTotal]
  infer_instance

instance [QuasiCompact X.hom] : CompactSpace (deformationModel X I k').generic :=
  QuasiCompact.compactSpace_of_compactSpace (deformationModel X I k').j

instance [IsSeparated X.hom] : QuasiSeparatedSpace (deformationModel X I k').generic :=
  quasiSeparatedSpace_of_quasiSeparated (deformationModel X I k').j

instance [QuasiCompact X.hom] : CompactSpace (deformationSpecialFibre X I k').left :=
  QuasiCompact.compactSpace_of_compactSpace (deformationSpecialFibre X I k').hom

instance [IsSeparated X.hom] : QuasiSeparatedSpace (deformationSpecialFibre X I k').left :=
  quasiSeparatedSpace_of_quasiSeparated (deformationSpecialFibre X I k').hom

end Instances

namespace NearbyCyclesModel

/-- Two flat coefficient changes preserve restricted vanishing when their pushforward
comparisons are invertible on bounded below complexes. -/
private lemma isZero_upperStar_upperStar_nearbyCycles_lowerShriek_flat_composite
    [ht12 : ∀ (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) Ab.{u + 1})
      [MonObj R] [IsCommMonObj R]
      (A B C : GradedObject ℤ (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) R)),
      GradedObject.HasGoodTensor₁₂Tensor A B C]
    [ht23 : ∀ (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) Ab.{u + 1})
      [MonObj R] [IsCommMonObj R]
      (A B C : GradedObject ℤ (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) R)),
      GradedObject.HasGoodTensorTensor₂₃ A B C]
    [ht4 : ∀ (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) Ab.{u + 1})
      [MonObj R] [IsCommMonObj R]
      (A B C D : GradedObject ℤ (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) R)),
      GradedObject.HasTensor₄ObjExt A B C D]
    {Λ₀ Λ₁ Λ₂ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ₀] [IsCommMonObj Λ₀] [MonObj Λ₁] [IsCommMonObj Λ₁]
    [MonObj Λ₂] [IsCommMonObj Λ₂]
    (a : Λ₀ ⟶ Λ₁) [IsMonHom a] (b : Λ₁ ⟶ Λ₂) [IsMonHom b]
    [∀ T : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a T))]
    [∀ T : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap b T))]
    {X X' U Y W : Scheme.{u}} (M : NearbyCyclesModel X X')
    (o : U ⟶ X) [IsOpenImmersion o] (e : Y ⟶ X') (ι : W ⟶ Y)
    (K₀ : DerivedCategory (Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ₀ U)))
    (n : ℤ) (hn : ((L((M.ε)^*⟦Λ₀⟧)).obj (D((o)_!open⟦Λ₀⟧).obj K₀)).IsGE n)
    (ha : ∀ (K : DerivedCategory (Mod (Sheaf (ProEt.topology M.generic) Ab.{u + 1})
      (condensedRingObj Λ₀ M.generic))) (n : ℤ), K.IsGE n →
      IsIso ((derivedPushHom a M.j).app K))
    (hb : ∀ (K : DerivedCategory (Mod (Sheaf (ProEt.topology M.generic) Ab.{u + 1})
      (condensedRingObj Λ₁ M.generic))) (n : ℤ), K.IsGE n →
      IsIso ((derivedPushHom b M.j).app K))
    (h : IsZero ((L((ι)^*⟦Λ₀⟧)).obj ((L((e)^*⟦Λ₀⟧)).obj
      ((M.nearbyCycles Λ₀).obj (D((o)_!open⟦Λ₀⟧).obj K₀))))) :
    IsZero ((L((ι)^*⟦Λ₂⟧)).obj ((L((e)^*⟦Λ₂⟧)).obj
      ((M.nearbyCycles Λ₂).obj (D((o)_!open⟦Λ₂⟧).obj
        ((L(Mod.extendScalars (coefficientMap b U))).obj
          ((L(Mod.extendScalars (coefficientMap a U))).obj K₀)))))) := by
  have h₁ := isZero_upperStar_upperStar_nearbyCycles_lowerShriek_extendScalars
    a M o e ι K₀ (derivedPushHom a M.j) (ha _ n hn) h
  have hn₁ : ((L((M.ε)^*⟦Λ₀⟧) ⋙ L(Mod.extendScalars (coefficientMap a M.generic))).obj
      (D((o)_!open⟦Λ₀⟧).obj K₀)).IsGE n :=
    isGE_leftDerivedFunctor_extendScalars_obj a _ n
  have hn₂ := DerivedCategory.TStructure.t.isGE_of_iso
    ((derivedUpperStarExtendScalarsIso a M.ε).app (D((o)_!open⟦Λ₀⟧).obj K₀) ≪≫
      (L((M.ε)^*⟦Λ₁⟧)).mapIso ((derivedOpenImmersionShriekIso a o).app K₀)) n
  exact isZero_upperStar_upperStar_nearbyCycles_lowerShriek_extendScalars
    b M o e ι _ (derivedPushHom b M.j) (hb _ n hn₂) h₁

variable {ℓ : ℕ} [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) {X X' U Y W : Scheme.{u}}
  (M : NearbyCyclesModel X X') (o : U ⟶ X) [IsOpenImmersion o] (e : Y ⟶ X') (ι : W ⟶ Y)
  [IsOpenImmersion ι]

-- Elaborating the statement compares the derived categories of the coefficient rings.
/-- **Restricted nearby cycles of extensions by zero, from the residue field to `𝒪_E`**: let `M`
be a model of `X` whose total space and geometric generic fibre are quasi-compact and
quasi-separated, `o : U ⟶ X` an open immersion, `e : Y ⟶ X'` a morphism of quasi-compact
quasi-separated schemes, `ι : W ⟶ Y` an open immersion and `K₀` an `𝒪_E`-complex on `U` with
`Do_! K₀` derived complete and `Lε^* Do_! K₀` bounded below. If
`Lι^* Le^* Ψ(Do_!(𝔽_E ⊗ᴸ K₀))` vanishes, so does `Lι^* Le^* Ψ(Do_! K₀)`: it is derived complete,
and its first derived reduction is the former (derived Nakayama). -/
theorem isZero_upperStar_upperStar_nearbyCycles_lowerShriek_padicIntegers_of_residueField
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace X'] [QuasiSeparatedSpace X']
    [CompactSpace M.generic] [QuasiSeparatedSpace M.generic] [CompactSpace M.total]
    [QuasiSeparatedSpace M.total] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (K₀ : DerivedCategory (Mod (Sheaf (ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) U)))
    (hK₀ : derivedCompleteIntegers ℓ E X
      (D((o)_!open⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj K₀))
    (n : ℤ) (hn : ((L((M.ε)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj
      (D((o)_!open⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj K₀)).IsGE n)
    (h : IsZero ((L((ι)^*⟦Profinite.continuousMapRingObj (integersResidueField ℓ E.1)⟧)).obj
      (L((e)^*⟦Profinite.continuousMapRingObj (integersResidueField ℓ E.1)⟧).obj
        ((M.nearbyCycles (Profinite.continuousMapRingObj (integersResidueField ℓ E.1))).obj
          (D((o)_!open⟦Profinite.continuousMapRingObj (integersResidueField ℓ E.1)⟧).obj
            ((L(Mod.extendScalars (coefficientMap
              (Profinite.padicIntegersRingObjToResidueField ℓ E.1) U))).obj K₀)))))) :
    IsZero ((L((ι)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj
      (L((e)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj
        ((M.nearbyCycles (Profinite.padicIntegersRingObj ℓ E.1)).obj
          (D((o)_!open⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj K₀)))) := by
  refine isZero_of_derivedCompleteIntegers_of_isZero_derivedReduction ?_ ?_
  · exact derivedCompleteIntegers_leftDerivedUpperStar_obj_of_isOpenImmersion ι
      (derivedCompleteIntegers_leftDerivedUpperStar_obj e
        (derivedCompleteIntegers_leftDerivedUpperStar_obj M.i
          (derivedCompleteIntegers_rightDerivedLowerStar_obj M.j
            (derivedCompleteIntegers_leftDerivedUpperStar_obj M.ε hK₀))))
  · rw [isZero_derivedReduction_iff]
    delta padicIntegersToResidueField residueFieldRingObj
    have hφ := isIso_derivedUpperStarExtendScalarsPushHom_residueField_app ℓ E M.j
      ((L((M.ε)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj
        (D((o)_!open⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj K₀)) n
    have k := isZero_extendScalars_upperStar_upperStar_nearbyCycles_lowerShriek
      (Profinite.padicIntegersRingObjToResidueField ℓ E.1) M o e ι K₀
      (derivedUpperStarExtendScalarsPushHom _ M.j)
    -- the coefficient rings carry different proofs of `Precoherent Profinite`
    have k' := k (by transport_mod_proofs hφ) (by transport_mod_proofs h)
    transport_mod_proofs k'

omit [IsOpenImmersion ι] in
/-- Apply the coefficient-independent vanishing criterion with the two bounded-below
pushforward comparison theorems for a finite extension of the p-adics. -/
private lemma isZero_upperStar_upperStar_nearbyCycles_lowerShriek_padic_transfer
    [QuasiCompact M.j] [QuasiSeparated M.j]
    (K₀ : DerivedCategory (Mod (Sheaf (ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) U)))
    (n : ℤ) (hn : ((L((M.ε)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj
      (D((o)_!open⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj K₀)).IsGE n)
    (h : IsZero ((L((ι)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj
      (L((e)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj
        ((M.nearbyCycles (Profinite.padicIntegersRingObj ℓ E.1)).obj
          (D((o)_!open⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj K₀))))) :
    type_of% (isZero_upperStar_upperStar_nearbyCycles_lowerShriek_flat_composite
    (ht12 := by intros; infer_instance) (ht23 := by intros; infer_instance)
    (ht4 := by intros; infer_instance)
    (padicIntegersRingObjToContinuousMapRingObj ℓ E)
    (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) M o e ι K₀ n (by transport_mod_proofs hn)
    (fun K n hn ↦ by
      transport_mod_proofs (@isIso_derivedPushHom_app_padicIntegers_of_isGE ℓ
        ‹Fact ℓ.Prime› E M.generic M.total M.j ‹QuasiCompact M.j› ‹QuasiSeparated M.j› K n hn))
    (fun K n hn ↦ by
      transport_mod_proofs (@isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE ℓ
        ‹Fact ℓ.Prime› E M.generic M.total M.j ‹QuasiCompact M.j› ‹QuasiSeparated M.j› K n hn))
    (by transport_mod_proofs h)) :=
  isZero_upperStar_upperStar_nearbyCycles_lowerShriek_flat_composite
    (ht12 := by intros; infer_instance) (ht23 := by intros; infer_instance)
    (ht4 := by intros; infer_instance)
    (padicIntegersRingObjToContinuousMapRingObj ℓ E)
    (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) M o e ι K₀ n (by transport_mod_proofs hn)
    (fun K n hn ↦ by
      transport_mod_proofs (@isIso_derivedPushHom_app_padicIntegers_of_isGE ℓ
        ‹Fact ℓ.Prime› E M.generic M.total M.j ‹QuasiCompact M.j› ‹QuasiSeparated M.j› K n hn))
    (fun K n hn ↦ by
      transport_mod_proofs (@isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE ℓ
        ‹Fact ℓ.Prime› E M.generic M.total M.j ‹QuasiCompact M.j› ‹QuasiSeparated M.j› K n hn))
    (by transport_mod_proofs h)

-- Elaborating the statement compares the derived categories of the coefficient rings.
omit [IsOpenImmersion ι] in
/-- **Restricted nearby cycles of extensions by zero, from `𝒪_E` to `ℚ̄_ℓ`**: let `M` be a model
of `X` whose inclusion `j` of the geometric generic fibre is quasi-compact and quasi-separated,
`o : U ⟶ X` an open immersion, `e : Y ⟶ X'`, `ι : W ⟶ Y`, and `K₀` an `𝒪_E`-complex on `U` with
`Lε^* Do_! K₀` bounded below. If `Lι^* Le^* Ψ(Do_! K₀)` vanishes, so does
`Lι^* Le^* Ψ(Do_!(ℚ̄_ℓ ⊗ᴸ_E E ⊗ᴸ_{𝒪_E} K₀))`: all the functors commute with the extensions of
scalars, `Rj_*` on bounded below complexes. -/
theorem isZero_upperStar_upperStar_nearbyCycles_lowerShriek_padicAlgCl_of_padicIntegers
    [QuasiCompact M.j] [QuasiSeparated M.j]
    (K₀ : DerivedCategory (Mod (Sheaf (ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) U)))
    (n : ℤ) (hn : ((L((M.ε)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj
      (D((o)_!open⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj K₀)).IsGE n)
    (h : IsZero ((L((ι)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj
      (L((e)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj
        ((M.nearbyCycles (Profinite.padicIntegersRingObj ℓ E.1)).obj
          (D((o)_!open⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj K₀))))) :
    IsZero ((L((ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
      (L((e)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
        ((M.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
          (D((o)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).obj
            ((L(Mod.extendScalars
              (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) U))).obj
              ((L(Mod.extendScalars
                (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E) U))).obj
                K₀)))))) := by
  have key := isZero_upperStar_upperStar_nearbyCycles_lowerShriek_padic_transfer
    E M o e ι K₀ n hn h
  transport_mod_proofs key

end NearbyCyclesModel

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (k' : Type u) [Field k'] [Algebra k k']
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

-- Destructuring the finite-coefficient statement unfolds the coefficient rings.
open NearbyCyclesModel in
/-- **Generic vanishing along a divisor for `ℚ̄_ℓ`-coefficients, from finite coefficients**: let
`X` be normal, `Z = V(h)` for a nonzero global function `h`, `j : X ∖ Z ⟶ X` the complement, `ζ`
a generic point of an irreducible component of `Z`, and `N` a bounded constructible
`ℚ̄_ℓ`-complex on `X ∖ Z`. Then `Le^* Ψ_X(j_! N)` vanishes over a neighbourhood of `ζ`. This is
deduced from the case of `𝔽_E`-coefficients
(`exists_isZero_upperStar_nearbyCycles_lowerShriek_residueField`, unfinished) through an integral
model `N₀` of `N` and derived Nakayama. -/
theorem exists_isZero_upperStar_nearbyCycles_lowerShriek_padicAlgCl
    [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
    (hX : IsNormalScheme X.left) {h : Γ(X.left, ⊤)} (hh : h ≠ 0) {I : X.left.IdealSheafData}
    (hI : I = IdealSheafData.ofIdealTop (Ideal.span {h}))
    (ζ : (centre X I).left) (hζ : closure {ζ} ∈ irreducibleComponents (centre X I).left)
    (N : Dᵇc((overRestrict X I.support.compl).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ∃ U : (centre X I).left.Opens, ζ ∈ U ∧
      IsZero ((L((((constantSpecialFibreProj k' (centre X I)) ⁻¹ᵁ U).ι)^*⟦
        Profinite.padicAlgClRingObj ℓ⟧)).obj
        (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
          (((deformationModel X I k').nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
            ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
              (overRestrictι X I.support.compl)).obj N).obj))) := by
  -- Share the tensor properties of module categories across the derived functors below.
  have (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) Ab.{u + 1})
      [MonObj R] [IsCommMonObj R]
      (A B C : GradedObject ℤ (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) R)) :
      GradedObject.HasGoodTensor₁₂Tensor A B C := by infer_instance
  have (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) Ab.{u + 1})
      [MonObj R] [IsCommMonObj R]
      (A B C : GradedObject ℤ (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) R)) :
      GradedObject.HasGoodTensorTensor₂₃ A B C := by infer_instance
  have (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) Ab.{u + 1})
      [MonObj R] [IsCommMonObj R]
      (A B C D : GradedObject ℤ (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) R)) :
      GradedObject.HasTensor₄ObjExt A B C D := by infer_instance
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := {}
  have : IsLocallyNoetherian (overRestrict X I.support.compl).left :=
    LocallyOfFiniteType.isLocallyNoetherian (overRestrict X I.support.compl).hom
  have : CompactSpace (overRestrict X I.support.compl).left :=
    QuasiCompact.compactSpace_of_compactSpace (overRestrict X I.support.compl).hom
  have : IsNoetherian (overRestrict X I.support.compl).left := {}
  have : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  -- an integral model `N ≅ ℚ̄_ℓ ⊗ᴸ_E E ⊗ᴸ_{𝒪_E} N₀`
  refine (exists_padicAlgCl_iso_integralModel
    (overRestrict X I.support.compl).left ℓ N).elim fun E hE ↦ ?_
  refine hE.elim fun N₀ he ↦ ?_
  refine he.elim fun e ↦ ?_
  have hN₀ : boundedConstructible _ N₀.obj := by exact_mod_proofs N₀.property
  -- the finite-coefficient case, for the reduction of `N₀`
  have core := exists_isZero_upperStar_nearbyCycles_lowerShriek_residueField k' hX hh hI ζ hζ E
    ((L(Mod.extendScalars (coefficientMap (Profinite.padicIntegersRingObjToResidueField ℓ E.1)
      (overRestrict X I.support.compl).left))).obj N₀.obj)
  have hF' : boundedConstructible _ ((L(Mod.extendScalars
      (coefficientMap (Profinite.padicIntegersRingObjToResidueField ℓ E.1)
        (overRestrict X I.support.compl).left))).obj N₀.obj) :=
    boundedConstructible_derivedExtendScalars_residueField _ ℓ E N₀.obj hN₀
  refine (core hF').elim fun U hU ↦ ?_
  refine ⟨U, hU.1, ?_⟩
  have hU := hU.2
  -- the integral case, by derived Nakayama
  have hK := boundedConstructible_openImmersionLowerShriek_obj _ ℓ
    (overRestrictι X I.support.compl) ⟨N₀.obj, hN₀⟩
  refine hK.1.1.elim fun n hn ↦ ?_
  have hn' := isGE_leftDerivedUpperStar_obj (Profinite.padicIntegersRingObj ℓ E.1)
    (deformationModel X I k').ε
    (D(((overRestrictι X I.support.compl).left)_!open⟦
      Profinite.padicIntegersRingObj ℓ E.1⟧).obj N₀.obj) n
  have h₀ := isZero_upperStar_upperStar_nearbyCycles_lowerShriek_padicIntegers_of_residueField
    E (deformationModel X I k') (overRestrictι X I.support.compl).left
    (zeroSectionSpecialFibreMap X I k').left
    (((constantSpecialFibreProj k' (centre X I)) ⁻¹ᵁ U).ι) N₀.obj
    (derivedCompleteIntegers_of_boundedConstructible hK) n hn' (by transport_mod_proofs hU)
  -- from `𝒪_E` to `ℚ̄_ℓ`
  have h₁ := isZero_upperStar_upperStar_nearbyCycles_lowerShriek_padicAlgCl_of_padicIntegers
    E (deformationModel X I k') (overRestrictι X I.support.compl).left
    (zeroSectionSpecialFibreMap X I k').left
    (((constantSpecialFibreProj k' (centre X I)) ⁻¹ᵁ U).ι) N₀.obj n hn' h₀
  refine h₁.of_iso ?_
  exact (D(((overRestrictι X I.support.compl).left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙
    (deformationModel X I k').nearbyCycles (Profinite.padicAlgClRingObj ℓ) ⋙
    L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙
    L((((constantSpecialFibreProj k' (centre X I)) ⁻¹ᵁ U).ι)^*⟦
      Profinite.padicAlgClRingObj ℓ⟧)).mapIso
      ((ObjectProperty.ι _).mapIso e).symm

end AlgebraicGeometry.ProEtale.CondensedRing
