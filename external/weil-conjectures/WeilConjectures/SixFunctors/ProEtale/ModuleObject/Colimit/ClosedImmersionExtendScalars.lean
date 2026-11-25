/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleClosedPushforward

/-!
# Closed pushforward and extension of scalars

Let `Λ` be a commutative condensed ring, `i : Z ⟶ X` a closed immersion and `j : U ⟶ X` a
quasi-compact open immersion onto its complement. This file proves, without the bounded
constructible six functor formalism of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` (which depends
on the present file through the descent of constructible complexes), that for a flat coefficient
change `a : Λ ⟶ Λ'` the extension of scalars commutes with `Ri_*`:
`T^X (Ri_* N) ≅ Ri_* (T^Z N)`
(`ProEtale.CondensedRing.derivedExtendScalarsLowerStarIsoOfIsClosedImmersion`). Indeed
`Lj^* T^X (Ri_* N) ≅ T^U (Lj^* Ri_* N) = 0` by (Pull), so `T^X (Ri_* N)` is supported on `Z`
(`ProEtale.CondensedRing.isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isZero`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The derived extension of scalars along a flat coefficient change preserves zero objects,
being isomorphic to the levelwise functor. -/
lemma isZero_leftDerivedExtendScalars_obj
    {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X : Scheme.{u}}
    [PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (hK : IsZero K) :
    IsZero ((L(Mod.extendScalars (coefficientMap a X))).obj K) :=
  (Functor.map_isZero (Mod.extendScalars (coefficientMap a X)).mapDerivedCategory hK).of_iso
    ((Functor.leftDerivedFunctorIsoMapDerivedCategory _).app K)

-- Unifying the instance arguments of the derived extensions of scalars appearing in (Pull) with
-- those of the statement is slow.
/-- For a flat coefficient change `a : Λ ⟶ Λ'` and a closed immersion `i : Z ⟶ X` with
quasi-compact open complement (e.g. `X` with noetherian underlying space), the extension of
scalars commutes with the derived pushforward: `T^X (Ri_* N) ≅ Ri_* (T^Z N)`. The complex
`T^X (Ri_* N)` restricts to `T^U (Lj^* Ri_* N) = 0` on the complement by (Pull), so it is
`Ri_* Li^* T^X (Ri_* N) ≅ Ri_* T^Z (Li^* Ri_* N) ≅ Ri_* T^Z N`. -/
noncomputable def derivedExtendScalarsLowerStarIsoOfIsClosedImmersion
    {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a]
    [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]
    {Z X : Scheme.{u}} [TopologicalSpace.NoetherianSpace X] (i : Z ⟶ X) [IsClosedImmersion i]
    (N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) :
    (L(Mod.extendScalars (coefficientMap a X))).obj ((R((i)_*⟦Λ⟧)).obj N) ≅
      (R((i)_*⟦Λ'⟧)).obj ((L(Mod.extendScalars (coefficientMap a Z))).obj N) :=
  let U : X.Opens := ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  haveI : TopologicalSpace.NoetherianSpace U := U.ι.isOpenEmbedding.isInducing.noetherianSpace
  haveI : QuasiCompact U.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hc : IsCompl (Set.range i.base) (Set.range U.ι.base) := by
    rw [Scheme.Opens.range_ι U]
    exact isCompl_compl
  let M := (R((i)_*⟦Λ⟧)).obj N
  let TM := (L(Mod.extendScalars (coefficientMap a X))).obj M
  have h0 : IsZero ((L((U.ι)^*⟦Λ'⟧)).obj TM) :=
    (isZero_leftDerivedExtendScalars_obj Λ a
      (isZero_leftDerivedUpperStar_obj_rightDerivedLowerStar_obj_of_disjoint
        Λ U.ι i hc.symm.disjoint N)).of_iso ((derivedPullIso a U.ι).app M).symm
  have hη := isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isZero Λ' U.ι i hc h0
  (@asIso _ _ _ _ ((derivedUpperStarLowerStarAdjunction Λ' i).unit.app TM) hη).trans
    ((R((i)_*⟦Λ'⟧)).mapIso (((derivedPullIso a i).app M).symm.trans
      ((L(Mod.extendScalars (coefficientMap a Z))).mapIso
        (asIso ((derivedUpperStarLowerStarAdjunction Λ i).counit.app N)))))

end AlgebraicGeometry.ProEtale.CondensedRing
