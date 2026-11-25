/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraTwist
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.HomologyCoherence
public import WeilConjectures.TraceFormula.CompactPullback
public import WeilConjectures.TraceFormula.WeilTrace

/-!
# Weil objects with the identity structure

Let `X` be a separated scheme of finite type over `Spec k`. Every object `A` of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` is
a Weil object for the identity of `X`, with the identity isomorphism `L(𝟙 X)^* A ≅ A` as
structure isomorphism (`ProEtale.CondensedRing.WeilBoundedConstructible.ofId`), and likewise every
module object `M` is a Weil sheaf for the identity, with `(𝟙 X)^* M ≅ M`
(`ProEtale.CondensedRing.WeilSheaf.ofId`). These structures are preserved by the operations of
the trace formula chapter:

- the homology sheaves of `ofId A` are the Weil sheaves `ofId Hⁿ(A)`
  (`ProEtale.CondensedRing.WeilBoundedConstructible.homologyFunctorOfIdIso`), by the
  compatibility of the derived pullback along `𝟙 X` with homology
  (`ProEtale.CondensedRing.leftDerivedUpperStarHomologyIso_hom_app_id`);
- the compactly supported cohomology of `ofId A` is `ofId (Ra_! A)`
  (`ProEtale.CondensedRing.weilCompactSupportCohomologyOfIdIso`), the base change along the trivial
  square being the identity (`boundedConstructibleUpperStarId_inv_app_comp_baseChange_app`).
-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]

section Sheaf

variable {X : Over (Spec (.of k))}

/-- A module object `M` on `X` as a Weil sheaf for the identity of `X`, with the identity
isomorphism `(𝟙 X)^* M ≅ M` as structure isomorphism. -/
noncomputable def WeilSheaf.ofId
    (M : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)) :
    WeilSheaf ℓ (Iso.refl X) :=
  IsoAlgebra.mk M ((upperStarId (Profinite.padicAlgClRingObj ℓ) X.left).app M)

/-- An isomorphism of module objects is an isomorphism of the Weil sheaves with the identity
structure. -/
noncomputable def WeilSheaf.ofIdMapIso
    {M M' : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)} (u : M ≅ M') :
    WeilSheaf.ofId ℓ M ≅ WeilSheaf.ofId ℓ M' :=
  IsoAlgebra.isoMk u ((upperStarId (Profinite.padicAlgClRingObj ℓ) X.left).hom.naturality u.hom)

end Sheaf

variable [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- An object `A` of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` as a Weil object for the identity of `X`, with the identity
isomorphism `L(𝟙 X)^* A ≅ A` as structure isomorphism. -/
noncomputable def WeilBoundedConstructible.ofId (A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    WeilBoundedConstructible ℓ (Iso.refl X).hom :=
  IsoAlgebra.mk A ((boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).app A)

/-- The structure isomorphism of `ofId A` is the identity isomorphism `L(𝟙 X)^* A ≅ A`. -/
lemma WeilBoundedConstructible.ofId_str (A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (WeilBoundedConstructible.ofId ℓ A).str =
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).app A :=
  IsoAlgebra.mk_str _ _

/-- The Weil structure of the `n`-th homology sheaf of `ofId A` is the identity isomorphism
`(𝟙 X)^* Hⁿ(A) ≅ Hⁿ(A)`. -/
lemma WeilBoundedConstructible.homologyFunctor_obj_ofId_str_hom (n : ℤ)
    (A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((WeilBoundedConstructible.homologyFunctor ℓ (Iso.refl X) n).obj
        (WeilBoundedConstructible.ofId ℓ A)).str.hom =
      (upperStarId (Profinite.padicAlgClRingObj ℓ) X.left).hom.app
        ((DerivedCategory.homologyFunctor _ n).obj A.obj) := by
  have h := leftDerivedUpperStarHomologyIso_hom_app_id (Profinite.padicAlgClRingObj ℓ) X.left n
    A.obj
  simp only [leftDerivedUpperStarHomologyIso, Functor.leftDerivedFunctorHomologyFunctorIso,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Iso.symm_hom, Category.assoc] at h
  rw [WeilBoundedConstructible.homologyFunctor_obj_str, WeilBoundedConstructible.ofId_str,
    Iso.trans_hom, Iso.app_hom, weilHomologyComparison_hom_app, Functor.mapIso_hom, Iso.app_hom,
    Functor.comp_map, ObjectProperty.ι_map, boundedConstructibleUpperStarId_hom_app_hom,
    Category.assoc]
  simp only [Iso.refl_hom, Over.id_left]
  exact h

/-- The `n`-th homology sheaf of the Weil object `ofId A` is the Weil sheaf `ofId Hⁿ(A)`. -/
noncomputable def WeilBoundedConstructible.homologyFunctorOfIdIso (n : ℤ)
    (A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (WeilBoundedConstructible.homologyFunctor ℓ (Iso.refl X) n).obj
        (WeilBoundedConstructible.ofId ℓ A) ≅
      WeilSheaf.ofId ℓ ((DerivedCategory.homologyFunctor _ n).obj A.obj) :=
  IsoAlgebra.isoMk (Iso.refl _) (by
    refine (congrArg (· ≫ _) (CategoryTheory.Functor.map_id _ _)).trans ?_
    rw [Category.id_comp]
    exact (homologyFunctor_obj_ofId_str_hom ℓ n A).symm.trans (Category.comp_id _).symm)

/-- The Weil structure of the compactly supported cohomology of a Weil object, unfolded. -/
lemma weilCompactSupportCohomology_obj_str (e : X ≅ X) (K : WeilBoundedConstructible ℓ e.hom) :
    ((weilCompactSupportCohomology ℓ e).obj K).str =
      (weilLowerShriekComparison ℓ e (Iso.refl (point k)) (toPoint_ext _ _)).app K.carrier ≪≫
        (boundedConstructibleLowerShriek ℓ (toPoint X)).mapIso K.str :=
  weilLowerShriek_obj_str ℓ e (Iso.refl (point k)) (toPoint_ext _ _) K

/-- The Weil structure of the compactly supported cohomology of `ofId A` is the identity
isomorphism of `Ra_! A`: the compact-support base change along the trivial square is the
identity, up to the identity isomorphisms of the pullbacks. -/
lemma weilCompactSupportCohomology_obj_ofId_str_hom
    (A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((weilCompactSupportCohomology ℓ (Iso.refl X)).obj
        (WeilBoundedConstructible.ofId ℓ A)).str.hom =
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ (point k)).hom.app
        ((boundedConstructibleLowerShriek ℓ (toPoint X)).obj A) := by
  have h := boundedConstructibleUpperStarId_inv_app_comp_baseChange_app ℓ
    (weilFrobeniusSquare (Iso.refl X) (Iso.refl (point k)) (toPoint_ext _ _)) A
  rw [weilCompactSupportCohomology_obj_str, WeilBoundedConstructible.ofId_str, Iso.trans_hom,
    Iso.app_hom, weilLowerShriekComparison_hom, Functor.mapIso_hom, Iso.app_hom,
    ← cancel_epi ((boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ
      (point k)).inv.app ((boundedConstructibleLowerShriek ℓ (toPoint X)).obj A)),
    Iso.inv_hom_id_app, ← Category.assoc]
  erw [h]
  rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  rfl

/-- The compactly supported cohomology of the Weil object `ofId A` is the Weil object
`ofId (Ra_! A)` on the base. -/
noncomputable def weilCompactSupportCohomologyOfIdIso
    (A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (weilCompactSupportCohomology ℓ (Iso.refl X)).obj (WeilBoundedConstructible.ofId ℓ A) ≅
      WeilBoundedConstructible.ofId ℓ ((boundedConstructibleLowerShriek ℓ (toPoint X)).obj A) :=
  IsoAlgebra.isoMk (Iso.refl _) (by
    refine (congrArg (· ≫ _) (CategoryTheory.Functor.map_id _ _)).trans ?_
    rw [Category.id_comp]
    exact (weilCompactSupportCohomology_obj_ofId_str_hom ℓ A).symm.trans
      (Category.comp_id _).symm)

section Trace

variable [Finite k] (n : ℕ) (x : Spec (.of (AlgebraicClosure k)) ⟶ X.left)
  (hx : x ≫ ((Iso.refl X).pow n).hom.left = ((geometricFrobeniusField k).pow n).hom ≫ x)

/-- The local trace of the Weil object `ofId A` for `A` concentrated in degree `0` is the trace of
the Frobenius on the stalk of the Weil sheaf `ofId H⁰(A)`. -/
lemma weilStalkTraceAlternatingSum_ofId_of_isZero
    (A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hA : ∀ i ≠ 0, Limits.IsZero ((DerivedCategory.homologyFunctor _ i).obj A.obj)) :
    weilStalkTraceAlternatingSum ℓ n x hx (WeilBoundedConstructible.ofId ℓ A) =
      weilSheafStalkTrace ℓ n x hx
        (WeilSheaf.ofId ℓ ((DerivedCategory.homologyFunctor _ 0).obj A.obj)) := by
  rw [weilStalkTraceAlternatingSum]
  refine (finsum_eq_single _ 0 fun j hj ↦ ?_).trans ?_
  · refine smul_eq_zero_of_right _ (traceOrZero_eq_zero_of_isZero ?_ _)
    rw [Functor.id_obj, WeilSheaf.frobeniusStalk, WeilSheaf.powStalkFunctor, Functor.comp_obj,
      WeilSheaf.stalkFunctor_obj_carrier, WeilSheaf.powFunctor_obj, WeilSheaf.pow_carrier]
    exact Functor.map_isZero _ (hA j hj)
  · rw [Int.negOnePow_zero, Units.val_one, one_smul]
    exact weilSheafStalkTrace_congr ℓ n x hx
      (WeilBoundedConstructible.homologyFunctorOfIdIso ℓ 0 A)

end Trace

end AlgebraicGeometry.ProEtale.CondensedRing
