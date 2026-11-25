/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.WeilIdentityStructure
public import WeilConjectures.TraceFormula.WeilIdentityStalk

/-!
# Local traces of Weil objects with structure through the identity

The local alternating trace of a Weil object for the identity, concentrated in degree zero, whose
structure is `(𝟙)^* ≅ 𝟭` followed by an endomorphism, is the trace of the Galois action on
its zeroth cohomology sheaf.
-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

lemma weilHomologyComparison_hom_app_comp_map_boundedConstructibleUpperStarId
    (C : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (n : ℤ) :
    (weilHomologyComparison ℓ (Iso.refl X) n).hom.app C ≫
        ((boundedConstructible _).ι ⋙ DerivedCategory.homologyFunctor _ n).map
          ((boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).hom.app C) =
      (upperStarId (Profinite.padicAlgClRingObj ℓ) X.left).hom.app
        (((boundedConstructible _).ι ⋙ DerivedCategory.homologyFunctor _ n).obj C) := by
  rw [weilHomologyComparison_hom_app, Functor.comp_map, ObjectProperty.ι_map,
    boundedConstructibleUpperStarId_hom_app_hom, Category.assoc, ← Functor.map_comp]
  have h := leftDerivedUpperStarHomologyIso_hom_app_id _ X.left n C.obj
  simp only [leftDerivedUpperStarHomologyIso, Functor.leftDerivedFunctorHomologyFunctorIso,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Iso.symm_hom, Category.assoc] at h
  rw [Functor.map_comp]
  exact h

theorem WeilBoundedConstructible.homologyFunctor_obj_str_hom_of_id_comp
    (K : WeilBoundedConstructible ℓ (Iso.refl X).hom) (β : K.carrier ⟶ K.carrier)
    (hK : K.str.hom =
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).hom.app K.carrier
          ≫ β)
    (n : ℤ) :
    ((WeilBoundedConstructible.homologyFunctor ℓ (Iso.refl X) n).obj K).str.hom =
      (upperStarId (Profinite.padicAlgClRingObj ℓ) X.left).hom.app
        ((WeilBoundedConstructible.homologyFunctor ℓ (Iso.refl X) n).obj K).carrier ≫
        ((boundedConstructible _).ι ⋙ DerivedCategory.homologyFunctor _ n).map β := by
  rw [WeilBoundedConstructible.homologyFunctor_obj_str, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, hK, Functor.map_comp, ← Category.assoc,
    weilHomologyComparison_hom_app_comp_map_boundedConstructibleUpperStarId]
  rfl

/-- Weil sheaves for the identity whose structures are `(𝟙)^* ≅ 𝟭` followed by endomorphisms
intertwined by an isomorphism of the underlying module objects are isomorphic. -/
noncomputable def WeilSheaf.isoOfUpperStarIdComp {F G : WeilSheaf ℓ (Iso.refl X)}
    (βF : F.carrier ⟶ F.carrier) (βG : G.carrier ⟶ G.carrier)
    (hF : F.str.hom = (upperStarId (Profinite.padicAlgClRingObj ℓ) X.left).hom.app F.carrier ≫
        βF)
    (hG : G.str.hom = (upperStarId (Profinite.padicAlgClRingObj ℓ) X.left).hom.app G.carrier ≫
        βG)
    (e : F.carrier ≅ G.carrier) (he : βF ≫ e.hom = e.hom ≫ βG) : F ≅ G :=
  IsoAlgebra.isoMk e (by
    have n := (upperStarId (Profinite.padicAlgClRingObj ℓ) X.left).hom.naturality e.hom
    rw [Functor.id_map] at n
    rw [← IsoAlgebra.str_hom, ← IsoAlgebra.str_hom, hF, hG]
    erw [reassoc_of% n]
    rw [Category.assoc, he])

/-- A Weil sheaf for the identity whose structure is `(𝟙)^* ≅ 𝟭` followed by an
    endomorphism is
isomorphic to `(A,
(𝟙)^* ≅ 𝟭 ≫ β)` for an isomorphism of the carrier with `A` intertwining the
endomorphisms. -/
noncomputable def WeilSheaf.isoMkOfUpperStarIdComp {F : WeilSheaf ℓ (Iso.refl X)}
    (βF : F.carrier ⟶ F.carrier)
    (hF : F.str.hom = (upperStarId (Profinite.padicAlgClRingObj ℓ) X.left).hom.app F.carrier ≫
        βF)
    (A : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left))
    (Φ : ((Iso.refl X).hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj A ≅ A) (βA : A ⟶
        A)
    (hΦ : Φ.hom = (upperStarId (Profinite.padicAlgClRingObj ℓ) X.left).hom.app A ≫ βA)
    (e : F.carrier ≅ A) (he : βF ≫ e.hom = e.hom ≫ βA) : F ≅ IsoAlgebra.mk A Φ :=
  IsoAlgebra.isoMk e (by
    have n := (upperStarId (Profinite.padicAlgClRingObj ℓ) X.left).hom.naturality e.hom
    rw [Functor.id_map] at n
    rw [← IsoAlgebra.str_hom, ← IsoAlgebra.str_hom, IsoAlgebra.mk_str, hF, hΦ]
    erw [reassoc_of% n]
    rw [Category.assoc, he])

variable [Finite k]

theorem weilStalkTraceAlternatingSum_eq_traceOrZero_of_homology
    (K : WeilBoundedConstructible ℓ (Iso.refl X).hom) (βK : K.carrier ⟶ K.carrier)
    (hK : K.str.hom =
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).hom.app K.carrier
          ≫ βK)
    (hvan : ∀ j : ℤ, j ≠ 0 →
      Limits.IsZero (((boundedConstructible _).ι ⋙ DerivedCategory.homologyFunctor _ j).obj
        K.carrier))
    (A : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left))
    (ι : ((boundedConstructible _).ι ⋙ DerivedCategory.homologyFunctor _ 0).obj K.carrier ≅ A)
    (β : A ≅ A)
    (hβ : ((boundedConstructible _).ι ⋙ DerivedCategory.homologyFunctor _ 0).map βK ≫
        ι.hom =
      ι.hom ≫ β.hom) (n : ℕ)
    (x : Spec (.of (AlgebraicClosure k)) ⟶ X.left)
    (hx : x ≫ ((Iso.refl X).pow (n + 1)).hom.left =
      ((geometricFrobeniusField k).pow (n + 1)).hom ≫ x) :
    weilStalkTraceAlternatingSum ℓ (n + 1) x hx K =
      weilSheafStalkTrace ℓ (n + 1) x hx (IsoAlgebra.mk A ((upperStarIsoIdOfEq ℓ
        (by rw [Iso.refl_hom,
            Over.id_left] : (Iso.refl X).hom.left = 𝟙 X.left)).app A ≪≫ β) :
          WeilSheaf ℓ (Iso.refl X)) := by
  have hF := WeilBoundedConstructible.homologyFunctor_obj_str_hom_of_id_comp ℓ K βK hK 0
  have hΦ : ((upperStarIsoIdOfEq ℓ
      (by rw [Iso.refl_hom,
          Over.id_left] : (Iso.refl X).hom.left = 𝟙 X.left)).app A ≪≫ β).hom =
      (upperStarId (Profinite.padicAlgClRingObj ℓ) X.left).hom.app A ≫ β.hom := by
    rw [Iso.trans_hom, Iso.app_hom, upperStarIsoIdOfEq_refl_hom_app]
  have hc := weilSheafStalkTrace_congr ℓ (n + 1) x hx
      (WeilSheaf.isoMkOfUpperStarIdComp ℓ _ hF A _ β.hom hΦ ι hβ)
  rw [weilStalkTraceAlternatingSum, finsum_eq_single _ 0 (fun j hj ↦ ?_), Int.negOnePow_zero,
    Units.val_one, one_smul, hc]
  refine smul_eq_zero_of_right _ (traceOrZero_eq_zero_of_isZero ?_ _)
  rw [Functor.id_obj, WeilSheaf.frobeniusStalk, WeilSheaf.powStalkFunctor, Functor.comp_obj,
    WeilSheaf.stalkFunctor_obj_carrier, WeilSheaf.powFunctor_obj, WeilSheaf.pow_carrier,
    WeilBoundedConstructible.homologyFunctor_obj_carrier]
  exact Functor.map_isZero _ (hvan j hj)

end AlgebraicGeometry.ProEtale.CondensedRing
