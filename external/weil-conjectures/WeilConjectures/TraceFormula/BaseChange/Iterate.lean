/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.HomologyCoherence
public import WeilConjectures.TraceFormula.WeilTrace

/-!

# Iterated Weil structures of Weil complexes and of their homology sheaves

Let `e : X ≅ X` be an automorphism of a scheme over `Spec k` and `(K, φ)` a Weil object of
`Dᵇc(X)⟦ℚ̲̄_ℓ⟧` for `e`. Its iterate `(K, φ^{(n+1)})`
(`ProEtale.CondensedRing.WeilBoundedConstructible.powSucc`) is a Weil object for `e^{n+1}`, with
the iterated structure isomorphism `Iso.powSuccStr` of the derived pullbacks, as for Weil sheaves
(`ProEtale.CondensedRing.WeilSheaf.pow`). The homology sheaves of the iterate are the
iterates of the homology sheaves
(`ProEtale.CondensedRing.WeilBoundedConstructible.homologyPowSuccIso`): the commutation of the
homology sheaves with the derived pullbacks is compatible with the composition isomorphisms
(`ProEtale.CondensedRing.leftDerivedUpperStarHomologyIso_comp_hom_app`).

The general statement is `CategoryTheory.Iso.powSuccStr_hom_eq_of_comp`: a functor `H` with
commutation isomorphisms `H ⋙ Q g ≅ P g ⋙ H` compatible with the composition isomorphisms
commutes with the iterated structure isomorphisms.

## Main definitions

- `ProEtale.CondensedRing.WeilBoundedConstructible.powSucc`: the iterate `(K, φ^{(n+1)})`.
- `ProEtale.CondensedRing.weilHomologyComparisonOfHom`: the commutation `Hʲ ⋙ g^* ≅ Lg^* ⋙ Hʲ`
  for an endomorphism `g`.

## Main results

- `ProEtale.CondensedRing.WeilBoundedConstructible.homologyPowSuccIso`:
  `(Hʲ(K), φ_{Hʲ(K)}^{(n+1)}) ≅ Hʲ(K, φ^{(n+1)})` as Weil sheaves for `e^{n+1}`, from the
  general `CategoryTheory.Iso.mapOfNatIsoPowSuccIso`.

-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Iso

variable {C : Type*} [Category C] {X : C} (e : X ≅ X) {D E : Type*} [Category D] [Category E]

/-- A functor `H : D ⥤ E` commutes with the iterated structure isomorphisms: let `P g` and
`Q g` be families of endofunctors of `D` and `E` indexed by the endomorphisms `g` of `X`, with
composition isomorphisms, and let `h g : H ⋙ Q g ≅ P g ⋙ H` be compatible with them. Then the
iterated structure isomorphism of `(h e).app a ≪≫ H.mapIso φ` is
`(h e^{n+1}).app a ≫ H (φ^{(n+1)})`. -/
theorem powSuccStr_hom_eq_of_comp (P : (X ⟶ X) → D ⥤ D)
    (compP : ∀ f g : X ⟶ X, P (f ≫ g) ≅ P g ⋙ P f) (Q : (X ⟶ X) → E ⥤ E)
    (compQ : ∀ f g : X ⟶ X, Q (f ≫ g) ≅ Q g ⋙ Q f) (H : D ⥤ E)
    (h : ∀ g : X ⟶ X, H ⋙ Q g ≅ P g ⋙ H)
    (hcomp : ∀ (f g : X ⟶ X) (a : D), (h (f ≫ g)).hom.app a ≫ H.map ((compP f g).hom.app a) =
      (compQ f g).hom.app (H.obj a) ≫ (Q f).map ((h g).hom.app a) ≫
        (h f).hom.app ((P g).obj a))
    {a : D} (φ : (P e.hom).obj a ≅ a) (n : ℕ) :
    (e.powSuccStr Q compQ ((h e.hom).app a ≪≫ H.mapIso φ) n).hom =
      (h (e.pow (n + 1)).hom).hom.app a ≫ H.map (e.powSuccStr P compP φ n).hom := by
  induction n with
  | zero =>
    have key : ∀ (g g' : X ⟶ X) (hg : g = g'),
        eqToHom (congrArg (fun g ↦ (Q g).obj (H.obj a)) hg) ≫ (h g').hom.app a =
          (h g).hom.app a ≫ H.map (eqToHom (congrArg (fun g ↦ (P g).obj a) hg)) := by
      rintro g _ rfl
      simp
    rw [powSuccStr_zero, powSuccStr_zero]
    simp only [Iso.trans_hom, eqToIso.hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp]
    exact (reassoc_of% key _ _ (Category.id_comp e.hom)) _
  | succ n ih =>
    change (compQ (e.pow (n + 1)).hom e.hom).hom.app (H.obj a) ≫
        (Q (e.pow (n + 1)).hom).map ((h e.hom).hom.app a ≫ H.map φ.hom) ≫
          (e.powSuccStr Q compQ ((h e.hom).app a ≪≫ H.mapIso φ) n).hom =
      (h ((e.pow (n + 1)).hom ≫ e.hom)).hom.app a ≫
        H.map ((compP (e.pow (n + 1)).hom e.hom).hom.app a ≫ (P (e.pow (n + 1)).hom).map φ.hom ≫
          (e.powSuccStr P compP φ n).hom)
    have nat := (h (e.pow (n + 1)).hom).hom.naturality φ.hom
    simp only [Functor.comp_map] at nat
    rw [ih, Functor.map_comp_assoc, reassoc_of% nat, Functor.map_comp, Functor.map_comp,
      reassoc_of% (hcomp (e.pow (n + 1)).hom e.hom a)]

/-- The transport along `H` of the iterate of an algebra is the iterate of its transport: for an
algebra `(a, φ)` for `P e`, the iterate for `Q e^{n+1}` of `(H a, (h e).app a ≪≫ H φ)` is
isomorphic, through the identity of `H a`, to the transport
`(H a, (h e^{n+1}).app a ≪≫ H φ^{(n+1)})`
of the iterate `(a, φ^{(n+1)})` (`powSuccStr_hom_eq_of_comp`). -/
noncomputable def mapOfNatIsoPowSuccIso (P : (X ⟶ X) → D ⥤ D)
    (compP : ∀ f g : X ⟶ X, P (f ≫ g) ≅ P g ⋙ P f) (Q : (X ⟶ X) → E ⥤ E)
    (compQ : ∀ f g : X ⟶ X, Q (f ≫ g) ≅ Q g ⋙ Q f) (H : D ⥤ E)
    (h : ∀ g : X ⟶ X, H ⋙ Q g ≅ P g ⋙ H)
    (hcomp : ∀ (f g : X ⟶ X) (a : D), (h (f ≫ g)).hom.app a ≫ H.map ((compP f g).hom.app a) =
      (compQ f g).hom.app (H.obj a) ≫ (Q f).map ((h g).hom.app a) ≫
        (h f).hom.app ((P g).obj a))
    (A : IsoAlgebra (P e.hom)) (n : ℕ) :
    IsoAlgebra.mk ((IsoAlgebra.mapOfNatIso (h e.hom)).obj A).carrier
        (e.powSuccStr Q compQ ((IsoAlgebra.mapOfNatIso (h e.hom)).obj A).str n) ≅
      (IsoAlgebra.mapOfNatIso (h (e.pow (n + 1)).hom)).obj
        (IsoAlgebra.mk A.carrier (e.powSuccStr P compP A.str n)) :=
  IsoAlgebra.isoMk (Iso.refl _) (by
    rw [Iso.refl_hom, Functor.map_id, Category.id_comp, Category.comp_id, ← IsoAlgebra.str_hom,
      ← IsoAlgebra.str_hom, IsoAlgebra.mk_str, IsoAlgebra.mapOfNatIso_obj_str]
    exact (powSuccStr_hom_eq_of_comp e P compP Q compQ H h hcomp A.str n).symm)

end CategoryTheory.Iso

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-! ### The iterated Weil structure -/

namespace WeilBoundedConstructible

variable {e : X ≅ X}

/-- The iterate `(K, φ^{(n+1)})` of a Weil object `(K, φ)` for an automorphism `e`: a Weil object
for `e^{n+1}`, with the iterated structure isomorphism `Iso.powSuccStr` of the derived pullbacks,
`φ^{(1)} = φ` and `φ^{(n+2)} : L(e^{n+1} ≫ e)^* K ≅ L(e^{n+1})^* Le^* K ≅ L(e^{n+1})^* K ≅ K`. -/
noncomputable abbrev powSucc (K : WeilBoundedConstructible ℓ e.hom) (n : ℕ) :
    WeilBoundedConstructible ℓ (e.pow (n + 1)).hom :=
  IsoAlgebra.mk K.carrier
    (e.powSuccStr (fun g ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g)
      (fun f g ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f g) K.str n)

end WeilBoundedConstructible

/-! ### Homology sheaves of the iterates -/

section Homology

variable (n : ℤ)

/-- The commutation `Hⁿ ⋙ g^* ≅ Lg^* ⋙ Hⁿ` of the homology sheaves with the derived pullback along
an endomorphism `g`, as in `weilHomologyComparison` (which is the case of an automorphism). -/
noncomputable def weilHomologyComparisonOfHom (g : X ⟶ X) :
    ((boundedConstructible _).ι ⋙ DerivedCategory.homologyFunctor _ n) ⋙
        (g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ≅
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g ⋙
        ((boundedConstructible _).ι ⋙ DerivedCategory.homologyFunctor _ n) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (leftDerivedUpperStarHomologyIso _ g.left n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleUpperStarCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ g).symm _ ≪≫
    Functor.associator _ _ _

lemma weilHomologyComparison_eq (e : X ≅ X) :
    weilHomologyComparison ℓ e n = weilHomologyComparisonOfHom ℓ n e.hom :=
  rfl

lemma weilHomologyComparisonOfHom_hom_app (g : X ⟶ X)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (weilHomologyComparisonOfHom ℓ n g).hom.app K =
      (leftDerivedUpperStarHomologyIso _ g.left n).hom.app K.obj := by
  simp only [weilHomologyComparisonOfHom, Iso.trans_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Iso.symm_hom,
    boundedConstructibleUpperStarCompatibility, ObjectProperty.liftCompιIso, Iso.refl_inv,
    NatTrans.id_app, Category.id_comp, Category.comp_id]
  exact (congrArg _ (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)

/-- The composition isomorphism `(f ≫ g)^* ≅ g^* ⋙ f^*` of the pullbacks of module objects for
morphisms `f`, `g` over a base, with the source written as the pullback along `(f ≫ g).left`.
It is `upperStarComp f.left g.left`; stating it with `(f ≫ g).left` keeps the kernel from
unfolding the pullbacks when comparing `(f ≫ g).left` with `f.left ≫ g.left`. -/
noncomputable def upperStarCompOver (f g : X ⟶ X) :
    ((f ≫ g).left)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ≅
      (g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ⋙ (f.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  upperStarComp _ f.left g.left

/-- The composition isomorphism `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` of the derived pullbacks, with the
source written as the derived pullback along `(f ≫ g).left` (see `upperStarCompOver`). -/
noncomputable def leftDerivedUpperStarCompOver (f g : X ⟶ X) :
    L(((f ≫ g).left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ≅
      L((g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙ L((f.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  Functor.leftDerivedFunctorFactorIso (upperStarCompOver ℓ f g)

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] in
/-- The commutation of the homology sheaves with the derived pullbacks is compatible with the
composition isomorphisms `leftDerivedUpperStarCompOver` and `upperStarCompOver`. -/
lemma leftDerivedUpperStarHomologyIso_compOver_hom_app (f g : X ⟶ X)
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left))) :
    (leftDerivedUpperStarHomologyIso _ (f ≫ g).left n).hom.app M ≫
        (DerivedCategory.homologyFunctor _ n).map ((leftDerivedUpperStarCompOver ℓ f g).hom.app M) =
      (upperStarCompOver ℓ f g).hom.app ((DerivedCategory.homologyFunctor _ n).obj M) ≫
        (f.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map
          ((leftDerivedUpperStarHomologyIso _ g.left n).hom.app M) ≫
        (leftDerivedUpperStarHomologyIso _ f.left n).hom.app
          (L((g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj M) :=
  Functor.leftDerivedFunctorHomologyFunctorIso_factorIso (upperStarCompOver ℓ f g) n M

/-- On the ambient derived category, the composition isomorphism of the derived pullbacks on
bounded constructible complexes is `leftDerivedUpperStarCompOver`. -/
lemma boundedConstructibleUpperStarComp_hom_app_hom' (f g : X ⟶ X)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f g).hom.app K).hom =
      (leftDerivedUpperStarCompOver ℓ f g).hom.app K.obj :=
  boundedConstructibleUpperStarComp_hom_app_hom _ ℓ f g K

/-- The commutation of the homology sheaves with the derived pullbacks is compatible with the
composition isomorphisms. -/
lemma weilHomologyComparisonOfHom_comp (f g : X ⟶ X)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (weilHomologyComparisonOfHom ℓ n (f ≫ g)).hom.app K ≫
        ((boundedConstructible _).ι ⋙ DerivedCategory.homologyFunctor _ n).map
          ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f g).hom.app K) =
      (upperStarCompOver ℓ f g).hom.app
          (((boundedConstructible _).ι ⋙ DerivedCategory.homologyFunctor _ n).obj K) ≫
        (f.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map
          ((weilHomologyComparisonOfHom ℓ n g).hom.app K) ≫
        (weilHomologyComparisonOfHom ℓ n f).hom.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj K) := by
  have h1 : ((boundedConstructible _).ι ⋙ DerivedCategory.homologyFunctor _ n).map
      ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f g).hom.app K) =
        (DerivedCategory.homologyFunctor _ n).map
          ((leftDerivedUpperStarCompOver ℓ f g).hom.app K.obj) :=
    congrArg (DerivedCategory.homologyFunctor _ n).map
      (boundedConstructibleUpperStarComp_hom_app_hom' ℓ f g K)
  rw [weilHomologyComparisonOfHom_hom_app, weilHomologyComparisonOfHom_hom_app,
    weilHomologyComparisonOfHom_hom_app, h1]
  exact leftDerivedUpperStarHomologyIso_compOver_hom_app ℓ n f g K.obj

end Homology

section PowSucc

variable {e : X ≅ X} (n : ℕ)

/-- The homology sheaves of the iterate `(K, φ^{(n+1)})` are the iterates of the homology
sheaves: `(Hʲ(K), φ_{Hʲ(K)}^{(n+1)}) ≅ Hʲ(K, φ^{(n+1)})` as Weil sheaves for `e^{n+1}`. -/
noncomputable def WeilBoundedConstructible.homologyPowSuccIso
    (K : WeilBoundedConstructible ℓ e.hom) (j : ℤ) :
    (WeilSheaf.powFunctor ℓ e (n + 1)).obj
        ((WeilBoundedConstructible.homologyFunctor ℓ e j).obj K) ≅
      (WeilBoundedConstructible.homologyFunctor ℓ (e.pow (n + 1)) j).obj (K.powSucc ℓ n) :=
  eqToIso (WeilSheaf.pow_succ ℓ _ n) ≪≫ e.mapOfNatIsoPowSuccIso
    (fun g ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g)
    (fun f g ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f g)
    (fun g ↦ (g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
    (fun f g ↦ upperStarComp (Profinite.padicAlgClRingObj ℓ) f.left g.left)
    ((boundedConstructible _).ι ⋙ DerivedCategory.homologyFunctor _ j)
    (fun g ↦ weilHomologyComparisonOfHom ℓ j g) (weilHomologyComparisonOfHom_comp ℓ j) K n

end PowSucc

end AlgebraicGeometry.ProEtale.CondensedRing
