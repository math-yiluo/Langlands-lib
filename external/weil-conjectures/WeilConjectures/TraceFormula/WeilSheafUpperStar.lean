/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.PullbackFamily
public import WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar
public import WeilConjectures.WeilObject.BoundedConstructible.Homology
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.HomologyFunctorCoherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.HomologyCoherence

/-!

# The pullback of Weil sheaves

Let `g : W ⟶ X` be a morphism over a finite field `k` with automorphisms `e_W`, `e_X` such that
`e_W ≫ g = g ≫ e_X`. The pullback `g^*` of module objects sends a Weil sheaf `(F, φ_F)` for `e_X`
to the Weil sheaf `g^* F` for `e_W` (`ProEtale.CondensedRing.weilSheafUpperStar`). This file
proves the two inputs of the dévissage of the local trace along a pullback
(`ProEtale.CondensedRing.weilStalkTraceAlternatingSum_weilUpperStar`):

- `ProEtale.CondensedRing.nonempty_homologyFunctor_weilUpperStar_iso`: for a Weil object `K` of
  `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`, `Hʲ(Lg^* K) ≅ g^* Hʲ(K)` as Weil sheaves;
- `ProEtale.CondensedRing.weilSheafStalkTrace_weilSheafUpperStar`: the trace of the Frobenius on
  the stalk of `g^* F` at a point `w̄` of `W` is its trace on the stalk of `F` at `w̄ ≫ g`.

Both are instances of the coherence of the composition isomorphisms of pullbacks
(`WeilConjectures.TraceFormula.PullbackFamily`).

-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### The pullbacks of module objects as a family of pullbacks -/

/-- The pullbacks of module objects over `ℚ̲̄_ℓ` satisfy the associativity law of a family of
pullbacks, along morphisms of schemes. -/
lemma pullbackAssoc_upperStar (ℓ : ℕ) [Fact ℓ.Prime] :
    PullbackAssoc (upperStar (Profinite.padicAlgClRingObj ℓ))
      (fun {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) ↦
        upperStarComp (Profinite.padicAlgClRingObj ℓ) f g) :=
  fun f g h ↦ upperStarComp_assoc _ f g h

section HomologyFunctor

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The commutation `H^n ⋙ f^* ≅ Lf^* ⋙ H^n` of the exact pullbacks of module objects with
homology is compatible with the composition isomorphisms, at an object. -/
lemma leftDerivedFunctorHomologyFunctorIso_upperStarComp {X Y Z : Scheme.{u}} (a : X ⟶ Y)
    (b : Y ⟶ Z) (n : ℤ)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) :
    (upperStarComp Λ a b).hom.app ((DerivedCategory.homologyFunctor _ n).obj K) ≫
        (a)^*⟦Λ⟧.map (((b)^*⟦Λ⟧.leftDerivedFunctorHomologyFunctorIso n).hom.app K) ≫
          ((a)^*⟦Λ⟧.leftDerivedFunctorHomologyFunctorIso n).hom.app (L((b)^*⟦Λ⟧).obj K) =
      ((a ≫ b)^*⟦Λ⟧.leftDerivedFunctorHomologyFunctorIso n).hom.app K ≫
        (DerivedCategory.homologyFunctor _ n).map
          ((leftDerivedUpperStarComp Λ a b).hom.app K) :=
  (leftDerivedUpperStarHomologyIso_comp_hom_app Λ a b n K).symm

/-- The commutation `H^n ⋙ f^* ≅ Lf^* ⋙ H^n` of the exact pullbacks of module objects with
homology is pseudonatural, for the composition isomorphisms `upperStarComp` and
`leftDerivedUpperStarComp`. -/
lemma pullbackPseudonatural_leftDerivedFunctorHomologyFunctorIso_upperStar (n : ℤ) :
    PullbackPseudonatural (C := Scheme.{u})
      (D := fun X ↦ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      (E := fun X ↦ DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
      (P := fun f ↦ (f)^*⟦Λ⟧) (fun f g ↦ upperStarComp Λ f g) (L := fun f ↦ L((f)^*⟦Λ⟧))
      (fun f g ↦ leftDerivedUpperStarComp Λ f g)
      (H := fun _ ↦ DerivedCategory.homologyFunctor _ n)
      (fun f ↦ (f)^*⟦Λ⟧.leftDerivedFunctorHomologyFunctorIso n) :=
  PullbackPseudonatural.of_hom_app fun {_ _ _} a b K ↦
    leftDerivedFunctorHomologyFunctorIso_upperStarComp Λ a b n K

end HomologyFunctor

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Finite k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X W : Over (Spec (.of k))} (eX : X ≅ X) (eW : W ≅ W)

/-! ### The pullbacks of bounded constructible complexes as a family of pullbacks -/

variable (k) in
/-- The schemes over `k` which are locally of finite type, quasi-compact and separated: those on
which the bounded constructible complexes `Dᵇc(-)⟦ℚ̲̄_ℓ⟧` and their pullbacks are defined. -/
def isFiniteTypeSeparated : ObjectProperty (Over (Spec (.of k))) :=
  fun X ↦ LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom ∧ IsSeparated X.hom

section BoundedConstructibleFamily

omit [Finite k]

/-- The derived pullback `Lf^* : Dᵇc(W)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(V)⟦ℚ̲̄_ℓ⟧` along a morphism of
`isFiniteTypeSeparated k`. -/
noncomputable def boundedConstructibleUpperStarFamily
    {V W : (isFiniteTypeSeparated k).FullSubcategory}
    (f : V ⟶ W) :
    Dᵇc(W.obj.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc(V.obj.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  haveI := V.property.1; haveI := V.property.2.1; haveI := V.property.2.2
  haveI := W.property.1; haveI := W.property.2.1; haveI := W.property.2.2
  boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f.hom

/-- The compatibility of `boundedConstructibleUpperStarFamily` with the inclusions. -/
noncomputable def boundedConstructibleUpperStarFamilyCompatibility
    {V W : (isFiniteTypeSeparated k).FullSubcategory} (f : V ⟶ W) :
    boundedConstructibleUpperStarFamily ℓ f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ L((f.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  haveI := V.property.1; haveI := V.property.2.1; haveI := V.property.2.2
  haveI := W.property.1; haveI := W.property.2.1; haveI := W.property.2.2
  boundedConstructibleUpperStarCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ f.hom

/-- The composition isomorphisms of `boundedConstructibleUpperStarFamily`, lifted from
`leftDerivedUpperStarComp`; they are `boundedConstructibleUpperStarComp`. -/
noncomputable def boundedConstructibleUpperStarFamilyComp
    {X Y Z : (isFiniteTypeSeparated k).FullSubcategory} (f : X ⟶ Y) (g : Y ⟶ Z) :
    boundedConstructibleUpperStarFamily ℓ (f ≫ g) ≅
      boundedConstructibleUpperStarFamily ℓ g ⋙ boundedConstructibleUpperStarFamily ℓ f :=
  liftedPullbackComp (C := Scheme.{u})
    (E := fun X ↦ DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)))
    (L := fun f ↦ L((f)^*⟦Profinite.padicAlgClRingObj ℓ⟧))
    (E' := fun V ↦ Dᵇc(V.obj.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (fun f g ↦ leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ℓ) f g)
    (fun _ ↦ (boundedConstructible _).ι) (fun _ ↦ ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarFamily ℓ) (boundedConstructibleUpperStarFamilyCompatibility ℓ)
    f g

/-- The commutation `Hⁿ ⋙ f^* ≅ Lf^* ⋙ Hⁿ` of the derived pullback on `Dᵇc(-)⟦ℚ̲̄_ℓ⟧` with the
homology sheaves; for an automorphism `e`, this is `weilHomologyComparison`. -/
noncomputable def boundedConstructibleHomologyComparison (n : ℤ)
    {V W : (isFiniteTypeSeparated k).FullSubcategory} (f : V ⟶ W) :
    ((boundedConstructible _).ι ⋙ DerivedCategory.homologyFunctor _ n) ⋙
        (f.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ≅
      boundedConstructibleUpperStarFamily ℓ f ⋙
        ((boundedConstructible _).ι ⋙ DerivedCategory.homologyFunctor _ n) :=
  liftedComparison (C := Scheme.{u})
    (E := fun X ↦ DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)))
    (L := fun f ↦ L((f)^*⟦Profinite.padicAlgClRingObj ℓ⟧))
    (E' := fun V ↦ Dᵇc(V.obj.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (Q := isFiniteTypeSeparated k)
    (fun f ↦ (f)^*⟦Profinite.padicAlgClRingObj ℓ⟧.leftDerivedFunctorHomologyFunctorIso n)
    (fun _ ↦ (boundedConstructible _).ι) (boundedConstructibleUpperStarFamily ℓ)
    (boundedConstructibleUpperStarFamilyCompatibility ℓ) f

/-- The commutation of the derived pullback on `Dᵇc(-)⟦ℚ̲̄_ℓ⟧` with the homology sheaves is
pseudonatural: the restriction of
`pullbackPseudonatural_leftDerivedFunctorHomologyFunctorIso_upperStar` along the inclusions. -/
lemma pullbackPseudonatural_boundedConstructibleHomologyComparison (n : ℤ) :
    PullbackPseudonatural (C := (isFiniteTypeSeparated k).FullSubcategory)
      (D := fun V ↦ Mod (Sheaf (Scheme.ProEt.topology V.obj.left) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V.obj.left))
      (E := fun V ↦ Dᵇc(V.obj.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
      (P := fun {V W : (isFiniteTypeSeparated k).FullSubcategory} (f : V ⟶ W) ↦
        (f.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
      (fun {X Y Z : (isFiniteTypeSeparated k).FullSubcategory} (f : X ⟶ Y) (g : Y ⟶ Z) ↦
        upperStarComp (Profinite.padicAlgClRingObj ℓ) f.hom.left g.hom.left)
      (L := boundedConstructibleUpperStarFamily ℓ) (boundedConstructibleUpperStarFamilyComp ℓ)
      (H := fun _ ↦ (boundedConstructible _).ι ⋙ DerivedCategory.homologyFunctor _ n)
      (boundedConstructibleHomologyComparison ℓ n) :=
  PullbackPseudonatural.lifted (C := Scheme.{u})
    (E := fun X ↦ DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)))
    (L := fun f ↦ L((f)^*⟦Profinite.padicAlgClRingObj ℓ⟧))
    (E' := fun V ↦ Dᵇc(V.obj.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (Q := isFiniteTypeSeparated k)
    (fun _ ↦ (boundedConstructible _).ι) (fun _ ↦ ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarFamily ℓ) (boundedConstructibleUpperStarFamilyCompatibility ℓ)
    (pullbackPseudonatural_leftDerivedFunctorHomologyFunctorIso_upperStar _ n)

end BoundedConstructibleFamily

/-! ### The pullback of Weil sheaves -/

section WeilSheafPullback

variable {g : W ⟶ X} (hg : eW.hom ≫ g = g ≫ eX.hom)

/-- The Frobenius comparison `g^* ⋙ e_W^* ≅ e_X^* ⋙ g^*` of the pullback of module objects along
`g` with `e_W ≫ g = g ≫ e_X`: the composite of the composition isomorphisms of the pullbacks and
the transport along `e_W ≫ g = g ≫ e_X`. -/
noncomputable def weilSheafUpperStarComparison :
    (g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ⋙ (eW.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ≅
      (eX.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ⋙
        (g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  (upperStarComp _ eW.hom.left g.left).symm ≪≫
    eqToIso (congrArg (upperStar _) (Over.left_comp_left_eq_of_comp_eq hg)) ≪≫
    upperStarComp _ g.left eX.hom.left

/-- The pullback `g^*` of Weil sheaves along `g : W ⟶ X` with `e_W ≫ g = g ≫ e_X`: a Weil sheaf
`(F, φ_F)` for `e_X` is sent to `g^* F` with the structure isomorphism
`e_W^* g^* F ≅ g^* e_X^* F ≅ g^* F` given by `weilSheafUpperStarComparison` and `g^* φ_F`. -/
noncomputable def weilSheafUpperStar : WeilSheaf ℓ eX ⥤ WeilSheaf ℓ eW :=
  IsoAlgebra.mapOfNatIso (weilSheafUpperStarComparison ℓ eX eW hg)

omit [Finite k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- The pullback of Weil sheaves is the pullback of algebras for the family of pullbacks of
module objects. -/
lemma weilSheafUpperStar_eq :
    weilSheafUpperStar ℓ eX eW hg =
      Endofunctor.IsoAlgebra.overPullback (P := upperStar (Profinite.padicAlgClRingObj ℓ))
        (fun {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) ↦
          upperStarComp (Profinite.padicAlgClRingObj ℓ) f g) eX eW hg :=
  rfl

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- The stalk functor of Weil sheaves for `e^{n+1}`, after the iterated structure isomorphisms
`Iso.powSuccStr`, is the Frobenius stalk functor of algebras for the family of pullbacks of
module objects. -/
lemma overPowSuccFunctor_comp_stalkFunctor (n : ℕ) (x : Spec (.of (AlgebraicClosure k)) ⟶ W.left)
    (hx : x ≫ (eW.pow (n + 1)).hom.left = ((geometricFrobeniusField k).pow (n + 1)).hom ≫ x) :
    Endofunctor.IsoAlgebra.overPowSuccFunctor (P := upperStar (Profinite.padicAlgClRingObj ℓ))
        (fun {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) ↦
          upperStarComp (Profinite.padicAlgClRingObj ℓ) f g) eW n ⋙
      WeilSheaf.stalkFunctor ℓ (eW.pow (n + 1)) ((geometricFrobeniusField k).pow (n + 1)).hom x hx =
      Endofunctor.IsoAlgebra.frobeniusStalkFunctor (P := upperStar (Profinite.padicAlgClRingObj ℓ))
        (fun {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) ↦
          upperStarComp (Profinite.padicAlgClRingObj ℓ) f g)
        (upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ)
          ((geometricFrobeniusField k).pow (n + 1)).hom) eW n x hx := by
  rw [WeilSheaf.stalkFunctor, weilStalkComparison, upperStarEqToIso_eq_eqToIso]
  rfl

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- The stalk functor of Weil sheaves with the `(n + 1)`-st Frobenius operator is the Frobenius
stalk functor of algebras for the family of pullbacks of module objects. -/
lemma WeilSheaf.powStalkFunctor_eq (n : ℕ) (x : Spec (.of (AlgebraicClosure k)) ⟶ W.left)
    (hx : x ≫ (eW.pow (n + 1)).hom.left = ((geometricFrobeniusField k).pow (n + 1)).hom ≫ x) :
    WeilSheaf.powStalkFunctor ℓ (n + 1) x hx =
      Endofunctor.IsoAlgebra.frobeniusStalkFunctor (P := upperStar (Profinite.padicAlgClRingObj ℓ))
        (fun {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) ↦
          upperStarComp (Profinite.padicAlgClRingObj ℓ) f g)
        (upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ)
          ((geometricFrobeniusField k).pow (n + 1)).hom) eW n x hx := by
  have h : WeilSheaf.powFunctor ℓ eW (n + 1) =
      Endofunctor.IsoAlgebra.overPowFunctor (P := upperStar (Profinite.padicAlgClRingObj ℓ))
        (fun {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) ↦
          upperStarComp (Profinite.padicAlgClRingObj ℓ) f g)
        (fun Y ↦ upperStarId (Profinite.padicAlgClRingObj ℓ) Y) eW (n + 1) :=
    rfl
  rw [WeilSheaf.powStalkFunctor, h, Endofunctor.IsoAlgebra.overPowFunctor_succ
    (P := upperStar (Profinite.padicAlgClRingObj ℓ))
    (c := fun {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) ↦
      upperStarComp (Profinite.padicAlgClRingObj ℓ) f g)
    (fun Y ↦ upperStarId (Profinite.padicAlgClRingObj ℓ) Y)
    (fun t ↦ upperStarComp_id_trans_isoWhiskerLeft_upperStarId ℓ t)]
  exact overPowSuccFunctor_comp_stalkFunctor ℓ eW n x hx

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- The trace of the Frobenius on the stalk only depends on the stalk with its Frobenius operator
up to isomorphism, for possibly different Weil sheaves and points. -/
lemma weilSheafStalkTrace_eq_of_iso (n : ℕ) {x : Spec (.of (AlgebraicClosure k)) ⟶ W.left}
    {hx : x ≫ (eW.pow (n + 1)).hom.left = ((geometricFrobeniusField k).pow (n + 1)).hom ≫ x}
    {x' : Spec (.of (AlgebraicClosure k)) ⟶ X.left}
    {hx' : x' ≫ (eX.pow (n + 1)).hom.left = ((geometricFrobeniusField k).pow (n + 1)).hom ≫ x'}
    {G : WeilSheaf ℓ eW} {F : WeilSheaf ℓ eX}
    (i : (WeilSheaf.powStalkFunctor ℓ (n + 1) x hx).obj G ≅
      (WeilSheaf.powStalkFunctor ℓ (n + 1) x' hx').obj F) :
    weilSheafStalkTrace ℓ (n + 1) x hx G = weilSheafStalkTrace ℓ (n + 1) x' hx' F :=
  (IsoAlgebra.traceOrZero_str_congr i).symm
omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- **Stalks of a pullback of Weil sheaves**: for `g : W ⟶ X` with `e_W ≫ g = g ≫ e_X`, a Weil
sheaf `F` for `e_X` and a point `w̄` of `W` of degree `n + 1`, the trace of the `(n + 1)`-st
Frobenius on the stalk of `g^* F` at `w̄` is its trace on the stalk of `F` at `w̄ ≫ g`. The
composition isomorphism `(w̄ ≫ g)^* F ≅ w̄^* g^* F` of the pullbacks intertwines the two Frobenius
operators (`CategoryTheory.pullbackFamilyStalkComparison_pullbackFamilyComparison`), once the
iterated structure
isomorphism of `g^* F` is identified with the pullback of that of `F`
(`CategoryTheory.Iso.powSuccStr_pullbackFamilyComparison`). -/
theorem weilSheafStalkTrace_weilSheafUpperStar (F : WeilSheaf ℓ eX) (n : ℕ)
    (w : frobeniusFixedPoints eW (n + 1)) :
    weilSheafStalkTrace ℓ (n + 1) w.1 w.2.2 ((weilSheafUpperStar ℓ eX eW hg).obj F) =
      weilSheafStalkTrace ℓ (n + 1) (frobeniusFixedPointsMap eW eX hg n w).1
        (frobeniusFixedPointsMap eW eX hg n w).2.2 F := by
  have I := Classical.choice
    (Endofunctor.IsoAlgebra.nonempty_obj_obj_iso_of_eq
      (c := fun {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) ↦
        upperStarComp (Profinite.padicAlgClRingObj ℓ) f g)
      (pullbackAssoc_upperStar ℓ) eX eW hg n
      (upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ)
        ((geometricFrobeniusField k).pow (n + 1)).hom) w.1 w.2.2
      (x := (frobeniusFixedPointsMap eW eX hg n w).1) rfl
      (frobeniusFixedPointsMap eW eX hg n w).2.2 (WeilSheaf ℓ eX) (WeilSheaf ℓ eW)
      (IsoAlgebra (𝟭 (GeometricPointMod ℓ (AlgebraicClosure k)))) F
      (weilSheafUpperStar ℓ eX eW hg) (WeilSheaf.powStalkFunctor ℓ (n + 1) w.1 w.2.2)
      (WeilSheaf.powStalkFunctor ℓ (n + 1) (frobeniusFixedPointsMap eW eX hg n w).1
        (frobeniusFixedPointsMap eW eX hg n w).2.2) rfl rfl rfl
      (heq_of_eq (weilSheafUpperStar_eq ℓ eX eW hg))
      (heq_of_eq (WeilSheaf.powStalkFunctor_eq ℓ eW n _ _))
      (heq_of_eq (WeilSheaf.powStalkFunctor_eq ℓ eX n _ _)))
  exact weilSheafStalkTrace_eq_of_iso ℓ eX eW n I

omit [Finite k] in
/-- **The homology sheaves of a pullback of Weil objects**: for `g : W ⟶ X` with
`e_W ≫ g = g ≫ e_X`, the Weil sheaf `Hʲ(Lg^* K)` is isomorphic to the pullback `g^* Hʲ(K)` of the
Weil sheaf `Hʲ(K)`.

The isomorphism is the commutation `θ_g : Hʲ ⋙ g^* ≅ Lg^* ⋙ Hʲ` of the exact functor `g^*` with
homology. It is compatible with the Weil structures because `θ` is pseudonatural
(`pullbackPseudonatural_boundedConstructibleHomologyComparison`), by
`Endofunctor.IsoAlgebra.nonempty_mapOfNatIso_pullback_iso`. -/
theorem nonempty_homologyFunctor_weilUpperStar_iso [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
    [IsSeparated W.hom] (K : WeilBoundedConstructible ℓ eX.hom) (j : ℤ) :
    Nonempty ((WeilBoundedConstructible.homologyFunctor ℓ eW j).obj
        ((weilUpperStar ℓ eW.hom eX.hom g hg).obj K) ≅
      (weilSheafUpperStar ℓ eX eW hg).obj
        ((WeilBoundedConstructible.homologyFunctor ℓ eX j).obj K)) := by
  let Xo : (isFiniteTypeSeparated k).FullSubcategory :=
    ⟨X, inferInstance, inferInstance, inferInstance⟩
  let Wo : (isFiniteTypeSeparated k).FullSubcategory :=
    ⟨W, inferInstance, inferInstance, inferInstance⟩
  let eX' : Xo ⟶ Xo := ObjectProperty.homMk eX.hom
  let eW' : Wo ⟶ Wo := ObjectProperty.homMk eW.hom
  let g' : Wo ⟶ Xo := ObjectProperty.homMk g
  have hg' : eW' ≫ g' = g' ≫ eX' := ObjectProperty.hom_ext _ hg
  have hB : weilUpperStarComparison ℓ eW.hom eX.hom g hg =
      pullbackFamilyComparison (c := boundedConstructibleUpperStarFamilyComp ℓ) g' eW' eX' hg' := by
    ext M
    rw [weilUpperStarComparison_hom_app, pullbackFamilyComparison_hom_app]
    rfl
  -- with `@`, the pseudonaturality is not unfolded to its universally quantified statement
  have h := Endofunctor.IsoAlgebra.nonempty_mapOfNatIso_pullback_iso
    (@pullbackPseudonatural_boundedConstructibleHomologyComparison ℓ _ k _ _ _ j) g' eW' eX' hg'
  exact h _ _ _ _ (WeilBoundedConstructible.homologyFunctor ℓ eX j)
    (weilUpperStar ℓ eW.hom eX.hom g hg) (WeilBoundedConstructible.homologyFunctor ℓ eW j)
    (weilSheafUpperStar ℓ eX eW hg) K rfl rfl rfl rfl HEq.rfl
    (heq_of_eq (congrArg IsoAlgebra.mapOfNatIso hB)) HEq.rfl HEq.rfl

end WeilSheafPullback

end AlgebraicGeometry.ProEtale.CondensedRing
