/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ObjectProperty.FullSubcategoryEqToHom
public import WeilConjectures.TraceFormula.BaseChange.Coherence
public import WeilConjectures.TraceFormula.BaseChange.Iterate
public import WeilConjectures.TraceFormula.BaseChange.WeilObject

/-!

# Local traces of the base change of a Weil object

Let `k` be a finite field, `Ω ⊇ k` a separably closed field, `X` a separated scheme of finite type
over `Spec k`, `e` an automorphism of `X` over `Spec k` and `σ` an automorphism of `Spec Ω` inverse
to the `#k ^ N`-power Frobenius of `Spec Ω`. For a geometric point `x̄ : Spec Ω ⟶ X` over `Spec k`
with `x̄ ≫ e = σ ≫ x̄`, the rational point `x̄' = (x̄, 𝟙)` of `X̄ = X ×_k Ω` is fixed by the model
Frobenius `Φ = (e ≫ F_X^N) ×_k Ω` (`geometricBaseChangePoint_comp_modelFrobenius_eq_iff`). This
file compares, for a Weil object `L` of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` for `e`:

* the Frobenius of the stalk at `x̄` of the Weil sheaf `Hʲ(L)`, for the twisted Frobenius `σ`
  (`WeilSheaf.stalkFunctor`), and
* the `j`-th homology of the local Frobenius at `x̄'` of the base change `Lπ^* L`, a Weil object
  for the model Frobenius `Φ` (`weilStalk`, `weilGeometricBaseChange`).

They are conjugate, so they have the same trace. The formal part is
`homology_modelFrobenius_comp_eq_aux`; this file identifies the two Frobenii with its abstract
composites, the Galois one for an abstract trivialization `τ : σ^* ≅ 𝟭` compatible with the
trivialization of the Frobenius pullback (`IsGaloisCompatibleFrobeniusIsoAt`).

## Main results

- `ProEtale.CondensedRing.traceOrZero_stalkFunctor_homologyFunctor_eq`:
  `Tr(Fr_x̄ | Hʲ(L)_x̄) = Tr(Hʲ(F_x̄') | Hʲ((Lπ^* L)_x̄'))`.

-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Finite k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {Ω : Type u} [Field Ω] [Algebra k Ω] [Fact (ringChar Ω).Prime]
  [Fact (ringChar Ω ≠ ℓ)]
  (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (N : ℕ) (g : X ⟶ X)

/-! ### The model Frobenius -/

section Model

omit [Finite k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] [Fact ℓ.Prime] in
/-- On the ambient derived categories, the composition isomorphism of the derived pullbacks on
bounded constructible complexes, with its source written through `f.left ≫ g.left`. -/
lemma boundedConstructibleUpperStarComp_hom_app_hom_eq {S : Type u} [Field S]
    [Fact (ringChar S).Prime] [Fact (ringChar S ≠ ℓ)] [Fact ℓ.Prime]
    {A B C : Over (Spec (.of S))} [LocallyOfFiniteType A.hom] [QuasiCompact A.hom]
    [IsSeparated A.hom] [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
    (f : A ⟶ B) (g : B ⟶ C) (K : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f g).hom.app K).hom =
      eqToHom (show ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (f ≫ g)).obj K).obj =
        L((f.left ≫ g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj K.obj from rfl) ≫
        (leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ℓ) f.left g.left).hom.app K.obj := by
  rw [eqToHom_refl, Category.id_comp]
  exact boundedConstructibleUpperStarComp_hom_app_hom _ ℓ f g K

variable {X N g} in
omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Fact (ringChar Ω).Prime]
  [Fact (ringChar Ω ≠ ℓ)] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [Finite k] [Fact ℓ.Prime] in
/-- A rational point fixed by the model Frobenius, on the underlying schemes. -/
lemma left_comp_modelFrobenius_left [Finite k]
    {x' : RationalPoint ((geometricBaseChange k Ω).obj X)}
    (hx' : x' ≫ baseChangeModelFrobenius Ω X N g = x') :
    x'.left ≫ (baseChangeModelFrobenius Ω X N g).left = x'.left :=
  (Over.comp_left _ _ _ x' (baseChangeModelFrobenius Ω X N g)).symm.trans (congrArg Over.Hom.left
      hx')

variable {X N g} in
/-- The local Frobenius at a rational point `x̄'` fixed by the model Frobenius `Φ` of the base
change of `(a, ψ)`, as an explicit composite on `Dᵇc(Spec Ω)⟦ℚ̲̄_ℓ⟧`:
```
Lx̄'^* Lπ^* a = L(x̄' ≫ Φ)^* Lπ^* a ≅ Lx̄'^* LΦ^* Lπ^* a
  --b--> Lx̄'^* Lπ^* Lg^* a --ψ--> Lx̄'^* Lπ^* a
```
-/
noncomputable def modelStalkFrobenius (x' : RationalPoint ((geometricBaseChange k Ω).obj X))
    (hx' : x' ≫ baseChangeModelFrobenius Ω X N g = x') (a :
        Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj a ⟶ a) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x').obj
        ((geometricBaseChangeUpperStar Ω ℓ X).obj a) ⟶
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x').obj
        ((geometricBaseChangeUpperStar Ω ℓ X).obj a) :=
  eqToHom (congrArg (fun f ↦ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ)
      ℓ f).obj ((geometricBaseChangeUpperStar Ω ℓ X).obj a)) hx'.symm) ≫
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ x'
      (baseChangeModelFrobenius Ω X N g)).hom.app ((geometricBaseChangeUpperStar Ω ℓ X).obj a) ≫
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x').map
      ((weilGeometricBaseChangeComparison Ω ℓ X N g).hom.app a ≫
        (geometricBaseChangeUpperStar Ω ℓ X).map ψ)

variable {X N g} in
/-- On the ambient derived category, the explicit local Frobenius of the base change is the
composite `modelFrobeniusAux` of the derived pullbacks. -/
lemma modelStalkFrobenius_hom [IsSepClosed Ω]
    (x' : RationalPoint ((geometricBaseChange k Ω).obj X))
    (hx' : x' ≫ baseChangeModelFrobenius Ω X N g = x') (a :
        Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj a ⟶ a) :
    (modelStalkFrobenius ℓ x' hx' a ψ).hom =
      modelFrobeniusAux (D := fun S ↦ DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S)
          Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj ℓ) S)))
        (fun a ↦ L((a)^*⟦Profinite.padicAlgClRingObj ℓ⟧))
        (fun a b ↦ leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ℓ) a b) x'.left
        (baseChangeModelFrobenius Ω X N g).left (geometricBaseChangeProj X) g.left
        (frobeniusIterate (overFrobenius X) N).left (left_comp_modelFrobenius_left hx')
        (modelFrobenius_left_comp_proj' X N g) (leftDerivedUpperStarFrobeniusIso ℓ X N)
        a.obj ψ.hom := by
  rw [modelStalkFrobenius]
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  simp only [ObjectProperty.FullSubcategory.eqToHom_hom']
  simp only [boundedConstructibleUpperStarComp_hom_app_hom_eq]
  simp only [boundedConstructibleUpperStar_map_hom]
  simp only [ObjectProperty.FullSubcategory.comp_hom, weilGeometricBaseChangeComparison_hom_app_hom,
    geometricBaseChangeUpperStar_map_hom, leftDerivedUpperStarModelFrobeniusComparison_hom_app]
  simp only [modelFrobeniusAux, leftDerivedUpperStarModelFrobeniusIso_hom_app, Functor.map_comp,
    Category.assoc]
  simp only [eqToHom_trans_assoc]
  rfl

variable {X N g} in
/-- The local Frobenius at `x̄'` of the base change of a Weil object `(L, φ)` is the explicit
composite `modelStalkFrobenius` for `(L, φ)`. -/
lemma weilStalk_weilGeometricBaseChange_frobenius_hom [IsSepClosed Ω]
    (x' : RationalPoint ((geometricBaseChange k Ω).obj X))
    (hx' : x' ≫ baseChangeModelFrobenius Ω X N g = x') (L : WeilBoundedConstructible ℓ g) :
    ((weilStalk ℓ (baseChangeModelFrobenius Ω X N g) x' hx').obj
        ((weilGeometricBaseChange Ω ℓ X N g).obj L)).frobenius.hom =
      modelStalkFrobenius ℓ x' hx' L.carrier L.str.hom := by
  rw [WeilBoundedConstructible.weilStalk_obj_frobenius_hom_eq]
  simp only [weilGeometricBaseChange_obj_str, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  rfl

end Model

/-! ### The Galois Frobenius -/

section Galois

variable {X} [IsSepClosed Ω] (e : X ≅ X) (σ : Spec (.of Ω) ≅ Spec (.of Ω))
  (x : Spec (.of Ω) ⟶ X.left) (hx : x ≫ e.hom.left = σ.hom ≫ x)

omit [Finite k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Algebra k Ω]
  [Fact (ringChar Ω).Prime] [Fact (ringChar Ω ≠ ℓ)] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] in
/-- The Frobenius comparison of the stalk, unfolded. -/
lemma weilStalkComparison_eq_trans : weilStalkComparison ℓ e σ.hom x hx =
    Functor.isoWhiskerLeft _
      (upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ) σ.hom).symm ≪≫
      (upperStarComp (Profinite.padicAlgClRingObj ℓ) σ.hom x).symm ≪≫
      upperStarEqToIso (Profinite.padicAlgClRingObj ℓ) hx.symm ≪≫
      upperStarComp (Profinite.padicAlgClRingObj ℓ) x e.hom.left :=
  rfl

omit [Finite k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Algebra k Ω]
  [Fact (ringChar Ω).Prime] [Fact (ringChar Ω ≠ ℓ)] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] in
/-- The Frobenius of the stalk of a Weil sheaf at a geometric point fixed up to `σ`, as an
explicit composite:
`x̄^* F --τ⁻¹--> σ^* x̄^* F ≅ (σ ≫ x̄)^* F = (x̄ ≫ e)^* F ≅ x̄^* e^* F --x̄^* φ_F--> x̄^* F`. -/
lemma stalkFunctor_obj_str_hom (W : WeilSheaf ℓ e) :
    ((WeilSheaf.stalkFunctor ℓ e σ.hom x hx).obj W).str.hom =
      (upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ) σ.hom).inv.app
          ((x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj W.carrier) ≫
        (upperStarComp (Profinite.padicAlgClRingObj ℓ) σ.hom x).inv.app W.carrier ≫
        eqToHom (congrArg (fun t : Spec (.of Ω) ⟶ X.left ↦
          (t)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj W.carrier) hx.symm) ≫
        (upperStarComp (Profinite.padicAlgClRingObj ℓ) x e.hom.left).hom.app W.carrier ≫
        (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map W.str.hom := by
  have h1 : ((WeilSheaf.stalkFunctor ℓ e σ.hom x hx).obj W).str.hom =
      (weilStalkComparison ℓ e σ.hom x hx).hom.app W.carrier ≫
        (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map W.str.hom := by
    rw [WeilSheaf.stalkFunctor_obj_str]
    rfl
  have h2 := isoWhiskerLeft_symm_trans_hom_app_aux ((x)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
    (upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ) σ.hom)
    (upperStarComp (Profinite.padicAlgClRingObj ℓ) σ.hom x)
    (upperStarEqToIso (Profinite.padicAlgClRingObj ℓ) hx.symm)
    (upperStarComp (Profinite.padicAlgClRingObj ℓ) x e.hom.left) W.carrier
  have h3 := (congrArg (fun i ↦ i.hom.app W.carrier)
    (weilStalkComparison_eq_trans ℓ e σ x hx)).trans h2
  refine h1.trans ((congrArg (· ≫ (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map W.str.hom) h3).trans
    ((congrArg (fun z ↦ ((upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ) σ.hom).inv.app
        ((x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj W.carrier) ≫
        (upperStarComp (Profinite.padicAlgClRingObj ℓ) σ.hom x).inv.app W.carrier ≫ z ≫
        (upperStarComp (Profinite.padicAlgClRingObj ℓ) x e.hom.left).hom.app W.carrier) ≫
        (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map W.str.hom)
      (upperStarEqToIso_hom_app _ hx.symm W.carrier)).trans ?_))
  simp only [Category.assoc]

end Galois

/-! ### The comparison of the local traces -/

section Comparison

variable {X} [IsSepClosed Ω] (e : X ≅ X) (σ : Spec (.of Ω) ≅ Spec (.of Ω))
  (hσ : σ.inv = Spec.map (powCardPowRingHom k Ω N)) (x : Spec (.of Ω) ⟶ X.left)
  (hxk : x ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
  (hx : x ≫ e.hom.left = σ.hom ≫ x)

omit [Finite k] [Algebra k Ω] [Fact (ringChar Ω).Prime] [Fact (ringChar Ω ≠ ℓ)]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] in
/-- The components of the Frobenius comparison of the stalk. -/
lemma weilStalkComparison_hom_app' (M) :
    (weilStalkComparison ℓ e σ.hom x hx).hom.app M =
      (upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ) σ.hom).inv.app
          ((x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M) ≫
        (upperStarComp (Profinite.padicAlgClRingObj ℓ) σ.hom x).inv.app M ≫
        eqToHom (congrArg (fun s : Spec (.of Ω) ⟶ X.left ↦
          (s)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M) hx.symm) ≫
        (upperStarComp (Profinite.padicAlgClRingObj ℓ) x e.hom.left).hom.app M :=
  (congrArg (fun i ↦ i.hom.app M) (weilStalkComparison_eq_trans ℓ e σ x hx)).trans
    ((isoWhiskerLeft_symm_trans_hom_app_aux ((x)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
      (upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ) σ.hom)
      (upperStarComp (Profinite.padicAlgClRingObj ℓ) σ.hom x)
      (upperStarEqToIso (Profinite.padicAlgClRingObj ℓ) hx.symm)
      (upperStarComp (Profinite.padicAlgClRingObj ℓ) x e.hom.left) M).trans
      (congrArg (fun z ↦
        (upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ) σ.hom).inv.app
          ((x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M) ≫
        (upperStarComp (Profinite.padicAlgClRingObj ℓ) σ.hom x).inv.app M ≫ z ≫
        (upperStarComp (Profinite.padicAlgClRingObj ℓ) x e.hom.left).hom.app M)
        (upperStarEqToIso_hom_app _ hx.symm M)))

/-- `traceOrZero_stalkFunctor_homologyFunctor_eq` for an abstract trivialization `τ` of the
Galois pullback compatible with the trivialization of the Frobenius pullback. -/
lemma traceOrZero_galoisFrobenius_eq_aux (L : WeilBoundedConstructible ℓ e.hom) (j : ℤ)
    (τ : (σ.hom)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ≅ 𝟭 _)
    (hτ : IsGaloisCompatibleFrobeniusIsoAt ℓ X N (upperStarFrobeniusIso ℓ X N) σ hσ x τ) :
    traceOrZero (τ.inv.app ((x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj
          ((WeilBoundedConstructible.homologyFunctor ℓ e j).obj L).carrier) ≫
        (upperStarComp (Profinite.padicAlgClRingObj ℓ) σ.hom x).inv.app
          ((WeilBoundedConstructible.homologyFunctor ℓ e j).obj L).carrier ≫
        eqToHom (congrArg (fun t : Spec (.of Ω) ⟶ X.left ↦
          (t)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj
            ((WeilBoundedConstructible.homologyFunctor ℓ e j).obj L).carrier) hx.symm) ≫
        (upperStarComp (Profinite.padicAlgClRingObj ℓ) x e.hom.left).hom.app
          ((WeilBoundedConstructible.homologyFunctor ℓ e j).obj L).carrier ≫
        (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map
          ((WeilBoundedConstructible.homologyFunctor ℓ e j).obj L).str.hom) =
      traceOrZero ((DerivedCategory.homologyFunctor _ j).map
        ((weilStalk ℓ (baseChangeModelFrobenius Ω X N e.hom) (geometricBaseChangePoint x hxk)
          ((geometricBaseChangePoint_comp_modelFrobenius_eq_iff x hxk N e.hom σ hσ).2 hx)).obj
          ((weilGeometricBaseChange Ω ℓ X N e.hom).obj L)).frobenius.hom.hom) := by
  have hW : ((WeilBoundedConstructible.homologyFunctor ℓ e j).obj L).str.hom =
      (leftDerivedUpperStarHomologyIso (Profinite.padicAlgClRingObj ℓ) e.hom.left j).hom.app
          L.carrier.obj ≫
        (DerivedCategory.homologyFunctor _ j).map L.str.hom.hom := by
    have h1 := congrArg Iso.hom (IsoAlgebra.mapOfNatIso_obj_str (weilHomologyComparison ℓ e j) L)
    have h2 := weilHomologyComparisonOfHom_hom_app ℓ j e.hom L.carrier
    exact h1.trans (congrArg (· ≫ _) h2)
  have hc := WeilBoundedConstructible.homologyFunctor_obj_carrier ℓ e j L
  have hT := eqToHom_comp_galois_comp_eqToHom_heq_aux
    (E := fun S ↦ Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) S))
    (fun a ↦ (a)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
    (fun a b ↦ upperStarComp (Profinite.padicAlgClRingObj ℓ) a b) e.hom.left σ.hom x hx
    τ hc _ _ (heq_of_eq hW)
  have hx' := (geometricBaseChangePoint_comp_modelFrobenius_eq_iff x hxk N e.hom σ hσ).2 hx
  have hconj := galoisFrobeniusAux_eq_conj (P := Spec (.of Ω))
    (D := fun S ↦ DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) S)))
    (E := fun S ↦ Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) S))
    (fun a ↦ L((a)^*⟦Profinite.padicAlgClRingObj ℓ⟧))
    (fun a b ↦ leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ℓ) a b)
    (fun a b c M ↦ leftDerivedUpperStarComp_assoc_app _ a b c M)
    (fun a ↦ (a)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
    (fun a b ↦ upperStarComp (Profinite.padicAlgClRingObj ℓ) a b)
    (fun a b c M ↦ upperStarComp_assoc_app_eqToHom _ a b c M)
    (fun S ↦ DerivedCategory.homologyFunctor _ j)
    (fun a ↦ leftDerivedUpperStarHomologyIso (Profinite.padicAlgClRingObj ℓ) a j)
    (fun a b M ↦ leftDerivedUpperStarHomologyIso_comp_hom_app _ a b j M)
    (geometricBaseChangePoint x hxk).left (baseChangeModelFrobenius Ω X N e.hom).left
    (geometricBaseChangeProj X) e.hom.left (frobeniusIterate (overFrobenius X) N).left σ.hom x
    (geometricBaseChangePoint_left_comp_proj x hxk) (left_comp_modelFrobenius_left hx')
    (modelFrobenius_left_comp_proj' X N e.hom) hx
    (comp_comp_frobeniusIterate_overFrobenius_left hσ x)
    (leftDerivedUpperStarFrobeniusIso ℓ X N) (upperStarFrobeniusIso ℓ X N)
    (fun M ↦ leftDerivedUpperStarHomologyIso_hom_app_idIso _ _ (upperStarFrobeniusIso ℓ X N) j M)
    τ hτ L.carrier.obj L.str.hom.hom
  have hF := (congrArg InducedCategory.Hom.hom
    (weilStalk_weilGeometricBaseChange_frobenius_hom ℓ (geometricBaseChangePoint x hxk)
      ((geometricBaseChangePoint_comp_modelFrobenius_eq_iff x hxk N e.hom σ hσ).2 hx) L)).trans
    (modelStalkFrobenius_hom ℓ (geometricBaseChangePoint x hxk) hx' L.carrier L.str.hom)
  refine (traceOrZero_conj (eqToIso (congrArg ((x)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
    hc)) _).symm.trans ?_
  refine (congrArg traceOrZero (hT.trans hconj)).trans ((traceOrZero_conj _ _).trans ?_)
  have hG := congrArg traceOrZero (congrArg (DerivedCategory.homologyFunctor _ j).map hF)
  exact hG.symm

/-- **The comparison of the local traces of a Weil object and of its base change.** Let
`(L, φ)` be a Weil object of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` for an automorphism `e`, `σ` an automorphism of
`Spec Ω` inverse to the `#k ^ N`-power Frobenius and `x̄ : Spec Ω ⟶ X` a geometric point with
`x̄ ≫ e = σ ≫ x̄`, so that `x̄' = (x̄, 𝟙)` is fixed by the model Frobenius
`Φ = (e ≫ F_X^N) ×_k Ω`. Then the trace of the Frobenius on the stalk at `x̄` of the Weil sheaf
`Hʲ(L)`, for the Frobenius `σ` twisted by `e`, is the trace of the `j`-th homology of the local
Frobenius at `x̄'` of the base change `Lπ^* L` for the model Frobenius:
```
Tr(Fr_{x̄} | Hʲ(L)_x̄) = Tr(Hʲ(F_{x̄'}) | Hʲ((Lπ^* L)_x̄')).
```
-/
theorem traceOrZero_stalkFunctor_homologyFunctor_eq (L : WeilBoundedConstructible ℓ e.hom)
    (j : ℤ) :
    traceOrZero (((WeilSheaf.stalkFunctor ℓ e σ.hom x hx).obj
        ((WeilBoundedConstructible.homologyFunctor ℓ e j).obj L)).str.hom) =
      traceOrZero ((DerivedCategory.homologyFunctor _ j).map
        ((weilStalk ℓ (baseChangeModelFrobenius Ω X N e.hom) (geometricBaseChangePoint x hxk)
          ((geometricBaseChangePoint_comp_modelFrobenius_eq_iff x hxk N e.hom σ hσ).2 hx)).obj
          ((weilGeometricBaseChange Ω ℓ X N e.hom).obj L)).frobenius.hom.hom) := by
  exact (congrArg traceOrZero (stalkFunctor_obj_str_hom ℓ e σ x hx _)).trans
    (traceOrZero_galoisFrobenius_eq_aux (ℓ := ℓ) (hσ := hσ) (hxk := hxk) (hx := hx) (L := L)
      (j := j) (τ := upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ) σ.hom)
      (hτ := isGaloisCompatibleFrobeniusIso_upperStarFrobeniusIso ℓ X N Ω σ hσ x))

/-- `traceOrZero_stalkFunctor_homologyFunctor_eq` for the stalk functor along a morphism
`σ'` equal to `σ.hom` (for instance with a different presentation of `Spec Ω`). -/
theorem traceOrZero_stalkFunctor_homologyFunctor_eq_of_hom_eq
    (σ' : Spec (.of Ω) ⟶ Spec (.of Ω)) (hσ' : σ.hom = σ') (hx' : x ≫ e.hom.left = σ' ≫ x)
    (L : WeilBoundedConstructible ℓ e.hom) (j : ℤ) :
    traceOrZero (((WeilSheaf.stalkFunctor ℓ e σ' x hx').obj
        ((WeilBoundedConstructible.homologyFunctor ℓ e j).obj L)).str.hom) =
      traceOrZero ((DerivedCategory.homologyFunctor _ j).map
        ((weilStalk ℓ (baseChangeModelFrobenius Ω X N e.hom) (geometricBaseChangePoint x hxk)
          ((geometricBaseChangePoint_comp_modelFrobenius_eq_iff x hxk N e.hom σ hσ).2 hx)).obj
          ((weilGeometricBaseChange Ω ℓ X N e.hom).obj L)).frobenius.hom.hom) := by
  subst hσ'
  exact traceOrZero_stalkFunctor_homologyFunctor_eq ℓ N e σ hσ x hxk hx L j

end Comparison

end AlgebraicGeometry.ProEtale.CondensedRing
