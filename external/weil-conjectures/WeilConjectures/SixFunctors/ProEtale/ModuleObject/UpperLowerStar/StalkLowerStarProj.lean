/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange

/-!

# Restriction of stalks of a pushforward

Let `f : X ⟶ Y` be a morphism of schemes and `x̄ : P ⟶ X`, `ȳ : P ⟶ Y` with `x̄ ≫ f = ȳ`. The
restriction `ȳ^* f_* M ⟶ x̄^* M` of module objects over `Λ`
(`ProEtale.CondensedRing.stalkLowerStarProj`) is the composite
`ȳ^* f_* M = (x̄ ≫ f)^* f_* M ≅ x̄^* f^* f_* M ⟶ x̄^* M` of the composition isomorphism and
the counit of `f^* ⊣ f_*`. For `P` the spectrum of a separably closed field, these are the
projections of the stalk of `f_* M` at `ȳ` to the stalks of `M` at the points over `ȳ`
(`ProEtale.CondensedRing.FibrePoints`, finite for finite `f`:
`ProEtale.CondensedRing.finite_fibrePoints`).

The restriction is compatible with

- precomposition of the points (`ProEtale.CondensedRing.stalkLowerStarProj_comp_left`),
- base change along a commutative square `a ≫ f = f ≫ b`
  (`ProEtale.CondensedRing.stalkLowerStarProj_lowerStarBaseChange`), and along a general
  commutative square `g' ≫ f = f' ≫ g`
  (`ProEtale.CondensedRing.stalkLowerStarProj_lowerStarBaseChange'`),
- transport of the points along equalities and morphisms of module objects.

For points `x̄, x̄'` over `ȳ` with `x̄ ≫ a = σ ≫ x̄'` and `ȳ ≫ b = σ ≫ ȳ`, these combine into the
compatibility of the restriction with the Frobenius comparisons
(`ProEtale.CondensedRing.pointComparison_lowerStarBaseChange_stalkLowerStarProj`): the Frobenius
of the stalk of `f_* M` at `ȳ`, followed by the restriction to `x̄`, is the restriction to `x̄'`
followed by the Frobenius transport from `x̄'` to `x̄`.

The coherences are first proved for abstract functors and isomorphisms
(`CategoryTheory.Iso.app_counit_eq_of_coherence`,
`CategoryTheory.Adjunction.unit_counit_baseChange_eq_of_coherence`) and then instantiated; this
keeps the kernel from unfolding the pullback functors.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Fibre

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y P : Scheme.{u}} (f : X ⟶ Y) (y : P ⟶ Y)

/-- The `P`-valued points `x̄ : P ⟶ X` over a `P`-valued point `ȳ : P ⟶ Y`. -/
abbrev FibrePoints : Type u :=
  {x : P ⟶ X // x ≫ f = y}

/-- A finite morphism has finitely many geometric points over a geometric point. -/
theorem finite_fibrePoints [IsFinite f] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (eP : P ≅ Spec (.of Ω)) : Finite (FibrePoints f y) :=
  have : Finite (f.GeometricFiber (eP.inv ≫ y)) := inferInstance
  Finite.of_injective
    (fun x : FibrePoints f y ↦ (⟨eP.inv ≫ x.1, by rw [Category.assoc, x.2]⟩ :
      f.GeometricFiber (eP.inv ≫ y)))
    fun a b h ↦ Subtype.ext (by
      simpa using congrArg (fun z : f.GeometricFiber (eP.inv ≫ y) ↦ eP.hom ≫ z.1) h)

variable {f y}

/-- The projection `ȳ^* f_* F ⟶ x̄^* F` of the stalk of the pushforward at `ȳ` to the stalk at a
point `x̄` over `ȳ`: the composite `ȳ^* f_* F = (x̄ ≫ f)^* f_* F ≅ x̄^* f^* f_* F ⟶ x̄^* F` of the
composition isomorphism and the counit of `f^* ⊣ f_*`. -/
noncomputable def stalkLowerStarProj {x : P ⟶ X} (hx : x ≫ f = y)
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (y)^*⟦Λ⟧.obj ((f)_*⟦Λ⟧.obj F) ⟶ (x)^*⟦Λ⟧.obj F :=
  eqToHom (by rw [← hx]) ≫ (upperStarComp Λ x f).hom.app _ ≫
    (x)^*⟦Λ⟧.map ((upperStarLowerStarAdjunction Λ f).counit.app F)


end Fibre

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y P : Scheme.{u}} {f : X ⟶ Y}

/-- Abstract form of `stalkLowerStarProj_comp_left`, with variables in place of the pullbacks. -/
lemma _root_.CategoryTheory.Iso.app_counit_eq_of_coherence {A B Q Q' : Type*}
    [Category A] [Category B] [Category Q] [Category Q'] {Rf : A ⥤ B} {Lf : B ⥤ A}
    (ε : Rf ⋙ Lf ⟶ 𝟭 A)
    {Xs : A ⥤ Q} {Ys XFs : B ⥤ Q} {S : Q ⥤ Q'} {SYs SXFs : B ⥤ Q'} {SXs : A ⥤ Q'}
    (cy : Ys ≅ XFs) (cxf : XFs ≅ Lf ⋙ Xs) (c1 : SYs ≅ SXFs) (c2 : SXFs ≅ Lf ⋙ SXs)
    (csy : SYs ≅ Ys ⋙ S) (csx : SXs ≅ Xs ⋙ S)
    (h1 : ∀ N, csy.hom.app N ≫ S.map (cy.hom.app N) ≫ S.map (cxf.hom.app N) =
      c1.hom.app N ≫ c2.hom.app N ≫ csx.hom.app (Lf.obj N)) (M : A) :
    c1.hom.app (Rf.obj M) ≫ c2.hom.app (Rf.obj M) ≫ SXs.map (ε.app M) =
      csy.hom.app (Rf.obj M) ≫ S.map (cy.hom.app (Rf.obj M) ≫ cxf.hom.app (Rf.obj M) ≫
        Xs.map (ε.app M)) ≫ csx.inv.app M := by
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (h1 (Rf.obj M)), ← Functor.comp_map Xs S, ← csx.hom.naturality_assoc]
  simp


lemma stalkLowerStarProj_eq {x : P ⟶ X} {y : P ⟶ Y} (hx : x ≫ f = y)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    stalkLowerStarProj Λ hx M = (upperStarCongr Λ hx.symm).hom.app ((f)_*⟦Λ⟧.obj M) ≫
      (upperStarComp Λ x f).hom.app ((f)_*⟦Λ⟧.obj M) ≫
      (x)^*⟦Λ⟧.map ((upperStarLowerStarAdjunction Λ f).counit.app M) := by
  rw [upperStarCongr_hom_app_eq_eqToHom]
  rfl

lemma upperStarCongr_proof_irrel {S T : Scheme.{u}} {a b : S ⟶ T} (e₁ e₂ : a = b) :
    upperStarCongr Λ e₁ = upperStarCongr Λ e₂ :=
  rfl

@[reassoc]
lemma upperStarComp_hom_app_map_upperStarCongr_hom_app' {S T U : Scheme.{u}} (t : S ⟶ T)
    {a b : T ⟶ U} (e : a = b) (e' : t ≫ a = t ≫ b)
    (N : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) :
    (upperStarComp Λ t a).hom.app N ≫ (t)^*⟦Λ⟧.map ((upperStarCongr Λ e).hom.app N) =
      (upperStarCongr Λ e').hom.app N ≫ (upperStarComp Λ t b).hom.app N := by
  subst e
  simp [upperStarCongr_self]

lemma restriction_comp_left_coherence {P' : Scheme.{u}} (σ : P' ⟶ P) {x : P ⟶ X} {y : P ⟶ Y}
    (hx : x ≫ f = y) (hx' : (σ ≫ x) ≫ f = σ ≫ y)
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (upperStarComp Λ σ y).hom.app N ≫ (σ)^*⟦Λ⟧.map ((upperStarCongr Λ hx.symm).hom.app N) ≫
        (σ)^*⟦Λ⟧.map ((upperStarComp Λ x f).hom.app N) =
      (upperStarCongr Λ hx'.symm).hom.app N ≫ (upperStarComp Λ (σ ≫ x) f).hom.app N ≫
        (upperStarComp Λ σ x).hom.app ((f)^*⟦Λ⟧.obj N) := by
  rewrite [upperStarComp_hom_app_map_upperStarCongr_hom_app'_assoc Λ σ hx.symm
      (hx'.symm.trans (Category.assoc σ x f)),
    CondensedRing.upperStarComp_hom_app_comp_upperStarComp_hom_app,
    upperStarCongr_hom_app_trans_assoc]
  conv_rhs => rw [upperStarCongr_proof_irrel Λ _ (hx'.symm.trans (Category.assoc σ x f))]

lemma stalkLowerStarProj_comp_left {P' : Scheme.{u}} (σ : P' ⟶ P) {x : P ⟶ X} {y : P ⟶ Y}
    (hx : x ≫ f = y) (hx' : (σ ≫ x) ≫ f = σ ≫ y)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    stalkLowerStarProj Λ hx' M =
      (upperStarComp Λ σ y).hom.app ((f)_*⟦Λ⟧.obj M) ≫
        (σ)^*⟦Λ⟧.map (stalkLowerStarProj Λ hx M) ≫ (upperStarComp Λ σ x).inv.app M := by
  rw [stalkLowerStarProj_eq, stalkLowerStarProj_eq]
  refine CategoryTheory.Iso.app_counit_eq_of_coherence _ _ _ _ _ _ _
    (restriction_comp_left_coherence Λ σ hx hx') M

/-- Abstract form of `stalkLowerStarProj_lowerStarBaseChange`. -/
lemma _root_.CategoryTheory.Adjunction.unit_counit_baseChange_eq_of_coherence {A B Q : Type*}
    [Category A] [Category B] [Category Q] {Rf : A ⥤ B} {Lf : B ⥤ A} (adj : Lf ⊣ Rf)
    {As : A ⥤ A} {Bs : B ⥤ B}
    {Xs : A ⥤ Q} {Ys YBs XFs XAFs : B ⥤ Q} {XAs : A ⥤ Q}
    (θ : Bs ⋙ Lf ≅ Lf ⋙ As) (cyb : YBs ≅ Bs ⋙ Ys) (cy : Ys ≅ XFs) (cxf : XFs ≅ Lf ⋙ Xs)
    (cxa : XAs ≅ As ⋙ Xs) (c1 : YBs ≅ XAFs) (c2 : XAFs ≅ Lf ⋙ XAs)
    (h : ∀ N, cyb.hom.app N ≫ cy.hom.app (Bs.obj N) ≫ cxf.hom.app (Bs.obj N) ≫
      Xs.map (θ.hom.app N) = c1.hom.app N ≫ c2.hom.app N ≫ cxa.hom.app (Lf.obj N)) (M : A) :
    cyb.hom.app (Rf.obj M) ≫ Ys.map (adj.unit.app (Bs.obj (Rf.obj M)) ≫
        Rf.map (θ.hom.app (Rf.obj M)) ≫ Rf.map (As.map (adj.counit.app M))) ≫
        (cy.hom.app (Rf.obj (As.obj M)) ≫ cxf.hom.app (Rf.obj (As.obj M)) ≫
          Xs.map (adj.counit.app (As.obj M))) =
      (c1.hom.app (Rf.obj M) ≫ c2.hom.app (Rf.obj M) ≫ XAs.map (adj.counit.app M)) ≫
        cxa.hom.app M := by
  have hκ := (cy ≪≫ cxf).hom.naturality (adj.unit.app (Bs.obj (Rf.obj M)) ≫
    Rf.map (θ.hom.app (Rf.obj M)) ≫ Rf.map (As.map (adj.counit.app M)))
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.comp_map, Category.assoc] at hκ
  rw [reassoc_of% hκ]
  have hε : Lf.map (adj.unit.app (Bs.obj (Rf.obj M)) ≫ Rf.map (θ.hom.app (Rf.obj M)) ≫
      Rf.map (As.map (adj.counit.app M))) ≫ adj.counit.app (As.obj M) =
      θ.hom.app (Rf.obj M) ≫ As.map (adj.counit.app M) := by
    simp only [Functor.map_comp, Category.assoc]
    erw [adj.counit_naturality, adj.counit_naturality_assoc, adj.left_triangle_components_assoc]
  rw [← Xs.map_comp, hε, Xs.map_comp, reassoc_of% (h (Rf.obj M))]
  simp only [Category.assoc]
  erw [cxa.hom.naturality (adj.counit.app M)]
  rfl

@[reassoc]
lemma upperStarComp_hom_app_upperStarCongr_hom_app' {S T U : Scheme.{u}} {a b : S ⟶ T}
    (e : a = b) (t : T ⟶ U) (e' : a ≫ t = b ≫ t)
    (N : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) :
    (upperStarComp Λ a t).hom.app N ≫ (upperStarCongr Λ e).hom.app ((t)^*⟦Λ⟧.obj N) =
      (upperStarCongr Λ e').hom.app N ≫ (upperStarComp Λ b t).hom.app N := by
  subst e
  simp [upperStarCongr_self]

@[reassoc]
lemma _root_.CategoryTheory.Functor.map_hom_app_comp_map_inv_app {C D E : Type*} [Category C]
    [Category D] [Category E] (F : D ⥤ E) {G H : C ⥤ D} (e : G ≅ H) (X : C) :
    F.map (e.hom.app X) ≫ F.map (e.inv.app X) = 𝟙 _ := by
  rw [← F.map_comp, Iso.hom_inv_id_app, F.map_id]

lemma restriction_baseChange_coherence {a : X ⟶ X} {b : Y ⟶ Y} (sq : CommSq a f f b)
    {x : P ⟶ X} {y : P ⟶ Y} (hx : x ≫ f = y) (hxy : (x ≫ a) ≫ f = y ≫ b)
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (upperStarComp Λ y b).hom.app N ≫ (upperStarCongr Λ hx.symm).hom.app ((b)^*⟦Λ⟧.obj N) ≫
        (upperStarComp Λ x f).hom.app ((b)^*⟦Λ⟧.obj N) ≫
        (x)^*⟦Λ⟧.map ((upperStarSquareComparison Λ sq).hom.app N) =
      (upperStarCongr Λ hxy.symm).hom.app N ≫ (upperStarComp Λ (x ≫ a) f).hom.app N ≫
        (upperStarComp Λ x a).hom.app ((f)^*⟦Λ⟧.obj N) := by
  rewrite [upperStarComp_hom_app_upperStarCongr_hom_app'_assoc Λ hx.symm b (by rw [hx]),
    CondensedRing.upperStarComp_hom_app_comp_upperStarComp_hom_app_assoc,
    upperStarSquareComparison_hom_app, Functor.map_comp, Functor.map_comp,
    CategoryTheory.Functor.map_hom_app_comp_map_inv_app_assoc,
    upperStarComp_hom_app_map_upperStarCongr_hom_app'_assoc Λ x sq.w.symm (by rw [sq.w]),
    upperStarComp_hom_app_comp_map_upperStarComp_hom_app, upperStarCongr_hom_app_trans_assoc,
    upperStarCongr_hom_app_trans_assoc, upperStarCongr_hom_app_trans_assoc]
  conv_lhs => rw [upperStarCongr_proof_irrel Λ _ hxy.symm]

@[reassoc]
lemma stalkLowerStarProj_lowerStarBaseChange {a : X ⟶ X} {b : Y ⟶ Y} (sq : CommSq a f f b)
    {x : P ⟶ X} {y : P ⟶ Y} (hx : x ≫ f = y) (hxy : (x ≫ a) ≫ f = y ≫ b)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (upperStarComp Λ y b).hom.app ((f)_*⟦Λ⟧.obj M) ≫
        (y)^*⟦Λ⟧.map ((lowerStarBaseChange Λ sq).app M) ≫
        stalkLowerStarProj Λ hx ((a)^*⟦Λ⟧.obj M) =
      stalkLowerStarProj Λ hxy M ≫ (upperStarComp Λ x a).hom.app M := by
  rw [lowerStarBaseChange_eq, Adjunction.exchangeRight_app, stalkLowerStarProj_eq,
    stalkLowerStarProj_eq]
  exact CategoryTheory.Adjunction.unit_counit_baseChange_eq_of_coherence
    (upperStarLowerStarAdjunction Λ f)
    (upperStarSquareComparison Λ sq) _ _ _ _ _ _ (restriction_baseChange_coherence Λ sq hx hxy) M

/-- Abstract form of `stalkLowerStarProj_lowerStarBaseChange'`, for a general commutative square. -/
lemma _root_.CategoryTheory.Adjunction.unit_counit_baseChange_eq_of_coherence' {A A' B B' Q : Type*}
    [Category A] [Category A'] [Category B] [Category B'] [Category Q] {Rf : A ⥤ B} {Lf : B ⥤ A}
    (adj : Lf ⊣ Rf) {Rf' : A' ⥤ B'} {Lf' : B' ⥤ A'} (adj' : Lf' ⊣ Rf') {As : A ⥤ A'}
    {Bs : B ⥤ B'} {Xs : A' ⥤ Q} {Ys XFs : B' ⥤ Q} {YBs XAFs : B ⥤ Q} {XAs : A ⥤ Q}
    (θ : Bs ⋙ Lf' ≅ Lf ⋙ As) (cyb : YBs ≅ Bs ⋙ Ys) (cy : Ys ≅ XFs) (cxf : XFs ≅ Lf' ⋙ Xs)
    (cxa : XAs ≅ As ⋙ Xs) (c1 : YBs ≅ XAFs) (c2 : XAFs ≅ Lf ⋙ XAs)
    (h : ∀ N, cyb.hom.app N ≫ cy.hom.app (Bs.obj N) ≫ cxf.hom.app (Bs.obj N) ≫
      Xs.map (θ.hom.app N) = c1.hom.app N ≫ c2.hom.app N ≫ cxa.hom.app (Lf.obj N)) (M : A) :
    cyb.hom.app (Rf.obj M) ≫ Ys.map (adj'.unit.app (Bs.obj (Rf.obj M)) ≫
        Rf'.map (θ.hom.app (Rf.obj M)) ≫ Rf'.map (As.map (adj.counit.app M))) ≫
        (cy.hom.app (Rf'.obj (As.obj M)) ≫ cxf.hom.app (Rf'.obj (As.obj M)) ≫
          Xs.map (adj'.counit.app (As.obj M))) =
      (c1.hom.app (Rf.obj M) ≫ c2.hom.app (Rf.obj M) ≫ XAs.map (adj.counit.app M)) ≫
        cxa.hom.app M := by
  have hκ := (cy ≪≫ cxf).hom.naturality (adj'.unit.app (Bs.obj (Rf.obj M)) ≫
    Rf'.map (θ.hom.app (Rf.obj M)) ≫ Rf'.map (As.map (adj.counit.app M)))
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.comp_map, Category.assoc] at hκ
  rw [reassoc_of% hκ]
  have hε : Lf'.map (adj'.unit.app (Bs.obj (Rf.obj M)) ≫ Rf'.map (θ.hom.app (Rf.obj M)) ≫
      Rf'.map (As.map (adj.counit.app M))) ≫ adj'.counit.app (As.obj M) =
      θ.hom.app (Rf.obj M) ≫ As.map (adj.counit.app M) := by
    simp only [Functor.map_comp, Category.assoc]
    erw [adj'.counit_naturality, adj'.counit_naturality_assoc, adj'.left_triangle_components_assoc]
  rw [← Xs.map_comp, hε, Xs.map_comp, reassoc_of% (h (Rf.obj M))]
  simp only [Category.assoc]
  erw [cxa.hom.naturality (adj.counit.app M)]
  rfl

variable {X' Y' : Scheme.{u}} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

lemma restriction_baseChange_coherence' (sq : CommSq g' f' f g) {x : P ⟶ X'} {y : P ⟶ Y'}
    (hx : x ≫ f' = y) (hxy : (x ≫ g') ≫ f = y ≫ g)
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (upperStarComp Λ y g).hom.app N ≫ (upperStarCongr Λ hx.symm).hom.app ((g)^*⟦Λ⟧.obj N) ≫
        (upperStarComp Λ x f').hom.app ((g)^*⟦Λ⟧.obj N) ≫
        (x)^*⟦Λ⟧.map ((upperStarSquareComparison Λ sq).hom.app N) =
      (upperStarCongr Λ hxy.symm).hom.app N ≫ (upperStarComp Λ (x ≫ g') f).hom.app N ≫
        (upperStarComp Λ x g').hom.app ((f)^*⟦Λ⟧.obj N) := by
  rewrite [upperStarComp_hom_app_upperStarCongr_hom_app'_assoc Λ hx.symm g (by rw [hx]),
    CondensedRing.upperStarComp_hom_app_comp_upperStarComp_hom_app_assoc,
    upperStarSquareComparison_hom_app, Functor.map_comp, Functor.map_comp,
    CategoryTheory.Functor.map_hom_app_comp_map_inv_app_assoc,
    upperStarComp_hom_app_map_upperStarCongr_hom_app'_assoc Λ x sq.w.symm (by rw [sq.w]),
    upperStarComp_hom_app_comp_map_upperStarComp_hom_app, upperStarCongr_hom_app_trans_assoc,
    upperStarCongr_hom_app_trans_assoc, upperStarCongr_hom_app_trans_assoc]
  conv_lhs => rw [upperStarCongr_proof_irrel Λ _ hxy.symm]

/-- **Restriction of stalks and base change**, for a general commutative square
`g' ≫ f = f' ≫ g`: for points `x̄ : P ⟶ X'` and `ȳ : P ⟶ Y'` with `x̄ ≫ f' = ȳ`, the restriction
of the stalk of `f'_* g'^* M` at `ȳ` to `x̄`, precomposed with the base-change morphism, is the
restriction of the stalk of `f_* M` at `ȳ ≫ g` to `x̄ ≫ g'`. -/
@[reassoc]
lemma stalkLowerStarProj_lowerStarBaseChange' (sq : CommSq g' f' f g) {x : P ⟶ X'} {y : P ⟶ Y'}
    (hx : x ≫ f' = y) (hxy : (x ≫ g') ≫ f = y ≫ g)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (upperStarComp Λ y g).hom.app ((f)_*⟦Λ⟧.obj M) ≫
        (y)^*⟦Λ⟧.map ((lowerStarBaseChange Λ sq).app M) ≫
        stalkLowerStarProj Λ hx ((g')^*⟦Λ⟧.obj M) =
      stalkLowerStarProj Λ hxy M ≫ (upperStarComp Λ x g').hom.app M := by
  rw [lowerStarBaseChange_eq, Adjunction.exchangeRight_app, stalkLowerStarProj_eq,
    stalkLowerStarProj_eq]
  exact CategoryTheory.Adjunction.unit_counit_baseChange_eq_of_coherence'
    (upperStarLowerStarAdjunction Λ f) (upperStarLowerStarAdjunction Λ f')
    (upperStarSquareComparison Λ sq) _ _ _ _ _ _ (restriction_baseChange_coherence' Λ sq hx hxy) M

/-- The restriction of stalks is natural in the module object. -/
@[reassoc]
lemma stalkLowerStarProj_naturality {x : P ⟶ X} {y : P ⟶ Y} (hx : x ≫ f = y)
    {M M' : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (g : M ⟶ M') :
    (y)^*⟦Λ⟧.map ((f)_*⟦Λ⟧.map g) ≫ stalkLowerStarProj Λ hx M' =
      stalkLowerStarProj Λ hx M ≫ (x)^*⟦Λ⟧.map g := by
  subst hx
  have h₁ := (upperStarComp Λ x f).hom.naturality ((f)_*⟦Λ⟧.map g)
  have h₂ := (upperStarLowerStarAdjunction Λ f).counit.naturality g
  simp only [Functor.comp_map, Functor.id_map] at h₁ h₂
  simp only [stalkLowerStarProj, eqToHom_refl, Category.id_comp]
  rw [reassoc_of% h₁, ← Functor.map_comp, h₂, Functor.map_comp, Category.assoc]

/-- The restriction of stalks along a transported point. -/
@[reassoc]
lemma upperStarCongr_hom_app_stalkLowerStarProj {x : P ⟶ X} {y₁ y₂ : P ⟶ Y} (e : y₁ = y₂)
    (h₁ : x ≫ f = y₁) (h₂ : x ≫ f = y₂)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (upperStarCongr Λ e).hom.app ((f)_*⟦Λ⟧.obj M) ≫ stalkLowerStarProj Λ h₂ M =
      stalkLowerStarProj Λ h₁ M := by
  rewrite [stalkLowerStarProj_eq, stalkLowerStarProj_eq, upperStarCongr_hom_app_trans_assoc]
  conv_lhs => rw [upperStarCongr_proof_irrel Λ _ h₁.symm]

/-- The restriction of stalks to a transported point. -/
lemma stalkLowerStarProj_upperStarCongr_hom_app {x₁ x₂ : P ⟶ X} {y : P ⟶ Y} (e : x₁ = x₂)
    (h₁ : x₁ ≫ f = y) (h₂ : x₂ ≫ f = y)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    stalkLowerStarProj Λ h₁ M ≫ (upperStarCongr Λ e).hom.app M = stalkLowerStarProj Λ h₂ M := by
  subst e
  rw [upperStarCongr_self, Iso.refl_hom, NatTrans.id_app, Category.comp_id]

/-- The Frobenius comparison `x̄'^* ≅ a^* ⋙ x̄^*` between points `x̄, x̄' : P ⟶ Z` with
`x̄ ≫ a = σ ≫ x̄'`, for an isomorphism `τ : σ^* ≅ 𝟭`. -/
noncomputable def pointComparison {σ : P ⟶ P} (τ : (σ)^*⟦Λ⟧ ≅ 𝟭 _) {Z : Scheme.{u}} (a : Z ⟶ Z)
    {x x' : P ⟶ Z} (h : x ≫ a = σ ≫ x') : (x')^*⟦Λ⟧ ⋙ 𝟭 _ ≅ (a)^*⟦Λ⟧ ⋙ (x)^*⟦Λ⟧ :=
  Functor.isoWhiskerLeft _ τ.symm ≪≫ (upperStarComp Λ σ x').symm ≪≫ upperStarCongr Λ h.symm ≪≫
    upperStarComp Λ x a

lemma pointComparison_hom {σ : P ⟶ P} (τ : (σ)^*⟦Λ⟧ ≅ 𝟭 _) {Z : Scheme.{u}} (a : Z ⟶ Z)
    {x x' : P ⟶ Z} (h : x ≫ a = σ ≫ x') :
    (pointComparison Λ τ a h).hom = Functor.whiskerLeft _ τ.inv ≫ (upperStarComp Λ σ x').inv ≫
      (upperStarCongr Λ h.symm).hom ≫ (upperStarComp Λ x a).hom :=
  rfl

lemma pointComparison_hom_app {σ : P ⟶ P} (τ : (σ)^*⟦Λ⟧ ≅ 𝟭 _) {Z : Scheme.{u}} (a : Z ⟶ Z)
    {x x' : P ⟶ Z} (h : x ≫ a = σ ≫ x')
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    (pointComparison Λ τ a h).hom.app M = τ.inv.app ((x')^*⟦Λ⟧.obj M) ≫
      (upperStarComp Λ σ x').inv.app M ≫ (upperStarCongr Λ h.symm).hom.app M ≫
      (upperStarComp Λ x a).hom.app M := by
  rw [pointComparison_hom, NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app,
    Functor.whiskerLeft_app]

/-- **The Frobenius of the stalk of a pushforward permutes the factors** (generic form). -/
lemma pointComparison_lowerStarBaseChange_stalkLowerStarProj {a : X ⟶ X} {b : Y ⟶ Y}
    (sq : CommSq a f f b) {σ : P ⟶ P} (τ : (σ)^*⟦Λ⟧ ≅ 𝟭 _) {y : P ⟶ Y} (hy : y ≫ b = σ ≫ y)
    {x x' : P ⟶ X} (hx : x ≫ f = y) (hx' : x' ≫ f = y) (h : x ≫ a = σ ≫ x')
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (φ : (a)^*⟦Λ⟧.obj M ⟶ M) :
    ((pointComparison Λ τ b hy).hom.app ((f)_*⟦Λ⟧.obj M) ≫
        (y)^*⟦Λ⟧.map ((lowerStarBaseChange Λ sq).app M ≫ (f)_*⟦Λ⟧.map φ)) ≫
        stalkLowerStarProj Λ hx M =
      stalkLowerStarProj Λ hx' M ≫ ((pointComparison Λ τ a h).hom.app M ≫ (x)^*⟦Λ⟧.map φ) := by
  have hxy : (x ≫ a) ≫ f = y ≫ b := by rw [Category.assoc, sq.w, ← Category.assoc, hx]
  have hxy' : (x ≫ a) ≫ f = σ ≫ y := hxy.trans hy
  have h₁ : (σ ≫ x') ≫ f = σ ≫ y := by rw [Category.assoc, hx']
  rewrite [pointComparison_hom_app, pointComparison_hom_app, Functor.map_comp]
  simp only [Category.assoc (obj := Mod (Sheaf (Scheme.ProEt.topology P) Ab.{u + 1})
    (condensedRingObj Λ P))]
  rewrite [stalkLowerStarProj_naturality, stalkLowerStarProj_lowerStarBaseChange_assoc Λ sq hx hxy,
    upperStarCongr_hom_app_stalkLowerStarProj_assoc Λ hy.symm hxy' hxy,
    ← stalkLowerStarProj_upperStarCongr_hom_app Λ h.symm h₁ hxy',
    stalkLowerStarProj_comp_left Λ σ hx' h₁]
  simp only [Category.assoc (obj := Mod (Sheaf (Scheme.ProEt.topology P) Ab.{u + 1})
    (condensedRingObj Λ P)), Iso.inv_hom_id_app_assoc]
  rw [← τ.inv.naturality_assoc, Functor.id_map]

end AlgebraicGeometry.ProEtale.CondensedRing
